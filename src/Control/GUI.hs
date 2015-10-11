-- |
--   Module:     Control.GUI
--   Copyright:  (c) 2015 Schell Scivally
--   License:    MIT
--   Maintainer: Schell Scivally <efsubenovex@gmail.com>
--
--   GUI's goal is to abstract over graphical user interfaces, assurring
--   they are renderable, dynamic (they change over their domain) and eventually
--   produce a value.
--
--   A GUI is a monadic 'spline' with an iteration value that can be
--   concatenated. What this means is that a GUI is essentially a user
--   experience that eventually produces a value and those GUIs can be
--   combined to produce a product value.

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}
module Control.GUI (
    -- * Creation
    -- $creation
    gui,
    -- * Transformation
    -- $transformation
    transformGUI,
    -- * Combination
    -- $combination
    combineGUI,
    eitherGUI,
    -- * Putting it all together
    runGUIs,
    -- * Reexports
    module S,
) where

import Control.Varying as S
import Control.Varying.Spline as S
import Control.Arrow (first)
import Control.Monad
import Data.Renderable
import Data.Monoid

--------------------------------------------------------------------------------
-- $creation
-- In order to create a spline you must first have a datatype with a 'Composite'
-- instance. Then you must create a 'varying' value of that datatype
-- describing how it will change over the domain of user input and time.
-- Also needed is an event stream that eventually ends the user's interaction.
-- The idea is that your interface varies over time and user input but
-- eventually produces a result value that can be used in a monadic
-- sequence.
--------------------------------------------------------------------------------
-- | Create a spline describing an interface that eventually produces a value.
-- The type used to represent the user interface must have a 'Composite'
-- instance. This allows GUIs to be layered graphically since separate
-- GUI's iteration values can all be combined after being broken down into
-- transformed primitives.
gui :: (Monad m, Monad n, Monoid (f (t, Element n r t)), Composite a f n r t)
    => Var m i a
    -- ^ The stream of a changing user interface.
    -> Var m i (Event b)
    -- ^ The event stream that concludes a user\'s interaction. When this
    -- stream produces an event the interaction will end and the spline
    -- will conclude.
    -> SplineT m f i (t, Element n r t) (a,b)
gui v ve = SplineT $ t ~> var (uncurry f)
    where t = (,) <$> v <*> ve
          f a e = let ui = composite a
                  in case e of
                         NoEvent -> Step ui NoEvent
                         Event b -> Step ui $ Event (a, b)

--------------------------------------------------------------------------------
-- $transformation
-- Simply put - here we are applying some kind of transformation to your
-- renderable interface. This most likely a standard two or three dimensional
-- affine transformation. Since the transformation also changes over the
-- same domain it\'s possible to tween GUIs.
--------------------------------------------------------------------------------
-- | Transforms a GUI.
transformGUI :: (Monad m, Monoid t, Functor f, Monoid (f (t,d)))
             => Var m i t -> SplineT m f i (t, d) b -> SplineT m f i (t, d) b
transformGUI vt g = SplineT $ Var $ \i -> do
    (Step ui e, v) <- runVar (runSplineT g) i
    (t, vt') <- runVar vt i
    let ui' = fmap (first (mappend t)) ui
    return (Step ui' e, runSplineT $ transformGUI vt' $ SplineT v)
--------------------------------------------------------------------------------
-- $combination
--------------------------------------------------------------------------------
-- | Combines two GUIs. The resulting SplineT will not produce a value until
-- either both component GUIs have produced a value, or until a switching
-- event occurs. At that moment a merging function is used to combine any
-- available produced values in the resulting GUI\'s return type.
-- The component GUIs\' graphical representations (the left Step values) are
-- 'mappend'\d together.
combineGUI :: (Monad m, Monoid (f u))
                => SplineT m f i u a
                -> SplineT m f i u b
                -> Var m i (Event c)
                -> SplineT m f i u (Maybe a, Maybe b, Maybe c)
combineGUI (SplineTConst a) (SplineTConst b) _ =
    SplineTConst (Just a, Just b, Nothing)
combineGUI (SplineTConst a) s vc =
    combineGUI (SplineT $ pure $ Step mempty $ Event a) s vc
combineGUI s (SplineTConst b) vc =
    combineGUI s (SplineT $ pure $ Step mempty $ Event b) vc
combineGUI (SplineT va) (SplineT vb) vc = SplineT $ Var $ \i -> do
    (Step ua ea, va') <- runVar va i
    (Step ub eb, vb') <- runVar vb i
    (ec, vc')         <- runVar vc i
    let g ex v = case ex of
                     Event x -> pure $ Step mempty $ Event x
                     NoEvent -> v
        va'' = g ea va'
        vb'' = g eb vb'
        ma = toMaybe ea
        mb = toMaybe eb
        mc = toMaybe ec
        ev = Event (ma,mb,mc)
        e  = case (ma,mb,mc) of
                 (Just _, Just _,      _) -> ev
                 (     _,      _, Just _) -> ev
                 _                        -> NoEvent
    return (Step (ua <> ub) e, runSplineT $ combineGUI (SplineT va'') (SplineT vb'') vc')

-- | Run two GUIs at the same time and return the result of the SplineT that
-- concludes first. If they conclude at the same time the result is taken from
-- the GUI on the left.
eitherGUI :: (Monad m, Monoid (f u))
          => SplineT m f i u a -> SplineT m f i u a -> SplineT m f i u a
eitherGUI (SplineTConst a) s =
    eitherGUI (SplineT $ pure $ Step mempty $ Event a) s
eitherGUI s (SplineTConst b) =
    eitherGUI s (SplineT $ pure $ Step mempty $ Event b)
eitherGUI (SplineT va) (SplineT vb) = SplineT $ Var $ \i -> do
    (Step ua ea, va') <- runVar va i
    (Step ub eb, vb') <- runVar vb i
    case (ea,eb) of
        (Event _,_) -> return (Step (ua <> ub) ea, va')
        (_,Event _) -> return (Step (ua <> ub) eb, vb')
        (_,_)       -> return (Step (ua <> ub) NoEvent,
                               runSplineT $ eitherGUI (SplineT va') (SplineT vb'))

-- | Run a list of GUIs in parallel. Restart individual GUIs whenever it
-- concludes in a value. Return a list of the most recent result values once the
-- control GUI concludes.
runGUIs :: (Monad m, Monoid (f b))
        => [Maybe c -> SplineT m f a b c] -> SplineT m f a b ()
        -> SplineT m f a b [Maybe c]
runGUIs gs = go gs es $ zipWith ($) gs xs
    where es = replicate n NoEvent
          xs = replicate n Nothing
          n  = length gs
          go fs evs guis egui = SplineT $ Var $ \a -> do
            let step (ecs, fb, vs) (f, ec, g) = do
                    (Step fb' ec', v) <- runVar (runSplineT g) a
                    let ec'' = ec <> ec'
                        fb'' = fb <> fb'
                        v'   = case ec' of
                                   NoEvent -> v
                                   Event c -> runSplineT $ f $ Just c
                    return (ecs ++ [ec''], fb'', vs ++ [SplineT v'])
            (ecs, fb, guis') <- foldM step ([],mempty,[]) (zip3 fs evs guis)
            (Step fb' ec, v) <- runVar (runSplineT egui) a
            let fb'' = fb <> fb'
                ec' = map toMaybe ecs <$ ec
            return (Step fb'' ec',
                    runSplineT $ go fs ecs guis' $ SplineT v)
