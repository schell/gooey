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
    combineGUIUntil,
    eitherGUI,
    -- * Reexports
    module S,
) where

import Control.Varying as S
import Control.Varying.Spline as S
import Control.Arrow (first)
import Data.Renderable
import Data.Monoid

--------------------------------------------------------------------------------
-- $creation
-- In order to create a SplineT you must first have a datatype with a 'Composite'
-- instance. Then you must create a 'varying' value of that datatype
-- describing how it will change over the domain of user input and time.
-- Also needed is an event stream that eventually ends the user's interaction.
-- The idea is that your interface varies over time and user input but
-- eventually produces a result value that can be used in a monadic
-- sequence.
--------------------------------------------------------------------------------
-- | Creates a new SplineT displaying an interface that eventually produces a value.
-- The type used to represent the user interface must have a 'Decomposable'
-- instance, that way the resulting GUI\'s discrete values can be rendered.
gui :: (Monad m, Monad n, Monoid (f (t, Element n r t)), Composite a f n r t)
    => Var m i a
    -- ^ The stream of a changing user interface.
    -> Var m i (Event b)
    -- ^ The event stream that concludes a user\'s interaction. When this
    -- stream produces an event the interaction will end and the merging
    -- function will be used to create the GUI\'s return type.
    -> (a -> b -> c)
    -- ^ The merging function that combines the interface's final value with the
    -- value produced by the event stream.
    -> SplineT m f i (t, Element n r t) c
gui v ve f = SplineT $ Var $ \i -> do
    (a, v')  <- runVar v i
    (e, ve') <- runVar ve i
    let ui = composite a
    return $ case e of
        NoEvent -> (Step ui NoEvent, runSplineT $ gui v' ve' f)
        Event b -> let ex = Event $ f a b
                   in (Step ui ex, pure $ Step mempty ex)

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
-- Combining two GUIs creates a new GUI. The strategy taken to combine the
-- result values of the two GUIs must be provided. With 'combineGUI' the
-- SplineT runs until both component GUIs have concluded. With 'combineGUIUntil'
-- the SplineT runs until either both component GUIs have concluded or
-- until a switching event occurs.
--------------------------------------------------------------------------------
-- | Combines two GUIs. The resulting SplineT will not produce a value until
-- both component GUIs have produced a value. At that moment a merging function
-- is used to combine the two values into the resulting GUI\'s return type.
-- The component GUIs\' graphical representations (the left Step values) are
-- 'mappend'\d together.
combineGUI :: Monad m
           => SplineT m f i u a
           -- ^ The first GUI.
           -> SplineT m f i u b
           -- ^ The second GUI.
           -> (a -> b -> c)
           -- ^ The merging function.
           -> SplineT m f i u c
combineGUI (SplineTConst a) (SplineTConst b) f = SplineTConst $ f a b
combineGUI (SplineTConst a) (SplineT vb) f = SplineT $ fmap (fmap (f a)) vb
combineGUI (SplineT va) (SplineTConst b) f = SplineT $ fmap (fmap (`f` b)) va
combineGUI (SplineT va) (SplineT vb) f = SplineT $ Var $ \i -> do
        (Step a ea, va') <- runVar va i
        (Step b eb, vb') <- runVar vb i
        return (Step (a <> b) (f <$> ea <*> eb),
                runSplineT $ combineGUI (SplineT va') (SplineT vb') f)

-- | Combines two GUIs. The resulting SplineT will not produce a value until
-- either both component GUIs have produced a value, or until a switching
-- event occurs. At that moment a merging function is used to combine any
-- available produced values in the resulting GUI\'s return type.
-- The component GUIs\' graphical representations (the left Step values) are
-- 'mappend'\d together.
combineGUIUntil :: (Monad m, Monoid (f u))
                => SplineT m f i u a
                -> SplineT m f i u b
                -> Var m i (Event c)
                -> (Maybe a -> Maybe b -> Maybe c -> d)
                -> SplineT m f i u d
combineGUIUntil (SplineTConst a) (SplineTConst b) _ f =
    SplineTConst $ f (Just a) (Just b) Nothing
combineGUIUntil (SplineTConst a) s vc f =
    combineGUIUntil (SplineT $ pure $ Step mempty $ Event a) s vc f
combineGUIUntil s (SplineTConst b) vc f =
    combineGUIUntil s (SplineT $ pure $ Step mempty $ Event b) vc f
combineGUIUntil (SplineT va) (SplineT vb) vc f = SplineT $ Var $ \i -> do
    (Step ua ea, va') <- runVar va i
    (Step ub eb, vb') <- runVar vb i
    (ec, vc')       <- runVar vc i
    let g ex v = case ex of
                     Event x -> pure $ Step mempty $ Event x
                     NoEvent -> v
        va'' = g ea va'
        vb'' = g eb vb'
        ma = toMaybe ea
        mb = toMaybe eb
        mc = toMaybe ec
        e  = case (ma,mb,mc) of
                 (Just _, Just _,      _) -> Event $ f ma mb mc
                 (     _,      _, Just _) -> Event $ f ma mb mc
                 _                        -> NoEvent
    return (Step (ua <> ub) e, runSplineT $ combineGUIUntil (SplineT va'') (SplineT vb'') vc' f)

-- | Run two GUIs at the same time and return the result of the SplineT that
-- concludes first. If they're both concluded the result is taken from the
-- GUI on the left.
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
                               runSplineT $ eitherGUI (SplineT va') (SplineT vb') )
