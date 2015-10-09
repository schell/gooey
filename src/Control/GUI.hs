-- |
--   Module:     Control.GUI
--   Copyright:  (c) 2015 Schell Scivally
--   License:    MIT
--   Maintainer: Schell Scivally <efsubenovex@gmail.com>
--
--   Graphical user interfaces that are renderable, change over time and
--   eventually produce a value.
--
--   GUIs are comprised of event streams and renderable datatypes that change
--   over time. A GUI is a monadic layer on top of automaton varying values
--   provided by the 'varying' library.

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
module Control.GUI (
    -- * Definition
    UX(..),
    GUI(..),
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
    eitherGUI
) where

import Control.Varying
import Control.Monad.IO.Class
import Control.Arrow (first)
import Data.Renderable
import Data.Monoid

--------------------------------------------------------------------------------
-- Defining a GUI
--------------------------------------------------------------------------------
-- | A discrete step in a "user experience". This is simply a type that
-- discretely describes an eventual value on the right and a renderable datatype
-- on the left. It is assumed that the left value is a datatype
-- that represents a user inteface and that the user is interacting with it
-- to eventually produce the datatype on the right.
data UX a b = UX a (Event b)

-- | A UX is a functor by applying a function to the contained event's value.
instance Functor (UX a) where
    fmap f (UX a b) = UX a $ fmap f b

-- | A UX is a monoid if its left and right types are monoids.
instance (Monoid a, Monoid b) => Monoid (UX a b) where
    mempty = UX mempty (Event mempty)
    mappend (UX a ea) (UX b eb) = UX (mappend a b) (mappend <$> ea <*> eb)

-- | A UX is an applicative if its left datatype is a monoid. It replies to
-- 'pure' with an empty left value while the right value is the argument
-- wrapped in an event. It means "the argument happens instantly with no
-- user interface".
instance Monoid a => Applicative (UX a) where
    pure a = UX mempty $ Event a
    (UX uia f) <*> (UX uib b) = UX (uia <> uib) (f <*> b)

-- | A UX is renderable if its left value is also renderable. It inherits all
-- Renderable type variables from its left value and simply renders that
-- value.
instance Composite a m r t => Composite (UX a b) m r t where
    composite (UX ui _) = composite ui

-- | A GUI is a UX that varies over some domain. What this means is that a
-- graphical user interface is essentially a user experience that eventually
-- produces a value. 'm' is the underlying monad. 'i' is the type of the user
-- input.  'a' is the renderable type - the interface itself. 'b' is the
-- eventual produced value.
newtype GUI m i a b = GUI { runGUI :: Var m i (UX a b) }

-- | A GUI can be a monoid if its UX\'s left and right types are monoids.
-- The identity is a GUI that has no user interface and immediately
-- produces an event who\'s value is the identity of its UX's right type.
-- The associative operation is to combine the two GUIs with 'combineGUI'.
instance (Monad m, Monoid a, Monoid b) => Monoid (GUI m i a b) where
    mempty = pure mempty
    mappend g h = combineGUI g h mappend

-- | A GUI is a functor by applying a function to the eventual produced
-- value.
instance Monad m => Functor (GUI m i a) where
    fmap f (GUI v) = GUI $ fmap (fmap f) v

-- | A GUI is applicative if its UX\'s left value is a monoid. It responds
-- to 'pure' by returning a GUI that has no user interface and immediately
-- produces the argument. It responds to '<*>' by applying the left
-- argument to the right. Each side\'s left UX value will be 'mappend' \'d.
instance (Monad m, Monoid a) => Applicative (GUI m i a) where
    pure = GUI . pure . pure
    (GUI vf) <*> (GUI va) = GUI $ ((<*>) <$> vf) <*> va

-- | A GUI is a monad if its UX's left value is a monoid. It responds to
-- '>>=' by returning a new GUI that runs until it produces a value, then
-- that value is used to create yet another GUI.
instance (Monad m, Monoid a) => Monad (GUI m i a) where
    (GUI v) >>= f = GUI $ Var $ \i -> do
        (UX a e, v') <- runVar v i
        case e of
            NoEvent -> return (UX a NoEvent, runGUI $ GUI v' >>= f)
            Event b -> runVar (runGUI $ f b) i

-- | A GUI can perform IO if its underlying monad can perform IO.
instance (MonadIO m, Monoid a) => MonadIO (GUI m i a) where
    liftIO f = GUI $ Var $ \_ -> do
        a <- liftIO f
        return (UX mempty (Event a), runGUI $ pure a)
--------------------------------------------------------------------------------
-- $creation
-- In order to create a GUI you must first have a datatype that is
-- 'Renderable'. Then you must create a 'varying' value of that datatype.
-- Also needed is an event stream that eventually ends the user's interaction.
-- The idea is that your interface varies over time and/or user input but
-- eventually produces a result value that can be used in a monadic
-- sequence.
--------------------------------------------------------------------------------
-- | Creates a new GUI displaying an interface that eventually produces a value.
-- The type used to represent the user interface must have a 'Decomposable'
-- instance, that way the resulting GUI\'s discrete values can be rendered.
gui :: (Monad m, Monad n, Composite a n r t)
    => Var m i a
    -- ^ The stream of a changing user interface.
    -> Var m i (Event b)
    -- ^ The event stream that concludes a user\'s interaction. When this
    -- stream produces an event the interaction will end and the merging
    -- function will be used to create the GUI\'s return type.
    -> (a -> b -> c)
    -- ^ The merging function that combines the interface's final value with the
    -- value produced by the event stream.
    -> GUI m i [(t, Element n r t)] c
gui v ve f = GUI $ Var $ \i -> do
    (a, v')  <- runVar v i
    (e, ve') <- runVar ve i
    let ui = composite a
    case e of
        NoEvent -> return (UX ui NoEvent, runGUI $ gui v' ve' f)
        Event b -> return (UX ui (Event $ f a b), pure $ UX [] $ Event $ f a b)

--------------------------------------------------------------------------------
-- $transformation
-- Simply put - here we are applying some kind of transformation to your
-- renderable interface. This most likely a standard two or three dimensional
-- affine transformation. Since the transformation also changes over the
-- same domain it\'s possible to tween GUIs.
--------------------------------------------------------------------------------
-- | Transforms a GUI.
transformGUI :: (Monad m, Monoid t)
             => Var m i t -> GUI m i [(t, d)] b -> GUI m i [(t, d)] b
transformGUI vt g = GUI $ Var $ \i -> do
    (UX ui e, v) <- runVar (runGUI g) i
    (t, vt') <- runVar vt i
    let ui' = map (first (mappend t)) ui
    return (UX ui' e, runGUI $ transformGUI vt' $ GUI v)
--------------------------------------------------------------------------------
-- $combination
-- Combining two GUIs creates a new GUI. The strategy taken to combine the
-- result values of the two GUIs must be provided. With 'combineGUI' the
-- GUI runs until both component GUIs have concluded. With 'combineGUIUntil'
-- the GUI runs until either both component GUIs have concluded or
-- until a switching event occurs.
--------------------------------------------------------------------------------
-- | Combines two GUIs. The resulting GUI will not produce a value until
-- both component GUIs have produced a value. At that moment a merging function
-- is used to combine the two values into the resulting GUI\'s return type.
-- The component GUIs\' graphical representations (the left UX values) are
-- 'mappend'\d together.
combineGUI :: (Monad m, Monoid u)
           => GUI m i u a
           -- ^ The first GUI.
           -> GUI m i u b
           -- ^ The second GUI.
           -> (a -> b -> c)
           -- ^ The merging function.
           -> GUI m i u c
combineGUI (GUI va) (GUI vb) f = GUI $ Var $ \i -> do
        (UX a ea, va') <- runVar va i
        (UX b eb, vb') <- runVar vb i
        return (UX (a <> b) (f <$> ea <*> eb),
                runGUI $ combineGUI (GUI va') (GUI vb') f)

-- | Combines two GUIs. The resulting GUI will not produce a value until
-- either both component GUIs have produced a value, or until a switching
-- event occurs. At that moment a merging function is used to combine any
-- available produced values in the resulting GUI\'s return type.
-- The component GUIs\' graphical representations (the left UX values) are
-- 'mappend'\d together.
combineGUIUntil :: (Monad m, Monoid u)
                => GUI m i u a
                -> GUI m i u b
                -> Var m i (Event c)
                -> (Either c (a,b) -> d)
                -> GUI m i u d
combineGUIUntil (GUI va) (GUI vb) vc f = GUI $ Var $ \i -> do
    (UX ua ea, va') <- runVar va i
    (UX ub eb, vb') <- runVar vb i
    (ec, vc')       <- runVar vc i
    let g ex v = case ex of
                     Event x -> pure $ UX mempty $ Event x
                     NoEvent -> v
        va'' = g ea va'
        vb'' = g eb vb'
        ma = toMaybe ea
        mb = toMaybe eb
        mc = toMaybe ec
        e  = case (ma,mb,mc) of
                 (Just a, Just b,      _) -> Event $ f $ Right (a, b)
                 (     _,      _, Just c) -> Event $ f $ Left c
                 _                        -> NoEvent
    return (UX (ua <> ub) e, runGUI $ combineGUIUntil (GUI va'') (GUI vb'') vc' f)

-- | Run two GUIs at the same time and return the result of the GUI that
-- concludes first.
eitherGUI :: (Monad m, Monoid u) => GUI m i u a -> GUI m i u a -> GUI m i u a
eitherGUI (GUI va) (GUI vb) = GUI $ Var $ \i -> do
    (UX ua ea, va') <- runVar va i
    (UX ub eb, vb') <- runVar vb i
    case (ea,eb) of
        (Event _,_) -> return (UX (ua <> ub) ea, va')
        (_,Event _) -> return (UX (ua <> ub) eb, vb')
        (_,_)       -> return (UX (ua <> ub) NoEvent,
                               runGUI $ eitherGUI (GUI va') (GUI vb') )
