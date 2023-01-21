module Polysemy.Scoped (
  -- * Effect
  Scoped,
  Scoped_,

  -- * Actions
  scoped,
  scoped_,

  -- * Interpretations
  runScoped,
  runScoped',
  runScoped_,
  rescope,
  ) where

import Polysemy
import Polysemy.Membership
import Polysemy.Meta
import Polysemy.Opaque
import Polysemy.Newtype
import Polysemy.HigherOrder
import Polysemy.Internal.Utils

-- TODO: consider exposing this. Either from here or an internal module
data ScopedMeta eff param :: MetaEffect where
  ScopedMeta :: param -> z a -> ScopedMeta eff param '[z :% eff] m a

-- TODO: consider exposing the constructor.
-- Either from here or an internal module
newtype Scoped eff param m a = Scoped (Meta (ScopedMeta eff param) m a)

type Scoped_ eff = Scoped eff ()

scoped :: forall eff param r a
        . Member (Scoped eff param) r
       => param -> Sem (eff ': r) a -> Sem r a
scoped p m =
  ScopedMeta p (raiseUnder m)
  & sendMetaUsing Here
  & subsumeCoerce @(Scoped eff param)
{-# INLINE scoped #-}

scoped_ :: Member (Scoped_ eff) r => Sem (eff ': r) a -> Sem r a
scoped_ = scoped ()
{-# INLINE scoped_ #-}

runScoped :: forall eff param r
           . (   forall q x
               . param
              -> Sem (eff ': Opaque q ': r) x -> Sem (Opaque q ': r) x
             )
          -> InterpreterFor (Scoped eff param) r
runScoped interp =
  coerceEff
  >>> interpretMeta @(ScopedMeta eff param) \case
    ScopedMeta param m -> do
      InterpreterH go <- getInterpreterH
      runMeta' (go . runOpaqueBundleAt @0 . interp param . collectOpaqueBundleAt @1 @'[_, _]) m

      -- runMeta' (runScoped (\p -> runOpaqueBundleAt @0 . interp p . collectOpaqueBundleAt @1 @'[_, _] ) . coerceEff . runOpaqueBundleAt @0 . interp param . collectOpaqueBundleAt @1 @'[_, _]) m

runScoped' :: forall eff r
           . (   forall q x
               . Int
              -> Sem (eff ': Opaque q ': r) x -> Sem (Opaque q ': r) x
             )
          -> InterpreterFor (Scoped eff Int) r
runScoped' interp =
  coerceEff
  >>> interpretMeta @(ScopedMeta eff Int) \case
    ScopedMeta param m ->
      runMeta' (runScoped (\p -> runOpaqueBundleAt @0 . interp (p - 1) . collectOpaqueBundleAt @1 @'[_, _] ) . coerceEff . runOpaqueBundleAt @0 . interp param . collectOpaqueBundleAt @1 @'[_, _]) m

runScoped_
  :: (forall q x. Sem (eff ': Opaque q ': r) x -> Sem (Opaque q ': r) x)
  -> InterpreterFor (Scoped_ eff) r
runScoped_ interp = runScoped (\() -> interp)
{-# INLINE runScoped #-}

rescope ::
  ∀ eff p2 p1 r .
  Member (Scoped eff p2) r =>
  (p1 -> p2) ->
  InterpreterFor (Scoped eff p1) r
rescope f =
  coerceEff @(Meta (ScopedMeta eff p1))
  >>> metaIntoMeta @(ScopedMeta eff p2) (\(ScopedMeta p e) -> ScopedMeta (f p) e)
  >>> subsumeCoerce @(Scoped eff p2)
{-# INLINEABLE rescope #-}
