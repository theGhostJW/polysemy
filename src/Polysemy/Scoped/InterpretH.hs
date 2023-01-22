{-# LANGUAGE BangPatterns #-}
module Polysemy.Scoped.InterpretH where
{-

  (
  -- * Effect
  Scoped,
  Scoped_,

  -- * Actions
  scoped,
  scoped_,

  -- * Interpretations
  runScoped,
  runScoped_,
  rescope,
  ) where

import Polysemy
import Polysemy.HigherOrder
import Polysemy.Opaque
import Polysemy.Internal
import Polysemy.Internal.Utils
import Polysemy.Internal.Scoped

runScoped :: forall eff param r
           . (   forall q x
               . param
              -> Sem (eff ': Opaque q ': r) x -> Sem (Opaque q ': r) x
             )
          -> InterpreterFor (Scoped eff param) r
runScoped interp =
  interpretFast \case
    Run w _ ->
      errorWithoutStackTrace ("unhandled ScopedRun of depth " ++ show w)
  . go 0
  . raiseUnder
  where
    go :: Word
       -> InterpreterFor (Scoped eff param) (Run eff ': r)
    go depth sem = sem & interpretH \case
      ScopedRun r -> propagate r
      Scoped p m -> m depth & runH' \m' ->
        go_ depth' m'
        & exposeRunInterpretH depth
        & toOpaqueAt @'[_]
        & interp p
        & fromOpaque
      where
        !depth' = depth + 1
    {-# INLINE go #-}

    go_ :: Word
        -> InterpreterFor (Scoped eff param) (Run eff ': r)
    go_ = go
    {-# NOINLINE go_ #-}

runScoped_
  :: (forall q x. Sem (eff ': Opaque q ': r) x -> Sem (Opaque q ': r) x)
  -> InterpreterFor (Scoped_ eff) r
runScoped_ interp = runScoped (\() -> interp)
{-# INLINE runScoped_ #-}
-}
