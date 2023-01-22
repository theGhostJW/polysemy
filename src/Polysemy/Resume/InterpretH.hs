{-# LANGUAGE BangPatterns #-}
module Polysemy.Resume.InterpretH where
{-
(
  -- * Effect
  Resumable,

  -- * Actions
  resume,

  -- * Interpretations
  runResumableBase,
  ) where

import Polysemy
import Polysemy.HigherOrder
import Polysemy.Opaque
import Polysemy.Internal
import Polysemy.Internal.Utils
import Polysemy.Internal.Scoped
import Polysemy.Internal.Resume

runResumableBase :: forall err eff r
                  . (  forall q x
                      . Sem (eff ': Opaque q ': r) x
                     -> Sem (Opaque q ': r) (Either err x)
                    )
                 -> InterpreterFor (Resumable err eff) r
runResumableBase interp =
  interpretFast \case
    Run w _ ->
      errorWithoutStackTrace ("unhandled ScopedRun of depth " ++ show w)
  . go 0
  . raiseUnder
  where
    go :: Word
       -> InterpreterFor (Resumable err eff) (Run eff ': r)
    go depth sem = sem & interpretH \case
      ResumableRun r -> propagate r
      Resume m -> do
        res <- m depth & runExposeH' \m' ->
          go_ depth' m'
          & exposeRunInterpretH depth
          & toOpaqueAt @'[_]
          & interp
          & fromOpaque
        case res of
          Left e -> return (Left e)
          Right ta -> Right <$> restoreH ta
      where
        !depth' = depth + 1
    {-# INLINE go #-}

    go_ :: Word
        -> InterpreterFor (Resumable err eff) (Run eff ': r)
    go_ = go
    {-# NOINLINE go_ #-}
-}
