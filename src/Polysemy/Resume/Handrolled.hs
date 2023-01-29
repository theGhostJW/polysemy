{-# LANGUAGE BangPatterns #-}
module Polysemy.Resume.Handrolled (
  -- * Effect
  Resumable,

  -- * Actions
  resume,

  -- * Interpretations
  runResumableBase,
  ) where

import Data.Functor.Identity
import Polysemy
import Polysemy.Membership
import Polysemy.Opaque
import Polysemy.Internal
import Polysemy.Internal.Utils
import Polysemy.Internal.Scoped
import Polysemy.Internal.Resume
import Polysemy.Internal.Core
import Polysemy.Internal.Union

runResumableBase :: forall err eff r
                  . (  forall q x
                      . Sem (eff ': Opaque q ': r) x
                     -> Sem (Opaque q ': r) (Either err x)
                    )
                 -> InterpreterFor (Resumable err eff) r
runResumableBase interp =
  interpretFast \case
    Run w _ ->
      errorWithoutStackTrace ("unhandled ResumableRun of depth " ++ show w)
  . go 0
  where
    go :: forall x
        . Word
       -> Sem (Resumable err eff ': r) x -> Sem (Run eff ': r) x
    go depth sem = Sem $ \k -> runSem sem $ \u c -> case decompCoerce u of
      Left g -> k (hoist (go_ depth) g) c
      Right wav -> case wav of
        Sent (Resume m) n ->
          go_ depth' (n (m depth))
          & exposeRunHandrolled depth
          & toOpaqueAt @'[_]
          & interp
          & fromOpaque
          & usingSem c k
        Weaved (Resume m) (Traversal trav) mkS wv _ ex ->
          go_ depth' (wv (mkS (m depth)))
          & exposeRunHandrolled depth
          & toOpaqueAt @'[_]
          & interp
          & fromOpaque
          & usingSem (c . ex
                      . either (mkS . Left)
                               (runIdentity #. trav (Identity #. Right)))
                      k
        Sent (ResumableRun r) n -> k (Union Here (Sent r (go_ depth . n))) c
        Weaved (ResumableRun r) trav mkS wv lwr ex ->
          k (Union Here (Weaved r trav mkS (go_ depth . wv) lwr ex)) c
      where
        !depth' = depth + 1
    {-# INLINE go #-}

    go_ :: forall x
         . Word
        -> Sem (Resumable err eff ': r) x -> Sem (Run eff ': r) x
    go_ = go
    {-# NOINLINE go_ #-}
