{-# LANGUAGE BangPatterns #-}
module Polysemy.Scoped.Handrolled where
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
import Polysemy.Membership
import Polysemy.Opaque
import Polysemy.Internal.Utils
import Polysemy.Internal.Scoped
import Polysemy.Internal.Core
import Polysemy.Internal
import Polysemy.Internal.Union

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
  where
    go :: forall x
        . Word
       -> Sem (Scoped eff param ': r) x -> Sem (Run eff ': r) x
    go depth sem = Sem $ \k -> runSem sem $ \u c -> case decompCoerce u of
      Left g -> k (hoist (go_ depth) g) c
      Right wav -> case wav of
        Sent (Scoped p m) n ->
          go_ depth' (n (m depth))
          & exposeRunHandrolled depth
          & toOpaqueAt @'[_]
          & interp p
          & fromOpaque
          & usingSem c k
        Weaved (Scoped p m) _ mkS wv _ ->
          go_ depth' (wv (mkS (m depth)))
          & exposeRunHandrolled depth
          & toOpaqueAt @'[_]
          & interp p
          & fromOpaque
          & usingSem (c .# coerce) k
        Sent (ScopedRun r) n -> k (Union Here (Sent r (go_ depth . n))) c
        Weaved (ScopedRun r) trav mkS wv lwr ->
          k (Union Here (Weaved r trav mkS (go_ depth . wv) lwr)) c
      where
        !depth' = depth + 1
    {-# INLINE go #-}

    go_ :: forall x
         . Word
        -> Sem (Scoped eff param ': r) x -> Sem (Run eff ': r) x
    go_ = go
    {-# NOINLINE go_ #-}

runScoped_
  :: (forall q x. Sem (eff ': Opaque q ': r) x -> Sem (Opaque q ': r) x)
  -> InterpreterFor (Scoped_ eff) r
runScoped_ interp = runScoped (\() -> interp)
{-# INLINE runScoped_ #-}
-}
