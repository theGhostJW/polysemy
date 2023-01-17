{-# LANGUAGE BangPatterns #-}
module Polysemy.Scoped.Handrolled (
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
    go depth sem = Sem $ \k -> runSem sem $ \u c -> case decomp u of
      Left g -> k (hoist (go_ depth) g) c
      Right wav -> case wav of
        Sent (Scoped p m) n ->
          go_ depth' (n (m depth))
          & exposeRunHandrolled depth
          & toOpaqueAt @'[_]
          & interp p
          & fromOpaque
          & usingSem c k
        Weaved (Scoped p m) _ mkS wv _ ex ->
          go_ depth' (wv (mkS (m depth)))
          & exposeRunHandrolled depth
          & toOpaqueAt @'[_]
          & interp p
          & fromOpaque
          & usingSem (c . ex) k
        Sent (ScopedRun r) n -> k (Union Here (Sent r (go_ depth . n))) c
        Weaved (ScopedRun r) trav mkS wv lwr ex ->
          k (Union Here (Weaved r trav mkS (go_ depth . wv) lwr ex)) c
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
