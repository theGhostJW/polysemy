module Polysemy.Internal.Scoped where

import Polysemy
import Polysemy.HigherOrder
import Polysemy.Internal.Core
import Polysemy.Internal.Membership
import Polysemy.Internal.Utils

data Run eff m a where
  Run :: {-# UNPACK #-} !Word -> eff m a -> Run eff m a

data Scoped eff param m a where
  ScopedRun :: forall eff param m a
             . Run eff m a -> Scoped eff param m a
  Scoped :: forall eff param m a
          . param -> (Word -> m a) -> Scoped eff param m a

type Scoped_ eff = Scoped eff ()

scoped :: forall eff param r a
        . Member (Scoped eff param) r
       => param -> Sem (eff ': r) a -> Sem r a
scoped p m = send @(Scoped eff param) $ Scoped p $ \w ->
  transform @(Scoped eff param) (ScopedRun . Run w) m
{-# INLINE scoped #-}

scoped_ :: Member (Scoped_ eff) r => Sem (eff ': r) a -> Sem r a
scoped_ = scoped ()
{-# INLINE scoped_ #-}

rescope :: forall eff p1 p2 r
         . Member (Scoped eff p2) r
        => (p1 -> p2)
        -> InterpreterFor (Scoped eff p1) r
rescope t = transform @(Scoped eff p2) \case
  ScopedRun sr -> ScopedRun sr
  Scoped p m -> Scoped (t p) m

exposeRunInterpretH :: forall eff r
                     . Word
                    -> (   forall x
                         . Sem (Run eff ': r) x
                        -> Sem (eff ': Run eff ': r) x
                       )
exposeRunInterpretH depth = reinterpret2H \case
  Run depth' e | depth == depth' -> propagate e
  other -> propagateUsing (There Here) other
{-# INLINE exposeRunInterpretH #-}

exposeRunHandrolled :: forall eff r
                     . Word
                    -> (   forall x
                         . Sem (Run eff ': r) x
                        -> Sem (eff ': Run eff ': r) x
                       )
exposeRunHandrolled depth = go
  where
    go :: forall x. Sem (Run eff ': r) x -> Sem (eff ': Run eff ': r) x
    go = hoistSem $ \u -> hoist go_ $ case decomp u of
      Left (Union pr wav) -> Union (There (There pr)) wav
      Right wav -> wav & rewriteWeaving' \case
        Run depth' e | depth == depth' -> Bundle Here e
        other -> Bundle (There Here) other
    {-# INLINE go #-}

    go_ :: forall x. Sem (Run eff ': r) x -> Sem (eff ': Run eff ': r) x
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINE exposeRunHandrolled #-}
