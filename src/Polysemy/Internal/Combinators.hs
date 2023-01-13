{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# OPTIONS_HADDOCK not-home #-}

-- | Description: The basic interpreter-building combinators
module Polysemy.Internal.Combinators
  ( -- * First order
    rewrite
  , transform
  , transformUsing

    -- * Statefulness
  , stateful
  , lazilyStateful
  ) where

import Data.Coerce
import Polysemy.Internal
import Polysemy.Internal.Union
import Polysemy.Internal.Core
import Polysemy.Internal.Utils

runWeaveState :: s -> Sem (Weave ((,) s) r ': r) a -> Sem r (s, a)
runWeaveState s0 sem0 = Sem $ \k c0 ->
  runSem sem0
    (\u c s -> case decomp u of
        Left g -> (`k` (\(s', x) -> c x s')) $
          weave
            (s, ())
            (uncurry runWeaveState)
            (runWeaveState s)
            g
        Right wav -> fromFOEff wav $ \ex -> \case
          RestoreW (s', a) -> c (ex a) s'
          GetStateW main -> c (ex (main ((,) s))) s
          LiftWithW main -> c (ex (main (runWeaveState s))) s
          EmbedW m -> runSem m k (\a -> c (ex a) s)
    )
    (\a s -> c0 (s, a))
    s0

runWeaveLazyState :: s -> Sem (Weave (LazyT2 s) r ': r) a -> Sem r (LazyT2 s a)
runWeaveLazyState s0 sem0 = Sem $ \k c0 ->
  runSem sem0
    (\u c s -> case decomp u of
        Left g -> (`k` (\(LazyT2 ~(s', x)) -> c x s')) $
          weave
            (LazyT2 (s, ()))
            (\(LazyT2 ~(s', sem)) -> coerce $ runWeaveLazyState s' sem)
            (coerce #. runWeaveLazyState s)
            g
        Right wav -> fromFOEff wav $ \ex -> \case
          RestoreW (LazyT2 ~(s', a)) -> c (ex a) s'
          GetStateW main -> c (ex (main (LazyT2 #. (,) s))) s
          LiftWithW main -> c (ex (main (runWeaveLazyState s))) s
          EmbedW m -> runSem m k (\a -> c (ex a) s)
    )
    (\a s -> c0 (LazyT2 (s, a)))
    s0

------------------------------------------------------------------------------
-- | Like 'interpret', but with access to an intermediate state @s@.
stateful
    :: forall s e r a
     . (∀ x m. e m x -> s -> Sem r (s, x))
    -> s -> Sem (e ': r) a -> Sem r (s, a)
stateful f = go
  where
    go :: forall x. s -> Sem (e ': r) x -> Sem r (s, x)
    go s0 sem0 = Sem $ \k c0 ->
      runSem sem0
        (\u c s -> case decomp u of
            Left g -> (`k` (\(s', x) -> c x s')) $
              weave
                (s, ())
                (uncurry go_)
                (runWeaveState s)
                g
            Right wav -> fromFOEff wav $ \ex e ->
              runSem (f e s) k (\(s', x) -> c (ex x) s')
        )
        (\a s -> c0 (s, a))
        s0
    {-# INLINE go #-}

    go_ :: forall x. s -> Sem (e ': r) x -> Sem r (s, x)
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINE[3] stateful #-}


------------------------------------------------------------------------------
-- | Like 'interpret', but with access to an intermediate state @s@.
lazilyStateful
    :: forall e s r a
     . (∀ x m. e m x -> s -> Sem r (s, x))
    -> s
    -> Sem (e ': r) a
    -> Sem r (s, a)
lazilyStateful f = go
  where
    go :: forall x. s -> Sem (e ': r) x -> Sem r (s, x)
    go s0 sem0 = Sem $ \k c0 ->
      runSem sem0
        (\u c s -> case decomp u of
            Left g -> (`k` (\(LazyT2 ~(s', x)) -> c x s')) $
              weave
                (LazyT2 (s, ()))
                (\(LazyT2 ~(s', sem)) -> coerce $ go_ s' sem)
                (runWeaveLazyState s)
                g
            Right wav -> fromFOEff wav $ \ex e ->
              runSem (f e s) k (\ ~(s', x) -> c (ex x) s')
        )
        (\a s -> c0 (s, a))
        s0
    {-# INLINE go #-}

    go_ :: forall x. s -> Sem (e ': r) x -> Sem r (s, x)
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINE[3] lazilyStateful #-}

------------------------------------------------------------------------------
-- | Rewrite an effect @e1@ directly into @e2@, and put it on the top of the
-- effect stack.
--
-- @'rewrite' n = 'interpretH' ('propagate' . n)@
--
-- @since 1.2.3.0
rewrite
    :: forall e1 e2 r a
     . (forall z x. e1 z x -> e2 z x)
    -> Sem (e1 ': r) a
    -> Sem (e2 ': r) a
rewrite f (Sem m) = Sem $ \k -> m $ \u ->
  k $ hoist (rewrite f) $ case decompCoerce u of
    Left x -> x
    Right wav -> Union Here (rewriteWeaving f wav)
      -- Union Here $ Weaving (f e) mkT lwr ex


------------------------------------------------------------------------------
-- | Transform an effect @e1@ into an effect @e2@ that is already somewhere
-- inside of the stack.
--
-- @since 1.2.3.0
transform
    :: forall e2 e1 r a
     . Member e2 r
    => (forall z x. e1 z x -> e2 z x)
    -> Sem (e1 ': r) a
    -> Sem r a
transform = transformUsing membership

transformUsing
    :: forall e2 e1 r a
     . ElemOf e2 r
    -> (forall z x. e1 z x -> e2 z x)
    -> Sem (e1 ': r) a
    -> Sem r a
transformUsing pr f (Sem m) = Sem $ \k -> m $ \u ->
  k $ hoist (transformUsing pr f) $ case decomp u of
    Left g -> g
    Right wav -> Union pr $ rewriteWeaving f wav
