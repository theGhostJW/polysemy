{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# OPTIONS_HADDOCK not-home #-}

-- | Description: The basic interpreter-building combinators
module Polysemy.Internal.Combinators
  ( -- * First order
    rewrite
  , rewriteAt
  , transform
  , transformUsing

    -- * Statefulness
  , stateful
  , lazilyStateful
  ) where

import Data.Coerce
import Data.Type.Equality
import Polysemy.Internal
import Polysemy.Internal.Union
import Polysemy.Internal.Sing
import Polysemy.Internal.Core
import Polysemy.Internal.Membership
import Polysemy.Internal.Utils

runWeaveState :: s -> Sem (Weave ((,) s) r ': r) a -> Sem r (s, a)
runWeaveState s0' sem0' = go s0' sem0'
  where
    go :: s -> Sem (Weave ((,) s) r ': r) a -> Sem r (s, a)
    go s0 sem0 = Sem $ \k c0 ->
      runSem sem0
        (\u c s -> case decomp u of
            Left g -> (`k` (\(s', x) -> c x s')) $
              weave
                (s, ())
                (uncurry go_)
                (go_ s)
                g
            Right wav -> fromFOEff wav $ \ex -> \case
              RestoreW (s', a) -> c (ex a) s'
              GetStateW main -> c (ex (main ((,) s))) s
              LiftWithW main -> c (ex (main (go_ s))) s
              EmbedW m -> runSem m k (\a -> c (ex a) s)
        )
        (\a s -> c0 (s, a))
        s0
    {-# INLINE go #-}

    go_ :: s -> Sem (Weave ((,) s) r ': r) a -> Sem r (s, a)
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINEABLE runWeaveState #-}

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
    :: forall e2 e1 r a
     . (forall z x. e1 z x -> e2 z x)
    -> Sem (e1 ': r) a
    -> Sem (e2 ': r) a
rewrite f = go
  where
    go :: forall x. Sem (e1 ': r) x -> Sem (e2 ': r) x
    go = hoistSem $ \u -> hoist go_ $ case decompCoerce u of
      Left g -> g
      Right wav -> Union Here $ rewriteWeaving f wav
    {-# INLINE go #-}

    go_ :: forall x. Sem (e1 ': r) x -> Sem (e2 ': r) x
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINEABLE rewrite #-}

rewriteAt
    :: forall l e2 e1 r a
     . SList l
    -> (forall z x. e1 z x -> e2 z x)
    -> Sem (Append l (e1 ': r)) a
    -> Sem (Append l (e2 ': r)) a
rewriteAt sl f = go
  where
    go :: forall x. Sem (Append l (e1 ': r)) x -> Sem (Append l (e2 ': r)) x
    go = hoistSem $ \(Union pr wav) -> hoist go_ $ case isMemberAt @r @e1 @e2 sl pr of
      Left pr' -> Union pr' wav
      Right Refl -> Union (memberAt @r sl) $ rewriteWeaving f wav
    {-# INLINE go #-}

    go_ :: forall x. Sem (Append l (e1 ': r)) x -> Sem (Append l (e2 ': r)) x
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINEABLE rewriteAt #-}


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
{-# INLINE transform #-}

transformUsing
    :: forall e2 e1 r a
     . ElemOf e2 r
    -> (forall z x. e1 z x -> e2 z x)
    -> Sem (e1 ': r) a
    -> Sem r a
transformUsing pr f = go
  where
    go :: forall x. Sem (e1 ': r) x -> Sem r x
    go = hoistSem $ \u -> hoist go_ $ case decomp u of
      Left g -> g
      Right wav -> Union pr $ rewriteWeaving f wav
    {-# INLINE go #-}

    go_ :: forall x. Sem (e1 ': r) x -> Sem r x
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINEABLE transformUsing #-}
