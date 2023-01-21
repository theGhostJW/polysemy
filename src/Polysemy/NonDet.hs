{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Description: Interpreters for 'NonDet'
module Polysemy.NonDet
  ( -- * Effect
    NonDet (..)

    -- * Interpretations
  , runNonDet
  , runNonDetMaybe
  , nonDetToError
  ) where

import Control.Applicative
import Control.Monad
-- import Control.Monad.Trans.Maybe
import Control.Monad.Trans

import Polysemy
import Polysemy.Error
import Polysemy.Internal
import Polysemy.Internal.NonDet
import Polysemy.Internal.Union
import Polysemy.Internal.Utils
import Polysemy.Internal.Core

------------------------------------------------------------------------------
-- | Run a 'NonDet' effect in terms of some underlying 'Alternative' @f@.
runNonDet :: Alternative f => Sem (NonDet ': r) a -> Sem r (f a)
runNonDet = runNonDetC . runNonDetInC
  -- runSem sem0
  --   (\u c1 c2 -> case decomp u of
  --       Left g -> (`k` (\l -> foldr (\x c2' c3 -> c1 x $ \l -> c2' $ \l' -> c3 (l ++ l')) ($ []) l c2)) $
  --         weave
  --           [()]
  --           (fmap join . traverse runNonDet)
  --           runWeaveNonDet
  --           g
  --       Right (Sent e n) -> case e of
  --         Empty -> c2 []
  --         Choose l r ->
  --           let l' =n l
  --         RestoreW t -> foldr (\x c2' c3 -> c1 (ex x) $ \l -> c2' $ \l' -> c3 (l ++ l')) ($ []) t c2 -- c (ex a) s'
  --         GetStateW main -> c1 (ex (main (:[]))) c2
  --         LiftWithW main -> c1 (ex (main runWeaveNonDet)) c2
  --   )
  --   (\a c -> c [a])
  --   c0

------------------------------------------------------------------------------
-- | Run a 'NonDet' effect in terms of an underlying 'Maybe'
--
-- Unlike 'runNonDet', uses of '<|>' will not execute the
-- second branch at all if the first option succeeds.
--
-- @since 1.1.0.0
runNonDetMaybe :: Sem (NonDet ': r) a -> Sem r (Maybe a)
runNonDetMaybe =
    fmap (either (const Nothing) Just)
  . runError
  . rewrite \case
    Empty -> Throw ()
    Choose left right -> Catch left (\() -> right)
-- TODO: KingoftheHomeless: roll using MaybeT if I bother

------------------------------------------------------------------------------
-- | Transform a 'NonDet' effect into an @'Error' e@ effect,
-- through providing an exception that 'empty' may be mapped to.
--
-- This allows '<|>' to handle 'throw's of the @'Error' e@ effect.
--
-- @since 1.1.0.0
nonDetToError :: Member (Error e) r
              => e
              -> Sem (NonDet ': r) a
              -> Sem r a
nonDetToError (e :: e) = transform $ \case
  Empty -> Throw e
  Choose left right -> Catch left (\_ -> right)

-- This stuff is lifted from 'fused-effects'. Thanks guys!
runNonDetC :: (Alternative f, Applicative m) => NonDetC m a -> m (f a)
runNonDetC (NonDetC m) = m (fmap . (<|>) . pure) (pure empty)


newtype NonDetC m a = NonDetC
  { -- | A higher-order function receiving two parameters: a function to combine
    -- each solution with the rest of the solutions, and an action to run when no
    -- results are produced.
    unNonDetC :: forall b . (a -> m b -> m b) -> m b -> m b
  }
  deriving (Functor)

instance Applicative (NonDetC m) where
  pure a = NonDetC (\ cons -> cons a)

  NonDetC f <*> NonDetC a = NonDetC $ \ cons ->
    f (\ f' -> a (cons . f'))
  -- {-# INLINE (<*>) #-}

instance Alternative (NonDetC m) where
  empty = NonDetC (\ _ nil -> nil)
  -- {-# INLINE empty #-}

  NonDetC l <|> NonDetC r = NonDetC $ \ cons -> l cons . r cons
  -- {-# INLINE (<|>) #-}

instance Monad (NonDetC m) where
  NonDetC a >>= f = NonDetC $ \ cons ->
    a (\ a' -> unNonDetC (f a') cons)
  -- {-# INLINE (>>=) #-}

instance MonadTrans NonDetC where
  lift m = NonDetC $ \c b -> m >>= (`c` b)

-- an ugly attempt to skip using NonDetC. I decided I didn't care.
-- runWeaveNonDet :: Sem (Weave [] ': r) a -> Sem r [a]
-- runWeaveNonDet sem0 = Sem $ \k c0 ->
--   runSem sem0
--     (\u c1 c2 -> case decomp u of
--         Left g -> (`k` (\l -> foldr (\x c2' c3 -> c1 x $ \l -> c2' $ \l' -> c3 (l ++ l')) ($ []) l c2)) $
--           weave
--             [()]
--             (fmap join . traverse runWeaveNonDet)
--             runWeaveNonDet
--             g
--         Right wav -> fromFOEff wav $ \ex -> \case
--           RestoreW t -> foldr (\x c2' c3 -> c1 (ex x) $ \l -> c2' $ \l' -> c3 (l ++ l')) ($ []) t c2 -- c (ex a) s'
--           GetStateW main -> c1 (ex (main (:[]))) c2
--           LiftWithW main -> c1 (ex (main runWeaveNonDet)) c2
--     )
--     (\a c -> c [a])
--     c0

runWeaveNonDetInC :: Sem (Weave [] r ': r) a -> NonDetC (Sem r) a
runWeaveNonDetInC = usingSem return $ \u c -> case decomp u of
  Left g -> NonDetC $ \c' b' ->
    liftSem (weave
               [()]
               (fmap join . traverse runWeaveNonDet)
               runWeaveNonDet
               g)
    >>= foldr (\a -> unNonDetC (c a) c') b'
  Right wav -> fromFOEff wav $ \ex -> \case
    RestoreW t -> foldr (\a -> (c (ex a) <|>)) empty t
    GetStateW main -> c $ ex $ main (:[])
    LiftWithW main -> c $ ex $ main runWeaveNonDet
    EmbedW m -> lift m >>= (c . ex)

runWeaveNonDet :: Sem (Weave [] r ': r) a -> Sem r [a]
runWeaveNonDet = runNonDetC . runWeaveNonDetInC

runNonDetInC :: Sem (NonDet ': r) a -> NonDetC (Sem r) a
runNonDetInC = usingSem return $ \u c ->
  case decomp u of
    Left g -> NonDetC $ \c' b' ->
      liftSem (weave
                 [()]
                 (fmap join . traverse runNonDet)
                 runWeaveNonDet
                 g)
      >>= foldr (\a -> unNonDetC (c a) c') b'
    Right wav -> case wav of
      Sent e n -> case e of
        Empty -> NonDetC $ \_ b -> b
        Choose l r -> (runNonDetInC (n l) <|> runNonDetInC (n r)) >>= c
      Weaved e _ mkS wv _ -> case e of
        Empty -> NonDetC $ \_ b -> b
        Choose l r ->
          (runNonDetInC (wv (mkS l)) <|> runNonDetInC (wv (mkS r)))
          >>= c .# coerce
