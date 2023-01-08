{-# LANGUAGE BangPatterns, TemplateHaskell, TupleSections #-}
{-# OPTIONS_HADDOCK not-home, prune #-}

-- | Description: The 'Writer' effect
module Polysemy.Internal.Writer where

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import qualified Control.Monad.Trans.Writer.Lazy as Lazy

import Data.Bifunctor
import Data.Tuple (swap)
import Data.Semigroup

import Polysemy
import Polysemy.Final

import Polysemy.Internal
import Polysemy.Internal.Combinators
import Polysemy.Internal.Union
import Polysemy.Internal.Core
import Polysemy.Internal.Utils


------------------------------------------------------------------------------
-- | An effect capable of emitting and intercepting messages.
data Writer o m a where
  -- | Write a message to the log.
  Tell   :: o -> Writer o m ()
  -- | Return the log produced by the higher-order action.
  Listen :: ∀ o m a. m a -> Writer o m (o, a)
  -- | Run the given action and apply the function it returns to the log.
  Pass   :: m (o -> o, a) -> Writer o m a

tell :: Member (Writer o) r => o -> Sem r ()
tell = send . Tell

listen :: Member (Writer o) r => Sem r a -> Sem r (o, a)
listen = send . Listen

pass :: Member (Writer o) r => Sem r (o -> o, a) -> Sem r a
pass = send . Pass
-- makeSem ''Writer

-- TODO(KingoftheHomeless): Research if this is more or less efficient than
-- using 'reinterpretH' + 'subsume'

-----------------------------------------------------------------------------
-- | Rewrite a @'Writer' o@ effect into a  @'Writer' ('Endo' o)@ effect,
-- right-associating all uses of '<>' for @o@.
--
-- This can be used in order to create @-AssocR@ variants out of regular
-- 'Writer' interpreters.
--
-- @since 1.2.0.0
writerIntoEndoWriter
    :: Monoid o
    => Sem (Writer o ': r) a
    -> Sem (Writer (Endo o) ': r) a
writerIntoEndoWriter = reinterpretH $ \case
  Tell o   -> tell (Endo (o <>))
  Listen m -> do
    (o, a) <- listen (runH m)
    return (appEndo o mempty, a)
  Pass m -> pass $ do
    (f, a) <- runH m
    let f' (Endo oo) = let !o' = f (oo mempty) in Endo (o' <>)
    return (f', a)


------------------------------------------------------------------------------
-- | A variant of 'Polysemy.Writer.runWriterTVar' where an 'STM' action is
-- used instead of a 'TVar' to commit 'tell's.
runWriterSTMAction :: forall o r a
                          . (Member (Final IO) r, Monoid o)
                         => (o -> STM ())
                         -> Sem (Writer o ': r) a
                         -> Sem r a
runWriterSTMAction write = interpretH $ \case
  Tell o -> embedFinal $ atomically (write o)
  Listen m -> controlFinal $ \lower -> mask $ \restore -> do
    -- See below to understand how this works
    tvar   <- newTVarIO mempty
    switch <- newTVarIO False
    fa     <-
        restore
          (lower (runWriterSTMAction (writeListen tvar switch) (runH' m)))
      `onException`
        commitListen tvar switch
    o      <- commitListen tvar switch
    return $ fmap (o, ) fa
  Pass m -> controlFinal $ \lower -> mask $ \restore -> do
    -- See below to understand how this works
    tvar   <- newTVarIO mempty
    switch <- newTVarIO False
    t      <-
        restore (lower (runWriterSTMAction (writePass tvar switch) (runH' m)))
      `onException`
        commitPass tvar switch id
    commitPass tvar switch $ foldr (const . fst) id t
    return $ fmap snd t

  where
    {- KingoftheHomeless:
      'writeListen'/'writePass' is used by the argument computation to a
      'listen' or 'pass' in order to 'tell', rather than directly using
      the provided 'write'.
      This is because we need to temporarily store its
      'tell's locally in order for the 'listen'/'pass' to work
      properly. In the case of 'listen', this is done in parallel with
      the global 'write's. In the case of 'pass', the argument computation
      doesn't use 'write' at all, and instead, when the computation completes,
      commit the changes it made to the local tvar by 'commitPass',
      globally 'write'ing it all at once.
      ('commitListen' serves only as a (likely unneeded) safety measure.)

      'commitListen''/'commitPass' is protected by 'mask'+'onException'.
      Combine this with the fact that the 'controlFinal' can't be
      interrupted by pure errors emitted by effects (since these will be
      represented as part of the effectful state), and we guarantee that no
      writes will be lost if the argument computation fails for whatever reason.

      The argument computation to a 'pass' may also spawn
      asynchronous computations which do 'tell's of their own.
      In order to make sure these 'tell's won't be lost once a
      'pass' completes, a switch is used to
      control which tvar 'writePass' writes to. The switch is flipped
      atomically together with commiting the writes of the local tvar
      as part of 'commit'. Once the switch is flipped,
      any asynchronous computations spawned by the argument
      computation will write to the global tvar instead of the local
      tvar (which is no longer relevant), and thus no writes will be
      lost.
    -}

    writeListen :: TVar o
                -> TVar Bool
                -> o
                -> STM ()
    writeListen tvar switch = \o -> do
      alreadyCommitted <- readTVar switch
      unless alreadyCommitted $ do
        s <- readTVar tvar
        writeTVar tvar $! s <> o
      write o
    {-# INLINE writeListen #-}

    writePass :: TVar o
              -> TVar Bool
              -> o
              -> STM ()
    writePass tvar switch = \o -> do
      useGlobal <- readTVar switch
      if useGlobal then
        write o
      else do
        s <- readTVar tvar
        writeTVar tvar $! s <> o
    {-# INLINE writePass #-}

    commitListen :: TVar o
                 -> TVar Bool
                 -> IO o
    commitListen tvar switch = atomically $ do
      writeTVar switch True
      readTVar tvar
    {-# INLINE commitListen #-}

    commitPass :: TVar o
               -> TVar Bool
               -> (o -> o)
               -> IO ()
    commitPass tvar switch f = atomically $ do
      o <- readTVar tvar
      let !o' = f o
      -- Likely redundant, but doesn't hurt.
      alreadyCommitted <- readTVar switch
      unless alreadyCommitted $
        write o'
      writeTVar switch True
    {-# INLINE commitPass #-}

runWeaveLazyWriter :: Monoid o
                   => Sem (Weave (LazyT2 o) ': r) a -> Lazy.WriterT o (Sem r) a
runWeaveLazyWriter = weaveToTransWeave
-- runWeaveLazyWriter sem0 = Sem $ \k c0 ->
--   runSem sem0
--     (\u c1 c2 -> case decomp u of
--         Left g ->
--           (`k` \(LazyT2 ~(o, x)) -> c1 x (\ores -> c2 $ \o' -> ores (o <> o')))
--           $ weave
--              (LazyT2 (mempty, ()))
--              (\(LazyT2 ~(o', sem)) ->
--                 fmap (\(LazyT2 ~(o, x)) -> LazyT2 (o' <> o, x))
--                      (runWeaveLazyWriter sem))
--              runWeaveLazyWriter
--              g
--         Right wav -> fromFOEff wav $ \ex -> \case
--           RestoreW (LazyT2 ~(o, a)) ->
--             c1 (ex a) $ \ores -> c2 \o' -> ores (o <> o')
--           GetStateW main -> c1 (ex (main (LazyT2 #. (,) mempty))) c2
--           LiftWithW main -> c1 (ex (main runWeaveLazyWriter)) c2
--     )
--     (\a c -> c (\o -> c0 (LazyT2 (o, a))))
--     ($ mempty)

interpretViaLazyWriter
  :: forall o e r a
   . Monoid o
  => (forall x. Weaving e (Sem (e ': r)) x -> Sem r (o, x))
  -> Sem (e ': r) a
  -> Sem r (o, a)
interpretViaLazyWriter f =
    fmap (\ ~(a, s) -> (s, a))
  . Lazy.runWriterT
  #. usingSem return \u c ->
    case decomp u of
      Left g ->
        liftHandlerWithNat
          (Lazy.WriterT
           #. fmap (\ ~(s, a) -> (a, s)) . interpretViaLazyWriter f)
          liftSem
          g
        >>= c
      Right wav ->
        Lazy.WriterT ((\ ~(s, a) -> (a, s)) <$> f wav) >>= c

-- interpretViaLazyWriter f sem0 = Sem $ \k c0 ->
--   runSem sem0
--     (\u c1 c2 -> case decomp u of
--         Left g ->
--           (`k` \(LazyT2 ~(o, x)) -> c1 x (\ores -> c2 $ \o' -> ores (o <> o')))
--           $ weave
--              (LazyT2 (mempty, ()))
--              (\(LazyT2 ~(o', sem)) ->
--                 fmap (\ ~(o, x) -> LazyT2 (o' <> o, x))
--                      (interpretViaLazyWriter f sem))
--              runWeaveLazyWriter
--              g
--         Right wav ->
--           runSem
--             (f wav)
--             k
--             (\ ~(o, x) -> c1 x (\ores -> c2 $ \o' -> ores (o <> o')))
--     )
--     (\a c -> c (\o -> c0 (o, a)))
--     ($ mempty)
