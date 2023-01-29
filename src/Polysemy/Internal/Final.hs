{-# LANGUAGE TemplateHaskell, PatternGuards, EmptyCase #-}
module Polysemy.Internal.Final
  (
    -- * Effect
    Final(..)

    -- * Actions
  , withWeavingToFinal
  , controlFinal
  , withLoweringToFinal
  , embedFinal

    -- * Combinators for Interpreting to the Final Monad
  , interpretFinal

    -- * Lowering
    -- | 'Lowering' is a domain-specific language very similar in
    -- use to 'Polysemy.HigherOrder', and is used to describe how
    -- higher-order effects are threaded down to the final monad.
    --
    -- 'withLoweringToFinal' should be used when 'controlFinal' is
    -- not powerful enough for your purposes. Notable combinators include
    -- 'runL', 'embed', 'liftWithL', and 'restoreL'.
  , Lowering

    -- ** Lifting the final monad to 'Lowering'
  , embed

    -- ** Lowering computations to the final monad
  , withProcessorL
  , controlWithProcessorL
  , processL

    -- ** Embedding computations into 'Lowering'
  , runL

    -- ** Lowering 'Lowering' to the final monad
  , controlL
  , liftWithL

    -- ** Manipulating effectful state
  , restoreL
  , runExposeL
  , exposeL

    -- * Interpretations
  , runM
  , finalToFinal

  -- * Interpretations for Other Effects
  , embedToFinal

  -- * Retrieving the type parameters of a 'Lowering' environemt
  , TypeParamsL(..)
  , getTypeParamsL
  ) where

import Data.Functor.Identity
import Data.Kind
import Polysemy.Internal
import Polysemy.Internal.Union
import Polysemy.Internal.Combinators
import Polysemy.Internal.HigherOrder
import Polysemy.Internal.TH.Effect
import Polysemy.Internal.Core
import Polysemy.Internal.Utils
import Polysemy.Internal.Reflection

-----------------------------------------------------------------------------
-- | An effect for embedding higher-order actions in the final target monad
-- of the effect stack.
--
-- This is very useful for writing interpreters that interpret higher-order
-- effects in terms of the final monad.
--
-- 'Final' is more powerful than 'Embed', but is also less flexible
-- to interpret (compare 'Polysemy.Embed.embedToEmbed' with 'finalToFinal').
-- If you only need the power of 'embed', then you should use 'Embed' instead.
--
-- /Note/: 'Final' actions are interpreted as actions of the final monad,
-- and the effectful state visible to 'controlFinal' \/ 'withLoweringToFinal'
-- \/ 'interpretFinal' is that of /all interpreters run in order to produce the/
-- /final monad/.
--
-- This means that any interpreter built using 'Final' will /not/ respect
-- local/global state semantics based on the order of interpreters run.
-- In this library, interpreters that make use of 'Final' signal this by having
-- a @-'Final'@ suffix.
--
-- State semantics of effects that are /not/ interpreted in terms of the final
-- monad will always appear local to effects that are interpreted in terms of
-- the final monad.
--
-- State semantics between effects that are interpreted in terms of the final
-- monad depend on the final monad. For example, if the final monad is a monad
-- transformer stack, then state semantics will depend on the order monad
-- transformers are stacked.
--
-- @since 1.2.0.0
newtype Final m z a where
  WithWeavingToFinal
    :: (forall t. WeavingInfo t z m -> m (t a)) -> Final m z a

data WeavingInfo t z m where
  Untransformed :: (forall x. z x -> m x) -> WeavingInfo Identity z m
  Transformed :: Traversal t
              -> (forall x. x -> t x)
              -> (forall x. t (z x) -> m (t x))
              -> (forall r x. Sem (Weave t r ': r) x -> Sem r (t x))
              -> WeavingInfo t z m

makeSem ''Final

mapWeavingInfo
  :: (forall x. n x -> m x) -> WeavingInfo t z n -> WeavingInfo t z m
mapWeavingInfo to = \case
  Untransformed n -> Untransformed (to . n)
  Transformed trav mkS wv lwr -> Transformed trav mkS (to . wv) lwr

-- | The 'Lowering' environment, which is a 'Polysemy.Sem' with a small
-- effect stack containing the @'Lower' m t n@ effect, which provides the
-- various @-S@ combinators, as well as @'Embed' m@ and @'Final' m@ effects,
-- allowing you to embed actions of the final monad into 'Lowering'.
--
-- The type parameters of 'Lowering' represent the following:
--
-- * @m@: The final monad, the @m@ in @'Final' m@.
-- * @t@: The type of final effectful state once /all/ interpreters -- past
--   and future -- have been run, and @'Polysemy.Sem'@ has been reduced to the
--   final monad.
-- * @n@: The type of the \"source monad\": the monad that can be lowered t
--   @m@. When 'withLoweringToFinal' is used, @n@ is @Sem r@.
--
-- @since 2.0.0.0
type Lowering m t n = Sem '[Lower m t n, Embed m, Final m]

data Lower m t n z a where
  LiftWithL :: forall m t n z a
             . ((forall x. Lowering m t n x -> m (t x)) -> m a)
            -> Lower m t n z a
  WithProcessorL :: forall m t n z a
                  . ((forall x. n x -> m (t x)) -> m a)
                 -> Lower m t n z a
  RestoreL  :: forall m t n z a. t a -> Lower m t n z a
  -- RunL      :: forall m t n z a. n a -> Lower m t n z a

-- | A singleton datatype parametrized with type parameters corresponding to
-- @HigherOrder@
data TypeParamsL
      (m :: Type -> Type)
      (t :: Type -> Type)
      (n :: Type -> Type) = TypeParamsL

-- | A trivial action just returning the 'TypeParamsL' singleton, with
-- type parameters matching that of the current 'Lowering' environment.
--
-- You can use this together with @ScopedTypeVariables@ to gain access to the
-- various parameters of the 'Lowering' if you need them.
getTypeParamsL :: forall m t n r
                . Sem (Lower m t n ': r) (TypeParamsL m t n)
getTypeParamsL = return TypeParamsL

-- | Embed a computation of the source monad into 'Lowering'.
--
-- @since 2.0.0.0
runL :: forall m t n r a. n a -> Sem (Lower m t n ': r) a
runL m = controlWithProcessorL $ \lwr -> lwr m

-- | Lift an computation of the final monad @m@ by giving it access to a
-- lowering function that can transform @'Lowering' m t n x@ to @m (t x)@.
--
-- This is analogous to @liftBaseWith@ of @MonadBaseControl@.
--
-- Note: the lowering function lowers @'Lowering' m t n@ by using the
-- effectful state as it is when 'liftWithL' is run.
--
-- @since 2.0.0.0
liftWithL :: forall m t n r a
           . ((forall x. Lowering m t n x -> m (t x)) -> m a)
          -> Sem (Lower m t n ': r) a
liftWithL main = send (LiftWithL main)

-- | A particularly useful composition:
-- @'controlL' h = 'liftWithL' h >>= 'restoreL'@
--
-- This is analogous to @control@ of @MonadBaseControl@.
--
-- Note: the lowering function lowers @'Lowering' m t n@ by using the
-- effectful state as it is when 'controlL' is run.
--
-- @since 2.0.0.0
controlL :: forall m t n r a
          . ((forall x. Lowering m t n x -> m (t x)) -> m (t a))
         -> Sem (Lower m t n ': r) a
controlL main = liftWithL main >>= restoreL

-- | Embed a computation of the source monad into 'Lowering', and reify
--   the effectful state of all purely interpreted effects (effects not
--   ultimately interpreted in terms of the final monad).
--
-- By reifying the effectful state, you may do one or more of the following:
--
-- * Guarantee that execution won't be interrupted by the failure of a purely
--   interpreted effect, since that failure will instead be reified into the
--   state.
-- * Check if the computation has failed because of a purely interpreted effect
--   by using 'Data.Foldable.null'
--   or @`Data.Traversable.traverse` (const Nothing)@.
-- * Discard any impact the computation has on purely interpreted effects by
--   never restoring the effectful state.
--
-- Once an effectful state has been reified, you may restore it using
-- 'restoreL'.
--
-- @since 2.0.0.0
runExposeL :: forall m t n r a. n a -> Sem (Lower m t n ': r) (t a)
runExposeL z = withProcessorL $ \lower -> lower z

-- | Restore a reified effectful state, bringing its changes into scope, and
-- returning the result of the computation.
--
-- This is analogous to @restoreM@ of @MonadBaseControl@.
--
-- /Note/: this overrides the local effectful state of any previously restored
-- effectful state.
--
-- For example, consider:
--
-- @
-- ta <- 'runExposeL' ma
-- tb <- 'runExposeL' mb
-- _  <- 'restoreL' ta
-- _  <- 'restoreL' tb
-- @
--
-- Unless @'restoreL' ta@ causes the handler to fail (because @ma@ failed due to
-- a local effect), the changes it brings into scope will be overridden by
-- @'restoreL' tb@.
--
-- If you want to integrate the results of both actions, you need to restore the
-- state in between uses of 'runExposeL', so that @'runExposeL' mb@ works with
-- the changes of @ta@ in scope.
-- @
-- ta <- 'runExposeH' ma
-- _  <- 'restoreL' ta
-- tb <- 'runExposeH' mb
-- _  <- 'restoreH' tb
-- @
--
-- @since 2.0.0.0
restoreL :: forall m t n r a. t a -> Sem (Lower m t n ': r) a
restoreL = send . RestoreL @m @_ @n

-- | Reify the effectful state of the purely interpreted effects used
--   used within the argument.
--
-- @'runExposeL' m = 'exposeL' ('runL' m)@
--
-- @since 2.0.0.0
exposeL :: forall m t n r a
         . Lowering m t n a
        -> Sem (Lower m t n ': r) (t a)
exposeL m = liftWithL $ \lower -> lower m

-- | Process a computation of the source monad by turning it into an computation
-- of the final monad returning a reified effectful state. The processed
-- computation is returned, rather than being immediately run like with 'runL'.
--
-- /Note/: The processed action makes use of the effectful state as it is by
-- the time 'processL' is run, rather than what it is by the time the processed
-- computation is run.
--
-- @since 2.0.0.0
processL :: forall m t n r a
          . Monad m
         => n a
         -> Sem (Lower m t n ': r) (m (t a))
processL z = withProcessorL $ \lower -> return (lower z)

-- | Lift an computation of the final monad by giving it access to a processor:
-- a function that transforms a computation of the source monad by turning it
-- into a computation of the final monad returning a reified effectful state.
--
-- 'withProcessorL' is a useful specialization of 'liftWithL':
--
-- @'withProcessorL' main = 'liftWithL' (\n -> main (n . 'runL'))@
--
-- /Note/: Processed actions makes use of the effectful state as it is by
-- the time 'withProcessorL' is run, rather than what it is by the time the
-- processed action is run.
--
-- @since 2.0.0.0
withProcessorL :: forall m t n r a
                . ((forall x. n x -> m (t x)) -> m a)
               -> Sem (Lower m t n ': r) a
withProcessorL main = send (WithProcessorL main)

-- | A particularly useful composition:
-- @'controlWithProcessorL' h = 'withProcessorL' h >>= 'restoreL'@
--
-- 'controlWithProcessorL' is a useful specialization of 'controlL':
--
-- @'controlWithProcessorL' main = 'controlL' (\n -> main (n . 'runL'))@
--
-- /Note/: Processed actions makes use of the effectful state as it is by
-- the time 'controlWithProcessorL' is run, rather than what it is by the time
-- the processed action is run.
--
-- @since 2.0.0.0
controlWithProcessorL :: forall m t n r a
                       . ((forall x. n x -> m (t x)) -> m (t a))
                      -> Sem (Lower m t n ': r) a
controlWithProcessorL main = withProcessorL main >>= restoreL

-- | Lift an computation of the final monad by giving it access to a function
-- that transforms any @'Sem' r@ computation into a compuation of the final
-- monad returning a reified effectful state. The computation of the final
-- monad must return a resulting effectful state.
--
-- The reified effectful state @t@ is 'Traversable', which gives you some
-- options -- see 'runExposeL'.
--
-- 'controlFinal' provides no means of sequentially combining effectful states.
-- If you need transform multiple @'Polysemy.Sem' r@ computations to the final
-- monad and sequentially execute them, then 'withLoweringToFinal' should be
-- used instead.
--
-- You are discouraged from using 'controlFinal' in application code,
-- as it ties your application code directly to the final monad.
--
-- @'controlFinal' main = 'withLoweringToFinal' ('controlWithProcessorL' main)@
--
-- @since 2.0.0.0
controlFinal :: forall m r a
              . (Member (Final m) r, Monad m)
             => (  forall t
                 . Traversable t
                => (forall x. Sem r x -> m (t x)) -> m (t a)
                )
             -> Sem r a
controlFinal main = withWeavingToFinal @m \case
  Untransformed n -> main (fmap Identity . n)
  Transformed trav mkS wv _ -> reify trav \(_ :: pr s) ->
    getViaTraversal <$> main (fmap (ViaTraversal @s) . wv . mkS)



runLowering :: forall m n a
             . Monad m
            => (forall t. Traversable t => Lowering m t n a)
            -> (forall t. WeavingInfo t n m -> m (t a))
runLowering lowering = \case
  Untransformed to ->
    let
      go :: forall x. Lowering m Identity n x -> m x
      go = usingSem return \(Union pr wav) c -> case pr of
        Here -> fromFOEff wav $ \ex -> \case
          RestoreL (Identity a) -> c (ex a)
          LiftWithL main' -> main' (fmap Identity . go) >>= c . ex
          WithProcessorL main' -> main' (fmap Identity . to) >>= c . ex
        There Here -> fromFOEff wav $ \ex (Embed m) -> m >>= c . ex
        There (There Here) -> case wav of
          Sent (WithWeavingToFinal main) to' ->
            main (Untransformed (go . to')) >>= c .# runIdentity
          Weaved (WithWeavingToFinal main) trav mkS wv lwr ex ->
            main (Transformed trav mkS (go . wv) lwr) >>= c . ex
        There (There (There pr')) -> absurdMembership pr'

    in
      go (Identity <$> lowering)
  Transformed (trav :: Traversal t) _ wv lwr0 -> reify trav \(_ :: pr s) ->
    let
      go :: forall x
          . Lowering m (ViaTraversal s t) n x
         -> Sem '[Weave t '[Embed m, Final m], Embed m, Final m] x
      go =
        reinterpret \case
          RestoreL (ViaTraversal t) -> sendUsing Here (RestoreW t)
          LiftWithL main ->
            sendUsing Here
              (LiftWithW (\lwr -> main (fmap ViaTraversal . runM . lwr . go)))
            >>= sendUsing Here . EmbedW . embed
          WithProcessorL main ->
            sendUsing Here
              (GetStateW (\mkS -> main (fmap ViaTraversal . wv . mkS)))
            >>= sendUsing Here . EmbedW . embed
        >>> intercept @(Embed m) (\(Embed e) ->
              sendUsing Here $ EmbedW $ embed e )
    in
      runM $ lwr0 $ go lowering

-- runLowering main nat =
--   let
--     go :: forall x. Lowering m (StT t) n x -> t m x
--     go = usingSem $ \(Union pr (Weaving eff mkT lwr ex)) -> do
--       let run_it = (ex . (<$ mkInitState lwr))
--       case pr of
--         Here -> run_it <$> case eff of
--           RestoreL t -> restoreT (return t)
--           RunL m -> nat m
--           LiftWithL main' -> liftWith $ \lower -> main' (lower . go)
--           WithProcessorL main' -> liftWith $ \lower -> main' (lower . nat)
--         There Here | Embed m <- eff -> run_it <$> lift m
--         There (There Here) | WithTransToFinal main' <- eff ->
--           fmap ex $ lwr $ getComposeT $ main' (ComposeT . mkT go)
--         There (There (There pr_)) -> case pr_ of {}
--   in
--     go main

-----------------------------------------------------------------------------
-- | Allows for embedding higher-order actions of the final monad
-- by providing the means of explicitly threading effects through @'Sem' r@
-- to the final monad. This is done through the use of the 'Lower'
-- environment, which provides a variety of combinators, most notably
-- 'controlL'.
--
-- You are discouraged from using 'withLoweringToFinal' in application code,
-- as it ties your application code directly to the final monad.
--
-- @since 2.0.0.0
withLoweringToFinal :: (Monad m, Member (Final m) r)
                     => (forall t. Traversable t => Lowering m t (Sem r) a)
                     -> Sem r a
withLoweringToFinal main = withWeavingToFinal (runLowering main)

------------------------------------------------------------------------------
-- | Lower a 'Sem' containing only a single lifted 'Monad' into that
-- monad.
runM :: Monad m => Sem '[Embed m, Final m] a -> m a
runM = usingSem return $ \u c -> case decomp u of
  Right wav -> fromFOEff wav $ \ex (Embed m) -> m >>= c . ex
  Left g -> case extract g of
    Sent (WithWeavingToFinal main) n ->
      main (Untransformed (runM . n)) >>= c .# runIdentity
    Weaved (WithWeavingToFinal main) trav mkS wv lwr ex ->
      main (Transformed trav mkS (runM . wv) lwr) >>= c . ex
{-# NOINLINE[3] runM #-}
{-# SPECIALIZE[~3] runM :: Sem '[Embed IO, Final IO] a -> IO a #-}
{-# SPECIALIZE[~3] runM :: Sem '[Embed Identity, Final Identity] a -> Identity a #-}


-----------------------------------------------------------------------------
-- | 'controlFinal' admits an implementation of 'embed'.
--
-- Just like 'embed', you are discouraged from using this in application code.
--
-- @since 1.2.0.0
embedFinal :: (Member (Final m) r, Functor m) => m a -> Sem r a
embedFinal m = withWeavingToFinal $ \case
  Untransformed _ -> Identity <$> m
  Transformed _ mkS _ _ -> mkS <$> m


------------------------------------------------------------------------------
-- | Like 'interpretH', but may be used to
-- interpret higher-order effects in terms of the final monad.
--
-- 'interpretFinal' requires less boilerplate than using 'interpretH'
-- together with 'withLoweringToFinal', but is also less powerful.
-- 'interpretFinal' does not provide any means of executing actions
-- of @'Sem' r@ as you interpret each action, and the provided interpreter
-- is automatically recursively used to process higher-order occurences of
-- @'Sem' (e ': r)@ to @'Sem' r@.
--
-- If you need greater control of how the effect is interpreted,
-- use 'interpretH' together with 'withLoweringToFinal' \/
-- 'controlFinal' instead.
--
-- /Note/: Effects that aren't interpreted in terms of the final
-- monad will have local state semantics in regards to effects
-- interpreted using 'interpretFinal'. See 'Final'.
--
-- @since 2.0.0.0
interpretFinal
    :: forall m e r a
     . (Member (Final m) r, Monad m)
    => (forall t z x. Traversable t => e z x -> Lowering m t z x)
       -- ^ A handler written using the 'Lowering' environment, where
       -- the source monad @z@ is the monad of the higher-order chunks in @e@.
    -> Sem (e ': r) a
    -> Sem r a
interpretFinal h =
  transform @(Final m) (\e -> WithWeavingToFinal (runLowering (h e)))

------------------------------------------------------------------------------
-- | Given natural transformations between @m1@ and @m2@, run a @'Final' m1@
-- effect by transforming it into a @'Final' m2@ effect.
--
-- @since 1.2.0.0
finalToFinal :: forall m2 m1 r a
              . (Monad m1, Monad m2, Member (Final m2) r)
             => (forall x. m1 x -> m2 x)
             -> (forall x. m2 x -> m1 x)
             -> Sem (Final m1 ': r) a
             -> Sem r a
finalToFinal to from = transform @(Final m2) $ \(WithWeavingToFinal main) ->
  WithWeavingToFinal (to . main . mapWeavingInfo from)

------------------------------------------------------------------------------
-- | Transform an @'Embed' m@ effect into a @'Final' m@ effect
--
-- @since 1.2.0.0
embedToFinal :: (Member (Final m) r, Functor m)
             => Sem (Embed m ': r) a
             -> Sem r a
embedToFinal = transform $ \(Embed m) -> WithWeavingToFinal $ \case
  Untransformed _ -> Identity <$> m
  Transformed _ mkS _ _ -> mkS <$> m
