{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}
{-# OPTIONS_HADDOCK not-home #-}

module Polysemy.Internal.HigherOrder where

import Data.Kind (Type)
import Data.Functor.Identity
import Control.Monad

import Polysemy.Internal
import Polysemy.Internal.CustomErrors (FirstOrder)
import Polysemy.Internal.Kind
import Polysemy.Internal.Union
import Polysemy.Internal.Utils
import Polysemy.Internal.Core
import Polysemy.Internal.Reflection

-- | A reified interpreter, transforming @'Polysemy.Sem' (e ': rH)@ to
-- @'Polysemy.Sem' rH@.
--
-- @since 2.0.0.0
newtype InterpreterH e rH = InterpreterH {
  unInterpreterH :: forall x. Sem (e ': rH) x -> Sem rH x
  }

-- | An effect providing various tools needed for higher-order interpreters,
-- most notably the ability to run higher-order chunks of the interpreted
-- effect. See 'interpretH' for a simple usage guide.
--
-- 'raise'ing actions to @'HigherOrder' ... : r@ in order to use them in
-- handlers is inefficient -- you should typically use 'embedH' instead.
-- If you want to avoid accidental usages of such 'raise's, you may be
-- interested in importing -- "Polysemy.HigherOrder.RewriteRule"
--
-- The type parameters represent the following:
--
-- * @z@: The monad of the higher-order thunks of the effect being interpreted.
-- * @t@: The type of effectful state of effects that have already been
--   interpreted (sometimes called local (effectful) state). @t@ is always
--   'Traversable', which can sometimes be useful (see the documentation of
--   'Polysemy.HigherOrder.runExposeH' for some examples.)
-- * @e@: The effect being handled
-- * @rH@: The effect stack the interpreter is working on
-- * @rC@: The effect stack which the `HigherOrder` effect can be lowered to.
--   Typically the same as 'rH'.
--
-- @since 2.0.0.0
data HigherOrder z t e rH rC :: Effect where
  GetProcessorH
    :: forall z t e rH rC m
     . HigherOrder z t e rH rC m (ProcessorH z t e rH)
  GetInterpreterH
    :: forall z t e rH rC m
     . HigherOrder z t e rH rC m (InterpreterH e rH)
  LiftWithH
    :: forall z t e rH rC m a
     . ((forall r x. Sem (HigherOrder z t e rH r ': r) x -> Sem r (t x))
        -> a)
    -> HigherOrder z t e rH rC m a
  RestoreH
    :: forall z t e rH rC m a. t a -> HigherOrder z t e rH rC m a
  EmbedH
    :: forall z t e rH rC m a. Sem rC a -> HigherOrder z t e rH rC m a
  GetStateH
    :: forall z t e rH rC m. HigherOrder z t e rH rC m (t ())
  PropagateH
    :: forall e q z t eH rH rC m a
     . ElemOf e rC
    -> e q a
    -> (forall x y. (x -> q y) -> t x -> Sem rC (t y))
    -> HigherOrder z t eH rH rC m a

-- | A proxy datatype parametrized with type parameters corresponding to
-- @HigherOrder@
data TypeParamsH
      (z :: Type -> Type)
      (t :: Type -> Type)
      (e :: Effect)
      (rH :: EffectRow)
      (rC :: EffectRow) = TypeParamsH

-- | A trivial action just returning the 'TypeParamsH' singleton, with
-- type parameters matching that of the current 'HigherOrder' environment.
--
-- You can use this together with @ScopedTypeVariables@ to gain access to the
-- various parameters of the 'HigherOrder' if you need them.
getTypeParamsH :: forall z t e rH rC r
                    . Sem (HigherOrder z t e rH rC ': r)
                          (TypeParamsH z t e rH rC)
getTypeParamsH = return TypeParamsH
{-# INLINE getTypeParamsH #-}

-- | Propagate an effect action where the higher-order chunks are of the same
-- monad @z@ as that used by the effect currently being handled.
--
-- This is useful for interpreters that want to rewrite and propagate actions.
-- For example, 'Polysemy.transform' can be written using this:
--
-- @
-- transform t = interpretH $ \e -> propagate (t e)
-- @
propagate :: forall e r z t eH rH rC a
           . (Member e rC, Raise rH rC)
          => e z a
          -> Sem (HigherOrder z t eH rH rC ': r) a
propagate = propagateUsing membership

-- | Propagate an effect action where the higher-order chunks are of the same
-- monad @z@ as that used by the effect currently being handled, given an
-- explicit proof that the effect exists in the effect stack.
propagateUsing :: forall e r z t eH rH rC a
                . Raise rH rC
               => ElemOf e rC
               -> e z a
               -> Sem (HigherOrder z t eH rH rC ': r) a
propagateUsing pr e = do
  InterpreterH interp <- getInterpreterH
  ProcessorH prcs   <- getProcessorH
  sendUsing Here $ PropagateH pr e (\ex t -> raise_ $ interp $ prcs t ex)


-- | Embed a @'Sem' rC@ action, where @rC@ is the effect row that
-- @'HigherOrder' ... ': r@ will eventually be lowered to. For most usage
-- @rC@ is the same as @r@.
--
-- This is /significantly/ more efficient compared to 'raise'ing the action
-- to fit the signature of @'Sem' ('HigherOrder' ... ': r)@, and should
-- preferred whenever possible. 'embedH' does, however, have a semantic
-- difference compared to 'raise'ing: it is not possible to 'intercept' effects
-- of an action embedded using 'embedH' unless that action is lowered again
-- so that the 'HigherOrder' effect isn't present, which is possible with
-- 'controlH' or 'liftWithH'.
--
-- Most `HigherOrder` operators exported from "Polysemy.HigherOrder" are
-- implemented using 'embedH', while corresponding operators exported from
-- "Polysemy.HigherOrder.Flexible" are implemented by raising. This means
-- that the combinators of "Polysemy.HigherOrder" are more efficient, while
-- the combinators of "Polysemy.HigherOrder.Flexible" are more flexible, and
-- can sometimes be significantly easier to use.
embedH :: forall r z t eH rH rC a
        . Sem rC a -> Sem (HigherOrder z t eH rH rC ': r) a
embedH = sendUsing Here . EmbedH

-- | Run a monadic action given by a higher-order effect that is currently
-- being interpreted, and recursively apply the current interpreter on it.
--
-- This is the standard tool for interpreting higher-order effects. It is
-- the simplest -- and most commonly useful -- way to process higher-order
-- chunks of effects.
--
-- Don't be intimidated by the signature; it looks the way it is to allow
-- 'runH' to be used in as many contexts as possible, without requiring
-- any type applications to get it to work.
--
-- Typically, you have:
--
-- @
-- 'runH' :: z a -> 'Polysemy.Sem' ('Polysemy.HigherOrder' z t e r r ': r) a
-- @
--
-- @since 2.0.0.0
runH :: forall r z t e rH rC a
      . Raise rH rC
     => z a
     -> Sem (HigherOrder z t e rH rC ': r) a
runH = runExposeH >=> restoreH

-- | Run a monadic action given by a higher-order effect that is currently
-- being interpreted, and apply an interpreter for the interpreted effect
-- on it. This is useful if you want to apply a different interpreter than
-- the one you're currently defining.
--
-- The signature of 'runH'' can often make it difficult to use. If you run into
-- issues, you can try using 'runExposeH'', and manually restore the returned
-- effectful state using 'restoreH'. You can also use the alternate
-- 'Polysemy.HigherOrder.Flexible.runH'' provided by
-- "Polysemy.HigherOrder.Flexible", which has a much easier to use signature --
-- but bear in mind that this may degrade performance; see the documentation for
-- "Polysemy.HigherOrder" module.
--
-- @since 2.0.0.0
runH' :: forall r z t e rH rC a b
       . (Sem (e ': rH) (t a) -> Sem rC (t b))
      -> z a -> Sem (HigherOrder z t e rH rC ': r) b
runH' interp = runExposeH' interp >=> restoreH

-- | Locally gain access to lowering function that can transform
-- @'Polysemy.Sem' ('Polysemy.Interpretation.HigherOrder' z t ... ': r) x@ to
-- @'Polysemy.Sem' r (t x)@.
--
-- This is analogous to @liftWith@ of @MonadTransControl@.
--
-- Note: the lowering function lowers @'Sem' ('HigherOrder' ... ': r)@ by using
-- the effectful state as it is when 'liftWithH' is run.
liftWithH :: forall r z t e rH rC a
           . (   (   forall r' x
                   . Sem (HigherOrder z t e rH r' ': r') x
                  -> Sem r' (t x))
              -> Sem rC a)
          -> Sem (HigherOrder z t e rH rC ': r) a
liftWithH main = sendUsing Here (LiftWithH main) >>= embedH

-- | A particularly useful composition:
-- @'controlH' h = 'liftWithH' h >>= 'restoreH'@
--
-- This is analogous to @controlT@ of @MonadTransControl@.
--
-- Note: the lowering function lowers @'Sem' ('HigherOrder' ... ': r)@ by using the
-- effectful state as it is when 'controlH' is run.
controlH :: forall r z t e rH rC a
          . (   (   forall rC' x
                  . Sem (HigherOrder z t e rH rC' ': rC') x
                 -> Sem rC' (t x))
             -> Sem rC (t a))
         -> Sem (HigherOrder z t e rH rC ': r) a
controlH main = liftWithH main >>= restoreH

-- | Run a monadic action given by a higher-order effect that is currently
-- being interpreted, recursively apply the current interpreter on it,
-- and reify the effectful state of all local effects
-- as part of the result.
--
-- By reifying the effectful state, you may do one or more of the following:
--
-- * Guarantee that the handler won't be interrupted by a local effect failing,
--   since that failure will instead be reified into the state.
-- * Check if the action run has failed because of a local effect by using
--   'Data.Foldable.null' or @`Data.Traversable.traverse` (const Nothing)@.
-- * Discard any impact the monadic action has on local effects by never
--   restoring the efectful state.
--
-- Once an effectful state has been reified, you may restore it using
-- 'restoreH'.
--
-- @since TODO
runExposeH :: forall r z t e rH rC a
            . Raise rH rC
           => z a -> Sem (HigherOrder z t e rH rC ': r) (t a)
runExposeH z = do
  InterpreterH interp <- getInterpreterH
  runExposeH' (raise_ . interp) z

-- | Run a monadic action given by a higher-order effect that is currently
-- being interpreted, and reify the effectful state of all local effects
-- as part of the result.
--
-- See 'runExposeH' for more information.
--
-- Unlike 'runExposeH', this doesn't recursively apply the current interpreter
-- to the monadic action -- allowing you to run a different interpreter
-- on it instead.
--
-- @since TODO
runExposeH' :: forall r z t e rH rC a b
             . (Sem (e ': rH) (t a) -> Sem rC b)
            -> z a
            -> Sem (HigherOrder z t e rH rC ': r) b
runExposeH' interp = processH >=> embedH . interp

-- | Restore a reified effectful state, bringing its changes into scope, and
-- returning the result of the computation.
--
-- This is analogous to @restoreT . return@ of @MonadTransControl@ or
-- @restoreM@ of @MonadBaseControl@.
--
-- /Note/: this overrides the local effectful state of any previously restored
-- effectful state.
--
-- For example, consider:
--
-- @
-- ta <- 'runExposeH' ma
-- tb <- 'runExposeH' mb
-- 'restoreH' ta
-- 'restoreH' tb
-- @
-- Unless @'restoreH' ta@ causes the handler to fail (because @ma@ failed due to
-- a local effect), the changes it brings into scope will be overridden by
-- @'restoreH' tb@.
--
-- If you want to integrate the results of both actions, you need to restore the
-- state in between uses of 'runExposeH', so that @'runExposeH' mb@ works with
-- the changes of @ta@ in scope.
-- @
-- ta <- 'runExposeH' ma
-- 'restoreH' ta
-- tb <- 'runExposeH' mb
-- 'restoreH' tb
-- @
--
-- @since TODO
restoreH :: forall r z t e rH rC a
          . t a -> Sem (HigherOrder z t e rH rC ': r) a
restoreH = sendUsing Here . RestoreH

-- | Reify the effectful state of the local effects of the argument.
--
-- @'runExposeH' m = 'exposeH' ('runH' m)@
--
-- @since TODO
exposeH :: forall z t e rH rC a
         . Sem (HigherOrder z t e rH rC ': rC) a
        -> Sem (HigherOrder z t e rH rC ': rC) (t a)
exposeH m = liftWithH $ \lower -> lower m

-- | Get the local effectful state as it is currently.
--
-- @since TODO
getStateH :: forall r z t e rH rC
           . Sem (HigherOrder z t e rH rC ': r) (t ())
getStateH = sendUsing Here GetStateH

-- | Process a monadic action given by the higher-order effect that is currently
-- being interpreted by turning it into a @'Sem' (e ': rH)@ action that
-- returns a reified effectful state. The processed monadic action is returned,
-- rather than being immediately run like with 'runH''.
--
-- /Note/: The processed action makes use of the effectful state as it is by
-- the time 'processH' is run, rather than what it is by the time the processed
-- action is run.
processH :: forall r z t e rH rC a
          . z a
         -> Sem (HigherOrder z t e rH rC ': r) (Sem (e ': rH) (t a))
processH z = do
  s <- getStateH
  ProcessorH prcs <- getProcessorH
  return $ prcs s (\_ -> z)

-- | Locally gain access to a processor: a function that transforms a monadic
-- action given by the higher-order effect that is currently being interpreted
-- by turning it into a @'Sem' (e ': rH)@ action that returns a reified
-- effectful state.
--
-- /Note/: Processed actions make use of the effectful state as it is by
-- the time 'withProcessorH' is run, rather than what it is by the time the
-- processed action is run.
withProcessorH :: forall r z t e rH rC a
                . ((forall x. z x -> Sem (e ': rH) (t x))
                   -> Sem rC a)
               -> Sem (HigherOrder z t e rH rC ': r) a
withProcessorH main = do
  s <- getStateH
  ProcessorH prcs <- getProcessorH
  embedH $ main (\z -> prcs s (\_ -> z))

-- | A particularly useful composition:
-- @'controlWithProcessorH' h = 'withProcessorH' h >>= 'restoreH'@
--
-- /Note/: Processed actions make use of the effectful state as it is by
-- the time 'withProcessorH' is run, rather than what it is by the time the
-- processed action is run.
controlWithProcessorH :: forall r z t e rH rC a
                       . ((forall x. z x -> Sem (e ': rH) (t x))
                          -> Sem rC (t a))
                      -> Sem (HigherOrder z t e rH rC ': r) a
controlWithProcessorH main = withProcessorH main >>= restoreH

-- | Retrieve a 'InterpreterH': the interpreter currently being defined
getInterpreterH :: forall z t e rH rC r
                 . Sem (HigherOrder z t e rH rC ': r)
                       (InterpreterH e rH)
getInterpreterH = sendUsing Here GetInterpreterH


newtype ProcessorH z t e r =
  ProcessorH (forall x y. t x -> (x -> z y) -> Sem (e ': r) (t y))

-- | Retrieve a 'ProcessorH': a function that transforms a monadic action
-- given by the higher-order effect that is currently being interpreted by
-- turning it into a @'Sem' (e ': rH)@ action that returns a reified
-- effectful state.
--
-- Unlike 'withProcessorH' and 'controlWithProcessorH', the processor returned
-- by this takes the effectful state it should operate with, rather than using
-- the effectful state as it is at the call to 'getProcessorH'.
-- The way it takes the effectful state is by receiving the monadic action
-- by having it wrapped into the effectful state.
--
-- Example (trivial) usage:
--
-- @
-- ProcessorH prcs <- getProcessorH
-- s <- getStateH
-- let processed_action = prcs s (const z)
-- @
getProcessorH :: Sem (HigherOrder z t e rH rC ': r) (ProcessorH z t e rH)
getProcessorH = sendUsing Here GetProcessorH

-- | A handler for a higher-order effect @e@, working with the effect stack
-- @rH@.
type EffHandlerH e rH =
       forall t z x
     . Traversable t
    => e z x -> Sem (HigherOrder z t e rH rH ': rH) x

------------------------------------------------------------------------------
-- | Like 'interpret', but for higher-order effects (i.e. those which make use
-- of the @m@ parameter.)
--
-- Higher-order actions within the effect to be interpreted can be run using
-- 'runH' or 'runH''. For example:
--
-- @
-- data Bind m a where
--   Bind :: m a -> (a -> m b) -> Bind m b
--
-- runBind :: Sem (Bind ': r) a -> Sem r a
-- runBind = 'interpretH' \\case
--   Bind ma f -> do
--     a <- 'runH' ma
--     b <- 'runH' (f a)
--     return b
-- @
--
-- 'interpretH' has a large suite of associated operators besides 'runH' and
-- 'runH'', which can be accessed through the "Polysemy.HigherOrder" module.
-- These operators are power tools only meant to be used for complex
-- interpretations of higher-order effects; 'runH' and 'runH'' are sufficient
-- for most uses of 'interpretH'.
--
-- @since TODO
interpretH :: forall e r
            . EffHandlerH e r
           -> InterpreterFor e r
interpretH h = go
  where
    go :: forall a'. Sem (e ': r) a' -> Sem r a'
    go (Sem sem) = Sem $ \k -> sem $ \u c -> case decomp u of
      Left g -> k (hoist go g) c
      Right (Sent (e :: e z y) n) ->
        let
          goSent :: forall rC x
                  . Sem (HigherOrder z Identity e r rC ': rC) x
                 -> Sem rC x
          goSent (Sem m) = Sem $ \k' -> m $ \u' c' -> case decomp u' of
            Left g -> k' (hoist goSent_ g) c'
            Right wav -> fromFOEff wav $ \ex' -> \case
              GetInterpreterH -> c' $ ex' $ InterpreterH go
              GetProcessorH -> c' $ ex' $
                ProcessorH (\(Identity t) fz -> (fmap Identity #. n . fz) t)
              RestoreH (Identity a) -> c' $ ex' a
              LiftWithH main -> c' $ ex' $ main $ fmap Identity #. goSent_
              EmbedH m' -> runSem m' k' (c' . ex')
              GetStateH -> c' $ ex' $ Identity ()
              PropagateH pr e' n' ->
                k' (Union pr (Sent e' (fmap runIdentity #. n' id .# Identity)))
                   (c' . ex')
          {-# INLINE goSent #-}

          goSent_ :: forall rC x
                . Sem (HigherOrder z Identity e r rC ': rC) x
               -> Sem rC x
          goSent_ = goSent
          {-# NOINLINE goSent_ #-}
        in
          runSem (goSent (h e)) k c
      Right (Weaved (e :: e z y) (trav :: Traversal t) _ wv lwr ex) ->
        reify trav $ \(_ :: pr s) ->
          let
            goWeaved :: forall rC x
                      . Sem (HigherOrder z (ViaTraversal s t) e r rC ': rC) x
                     -> Sem (Weave t rC ': rC) x
            goWeaved (Sem m) = Sem $ \k' -> m $ \u' c' ->
              case decompCoerce u' of
                Left g -> k' (hoist goWeaved_ g) c'
                Right wav -> fromFOEff wav $ \ex' -> \case
                  GetInterpreterH -> c' $ ex' $ InterpreterH go
                  GetProcessorH ->
                      c' $ ex' $ ProcessorH $ \t fz ->
                        (fmap ViaTraversal #. wv .# getViaTraversal) (fmap fz t)
                  RestoreH (ViaTraversal t) ->
                    k' (injUsing Here (RestoreW t)) (c' . ex')
                  LiftWithH main ->
                    (`k'` c') $ injUsing Here $ LiftWithW $ \lwr' ->
                      ex' $ main $ (fmap ViaTraversal #. lwr' . goWeaved_)
                  EmbedH m' -> k' (injUsing Here $ EmbedW m') (c' . ex')
                  GetStateH ->
                    k' (injUsing Here (GetStateW (\w -> ViaTraversal (w ()))))
                       (c' . ex')
                  PropagateH pr e' n ->
                    (`k'` id) $ injUsing Here $ GetStateW $ \mkS' ->
                    (`k'` id) $ injUsing Here $ LiftWithW $ \lwr' ->
                    k' (injUsing Here (
                           EmbedW $ liftSem $ Union pr
                           $ Weaved e' trav mkS'
                              (fmap getViaTraversal #. n id .# ViaTraversal)
                              lwr'
                              id)) $ \ta ->
                    k' (injUsing Here $ RestoreW ta) (c' . ex')
            {-# INLINE goWeaved #-}

            goWeaved_ :: forall rC x
                       . Sem (HigherOrder z (ViaTraversal s t) e r rC ': rC) x
                      -> Sem (Weave t rC ': rC) x
            goWeaved_ = goWeaved
            {-# NOINLINE goWeaved_ #-}
          in
            runSem (lwr (goWeaved (h e))) k (c . ex)

------------------------------------------------------------------------------
-- | A generalization of 'interpretH', 'reinterpretH', 'reinterpret2H', etc.:
-- given an explicit membership transformation from @r@ to @r'@ and a
-- handler @h@ for a (higher-order) effect @e@, @'genericInterpretH' h@
-- gives an interpreter @Sem (e ': r)@ to @Sem r'@.
--
-- The most commonly useful membership transformation to use with
-- 'genericInterpretH' is 'Polysemy.Membership.subsumeMembership'
--
-- @since TODO
genericInterpretH :: forall e r' r a
                  . (forall e'. ElemOf e' r -> ElemOf e' r')
                 -> EffHandlerH e r'
                 -> Sem (e ': r) a
                 -> Sem r' a
genericInterpretH tPr h = interpretH h . mapMembership \case
  Here -> Here
  There pr -> There (tPr pr)
{-# INLINE genericInterpretH #-}

------------------------------------------------------------------------------
-- | The simplest way to produce an effect handler. Interprets an effect @e@ by
-- transforming it into other effects inside of @r@.
--
-- @since TODO
interpret :: forall e r
           . FirstOrder e "interpret"
          => (∀ z x. e z x -> Sem r x)
          -> InterpreterFor e r
interpret = baseInterpret
{-# INLINE interpret #-}

------------------------------------------------------------------------------
-- | Like 'reinterpret', but for higher-order effects. See 'interpretH' for a
-- simple usage guide.
--
-- @since 2.0.0.0
reinterpretH :: forall e1 e2 r a
                . EffHandlerH e1 (e2 ': r)
               -> Sem (e1 ': r) a
               -> Sem (e2 ': r) a
reinterpretH = genericInterpretH There
{-# INLINE reinterpretH #-}

------------------------------------------------------------------------------
-- | Like 'interpret', but instead of removing the effect @e@, reencodes it in
-- some new effect @f@. This function will fuse when followed by
-- 'Polysemy.State.runState', meaning it's free to 'reinterpret' in terms of
-- the 'Polysemy.State.State' effect and immediately run it.
--
-- @since 0.1.0.0
reinterpret :: forall e1 e2 r a
              . FirstOrder e1 "reinterpret"
             => (∀ z x. e1 z x -> Sem (e2 ': r) x)
             -> Sem (e1 ': r) a
             -> Sem (e2 ': r) a
reinterpret h = baseInterpret h . raiseUnder
{-# INLINE[2] reinterpret #-} -- rewrite rule

------------------------------------------------------------------------------
-- | Like 'reinterpret2', but for higher-order effects. See 'interpretH' for a
-- simple usage guide.
--
-- @since 2.0.0.0
reinterpret2H :: forall e1 e2 e3 r a
                 . EffHandlerH e1 (e2 ': e3 ': r)
                -> Sem (e1 ': r) a
                -> Sem (e2 ': e3 ': r) a
reinterpret2H = genericInterpretH (There . There)
{-# INLINE reinterpret2H #-} -- genericInterpretH uses mapMembership

------------------------------------------------------------------------------
-- | Like 'reinterpret', but introduces /two/ intermediary effects.
--
-- @since 0.1.0.0
reinterpret2 :: forall e1 e2 e3 r a
              . FirstOrder e1 "reinterpret2"
             => (∀ z x. e1 z x -> Sem (e2 ': e3 ': r) x)
             -> Sem (e1 ': r) a
             -> Sem (e2 ': e3 ': r) a
reinterpret2 h = baseInterpret h . raise2Under
{-# INLINE[2] reinterpret2 #-} -- rewrite rule

------------------------------------------------------------------------------
-- | Like 'reinterpret3', but for higher-order effects. See 'interpretH' for a
-- simple usage guide.
--
-- @since TODO
reinterpret3H :: forall e1 e2 e3 e4 r a
                 . EffHandlerH e1 (e2 ': e3 ': e4 ': r)
                -> Sem (e1 ': r) a
                -> Sem (e2 ': e3 ': e4 ': r) a
reinterpret3H = genericInterpretH (There . There . There)
{-# INLINE reinterpret3H #-} -- genericInterpretH uses mapMembership

------------------------------------------------------------------------------
-- | Like 'reinterpret', but introduces /three/ intermediary effects.
--
-- @since TODO
reinterpret3 :: forall e1 e2 e3 e4 r a
              . FirstOrder e1 "reinterpret3"
             => (∀ z x. e1 z x -> Sem (e2 ': e3 ': e4 ': r) x)
             -> Sem (e1 ': r) a
             -> Sem (e2 ': e3 ': e4 ': r) a
reinterpret3 h = baseInterpret h . raise3Under
{-# INLINE[2] reinterpret3 #-} -- rewrite rule

------------------------------------------------------------------------------
-- | Like 'interpret', but instead of handling the effect, allows responding to
-- the effect while leaving it unhandled. This allows you, for example, to
-- intercept other effects and insert logic around them.
--
-- See 'interpretH' for a simple usage guide.
--
-- @since 2.0.0.0
intercept :: forall e r a
           . FirstOrder e "intercept"
          => Member e r
          => (∀ z x. e z x -> Sem r x)
          -> Sem r a
          -> Sem r a
intercept h = baseInterpret h . expose
{-# INLINE intercept #-} -- expose uses mapMembership

------------------------------------------------------------------------------
-- | Like 'intercept', but for higher-order effects.
--
-- @since TODO
interceptH :: forall e r a
              . Member e r
             => EffHandlerH e r
             -> Sem r a
             -> Sem r a
interceptH h = interpretH h . expose
{-# INLINE interceptH #-} -- expose uses mapMembership

------------------------------------------------------------------------------
-- | Like 'interceptUsing', but for higher-order effects.
--
-- @since TODO
interceptUsingH :: forall e r a
                 . ElemOf e r
                -> EffHandlerH e r
                -> Sem r a
                -> Sem r a
interceptUsingH pr h = interpretH h . exposeUsing pr
{-# INLINE interceptUsingH #-} -- exposeUsing uses mapMembership

------------------------------------------------------------------------------
-- | A variant of 'intercept' that accepts an explicit proof that the effect
-- is in the effect stack rather then requiring a 'Member' constraint.
--
-- This is useful in conjunction with 'Polysemy.Membership.tryMembership'
-- in order to conditionally perform 'intercept'.
--
-- @since TODO
interceptUsing :: forall e r a .
                  FirstOrder e "interceptUsing"
               => Member e r
               => ElemOf e r
               -> (∀ z x. e z x -> Sem r x)
               -> Sem r a
               -> Sem r a
interceptUsing pr h = baseInterpret h . exposeUsing pr
{-# INLINE interceptUsing #-} -- exposeUsing uses mapMembership

baseInterpret :: (∀ z x. e z x -> Sem r x) -> InterpreterFor e r
baseInterpret = interpretFast
{-# INLINE baseInterpret #-}
