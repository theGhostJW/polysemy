{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_HADDOCK not-home #-}
module Polysemy.Internal.Interpretation where

import Control.Monad

import Polysemy.Internal
import Polysemy.Internal.CustomErrors (FirstOrder)
import Polysemy.Internal.Kind
import Polysemy.Internal.Union

newtype ProcessorH z t e r = ProcessorH { unProcessorH :: forall x. z x -> Sem (e ': r) (t x) }
newtype InterpreterH e r r' = InterpreterH { unInterpreterH :: forall x. Sem (e ': r) x -> Sem r' x }

-- | An effect for running monadic actions within a higher-order effect
-- currently being interpreted.
data Handling z t e r r' :: Effect where
  WithProcessorH
    :: forall z t e r r' m a
     . ((forall x. z x -> Sem (e ': r) (t x)) -> a)
    -> Handling z t e r r' m a
  WithInterpreterH
    :: forall z t e r r' m a
     . ((forall x. Sem (e ': r) x -> Sem r' x) -> a)
    -> Handling z t e r r' m a
  LiftWithH
    :: forall z t e r r' r'' m a
     . ((forall x. Sem (Handling z t e r r' ': r'') x -> Sem r'' (t x)) -> a)
    -> Handling z t e r r' m a
  RestoreH
    :: forall z t e r r' m a . t a -> Handling z t e r r' m a

propagate :: forall e r z t e' r' r'' a
           . (Member e r, Subsume r'' r)
          => e z a
          -> Sem (Handling z t e' r' r'' ': r) a
propagate = propagateUsing membership
{-# INLINE propagate #-}

propagateUsing :: forall e r z t e' r' r'' a
                . Subsume r'' r
               => ElemOf e r
               -> e z a
               -> Sem (Handling z t e' r' r'' ': r) a
propagateUsing pr = sendViaUsing (There pr) runH
{-# INLINE propagateUsing #-}

-- | Run a monadic action given by a higher-order effect that is currently
-- being interpreted, and recursively apply the current interpreter on it.
--
-- This is the standard tool for interpreting higher-order effects.
--
-- @since TODO
runH :: forall z t e r r' r'' a
      . Subsume r' r''
     => z a
     -> Sem (Handling z t e r r' ': r'') a
runH = runExposeH >=> restoreH
{-# INLINE runH #-}

liftWithH :: forall z t e r r' r'' r''' a
           . (   (forall x. Sem (Handling z t e r r' ': r'') x -> Sem r'' (t x))
              -> Sem r''' a)
          -> Sem (Handling z t e r r' ': r''') a
liftWithH main = sendUsing Here (LiftWithH main) >>= raise
{-# INLINE liftWithH #-}

controlH :: forall z t e r r' r'' r''' a
          . (   (forall x. Sem (Handling z t e r r' ': r'') x -> Sem r'' (t x))
             -> Sem r''' (t a)
            )
         -> Sem (Handling z t e r r' ': r''') a
controlH main = liftWithH main >>= restoreH
{-# INLINE controlH #-}

-- | Run a monadic action given by a higher-order effect that is currently
-- being interpreted.
--
-- Unlike 'runH', this doesn't recursively apply the current interpreter
-- to the monadic action -- allowing you to run a different interpreter
-- on it instead.
--
-- @since TODO
runH' :: forall z t e r r' r'' a
       . Subsume r r''
      => z a
      -> Sem (e ': Handling z t e r r' ': r'') a
runH' z = runExposeH' z >>= raise . restoreH
{-# INLINE runH' #-}

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
-- Once an effectful state has been reified, you may restore it using 'restoreH'.
--
-- @since TODO
runExposeH :: forall z t e r r' r'' a
            . Subsume r' r''
           => z a -> Sem (Handling z t e r r' ': r'') (t a)
runExposeH z = do
  ProcessorH prcs <- getProcessorH
  InterpreterH interp <- getInterpreterH
  raise $ subsume_ $ interp $ prcs z
{-# INLINE runExposeH #-}

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
runExposeH' :: forall z t e r r' r'' a
             . Subsume r r''
            => z a
            -> Sem (e ': Handling z t e r r' ': r'') (t a)
runExposeH' z = do
  ProcessorH prcs <- raise getProcessorH
  subsume_ $ prcs z
{-# INLINE runExposeH' #-}



-- | Restore a reified effectful state, bringing its changes into scope, and
-- returning the result of the computation.
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
restoreH :: forall z t e r r' r'' a. t a -> Sem (Handling z t e r r' ': r'') a
restoreH = sendUsing Here . RestoreH
{-# INLINE restoreH #-}

-- | Reify the effectful state of the local effects of the argument.
--
-- @'runExposeH' m = 'exposeH' ('runH' m)@
--
-- /Note/: `polysemy-plugin` is heavily recommended when using this function
-- to avoid ambiguous types. If `polysemy-plugin` isn't available, consider
-- using 'runExposeH' and `runExposeH'` instead.
--
-- @since TODO
exposeH :: forall z t e r r' r'' a
         . Sem (Handling z t e r r' ': r'') a
        -> Sem (Handling z t e r r' ': r'') (t a)
exposeH m = liftWithH $ \lower -> lower m
{-# INLINE exposeH #-}

-- | Retrieve a 'Processor': a function which can be used to process a monadic
-- action given by a higher-order effect that is currently being interpreted
-- without immediately running it, turning it into a @'Sem' (e ': r)@ action
-- that returns a reified effectful state.
getProcessorH :: forall z t e r r' r''
               . Sem (Handling z t e r r' ': r'') (ProcessorH z t e r)
getProcessorH = sendUsing Here (WithProcessorH ProcessorH)
{-# INLINE getProcessorH #-}

getInterpreterH :: forall z t e r r' r''
               . Sem (Handling z t e r r' ': r'') (InterpreterH e r r')
getInterpreterH = sendUsing Here (WithInterpreterH InterpreterH)
{-# INLINE getInterpreterH #-}

type Tactical z e r r' a =
      forall t
    . Traversable t
  => Sem (Handling z t e r r' ': r') a

type EffHandlerH e r r' =
     forall z x. e z x -> Tactical z e r r' x

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
-- 'runH'', which can be accessed through the "Polysemy.Tactical" module. These
-- operators are power tools only meant to be used for complex interpretations
-- of higher-order effects; 'runH' and 'runH'' are sufficient for most uses of
-- 'interpretH'.
--
-- @since TODO
interpretH :: forall e r a
              . EffHandlerH e r r
             -> Sem (e ': r) a
             -> Sem r a
interpretH = interpretGenericH
  -- Sem $ \(k :: forall x. Union r (Sem r) x -> m x) ->
  -- sem $ \u -> case decomp u of
  --   Left g -> k $ hoist (interpretH h) g
  --   Right (Weaving e
  --                (mkT :: forall n x
  --                      . Monad n
  --                     => (forall y. Sem (e ': r) y -> n y)
  --                     -> z x -> t n x
  --                )
  --                lwr
  --                ex
  --         ) ->
  --     let
  --         {-# SPECIALIZE INLINE
  --             commonHandler :: forall n x
  --                            . Weaving (Handling z (StT t) e r) n x
  --                           -> t m x #-}
  --         {-# SPECIALIZE INLINE
  --             commonHandler :: forall r' n x
  --                            . Weaving (Handling z (StT t) e r) n x
  --                           -> t (Sem r') x #-}
  --         commonHandler :: forall n b x
  --                        . Monad b => Weaving (Handling z (StT t) e r) n x -> t b x
  --         commonHandler (Weaving eff _ lwr' ex') = do
  --           let run_it = fmap (ex' . (<$ mkInitState lwr'))
  --           case eff of
  --             WithInterpreterH main -> run_it $ return $ main $ interpretH h
  --             WithProcessorH main -> run_it $
  --               liftWith $ \lower -> return $ main (lower . mkT id)
  --             RestoreH t -> run_it $
  --               restoreT (return t)
  --             LiftWithH main -> run_it $ liftWith $ \lower ->
  --               return $ main (lower . go3)

  --         go1 :: forall x. Sem (Handling z (StT t) e r ': r) x -> t m x
  --         go1 = usingSem $ \u' -> case decomp u' of
  --           Left g -> liftHandlerWithNat go2 k g
  --           Right wav -> commonHandler wav
  --         {-# INLINE go1 #-}

  --         go2 :: forall x. Sem (Handling z (StT t) e r ': r) x -> t (Sem r) x
  --         go2 = usingSem $ \u' -> case decomp u' of
  --           Left g -> liftHandlerWithNat go2 liftSem g
  --           Right wav -> commonHandler wav
  --         {-# NOINLINE go2 #-}

  --         go3 :: forall r'' x
  --              . Sem (Handling z (StT t) e r r' ': r'') x
  --             -> t (Sem r'') x
  --         go3 subInterpret = usingSem $ \u' -> case decomp u' of
  --           Left g -> liftHandlerWithNat (go3 subInterpret) liftSem g
  --           Right wav -> commonHandler wav
  --         {-# NOINLINE go3 #-}
  --     in
  --       fmap ex $ lwr $ go1 (h e)
{-# INLINE interpretH #-}

interpretGenericH :: forall e r' r a
                  . Subsume r r'
                 => EffHandlerH e r r'
                 -> Sem (e ': r) a
                 -> Sem r' a
interpretGenericH h = go
  where
    go :: forall a'. Sem (e ': r) a' -> Sem r' a'
    go (Sem sem) = Sem $ \(k :: forall x. Union r' (Sem r') x -> m x) ->
      sem $ \u -> case decomp u of
        Left g -> k $ subsumeUnion @r @r' $ hoist go g
        Right (Weaving e
                     (mkT :: forall n x
                           . Monad n
                          => (forall y. Sem (e ': r) y -> n y)
                          -> z x -> t n x
                     )
                     lwr
                     ex
              ) ->
          let
              {-# SPECIALIZE INLINE
                  commonHandler :: forall n x
                                 . Weaving (Handling z (StT t) e r r') n x
                                -> t m x #-}
              {-# SPECIALIZE INLINE
                  commonHandler :: forall r'' n x
                                 . Weaving (Handling z (StT t) e r r') n x
                                -> t (Sem r'') x #-}
              commonHandler :: forall n b x
                             . Monad b
                            => Weaving (Handling z (StT t) e r r') n x -> t b x
              commonHandler (Weaving eff _ lwr' ex') = do
                let run_it = fmap (ex' . (<$ mkInitState lwr'))
                case eff of
                  WithInterpreterH main -> run_it $ return $ main $ go
                  WithProcessorH main -> run_it $
                    liftWith $ \lower -> return $ main (lower . mkT id)
                  RestoreH t -> run_it $
                    restoreT (return t)
                  LiftWithH main -> run_it $ liftWith $ \lower ->
                    return $ main (lower . go3)

              go1 :: forall x. Sem (Handling z (StT t) e r r' ': r') x -> t m x
              go1 = usingSem $ \u' -> case decomp u' of
                Left g -> liftHandlerWithNat go2 k g
                Right wav -> commonHandler wav
              {-# INLINE go1 #-}

              go2 :: forall x
                   . Sem (Handling z (StT t) e r r' ': r') x -> t (Sem r') x
              go2 = usingSem $ \u' -> case decomp u' of
                Left g -> liftHandlerWithNat go2 liftSem g
                Right wav -> commonHandler wav
              {-# NOINLINE go2 #-}

              go3 :: forall r'' x
                   . Sem (Handling z (StT t) e r r' ': r'') x
                  -> t (Sem r'') x
              go3 = usingSem $ \u' -> case decomp u' of
                Left g -> liftHandlerWithNat go3 liftSem g
                Right wav -> commonHandler wav
              {-# NOINLINE go3 #-}
          in
            fmap ex $ lwr $ go1 (h e)
{-# INLINE interpretGenericH #-}

------------------------------------------------------------------------------
-- | The simplest way to produce an effect handler. Interprets an effect @e@ by
-- transforming it into other effects inside of @r@.
--
-- @since TODO
interpret :: forall e r a
              . FirstOrder e "interpret"
             => (∀ z x. e z x -> Sem r x)
             -> Sem (e ': r) a
             -> Sem r a
interpret h =
  interpretH $ \e -> raise (h e)
{-# INLINE interpret #-}

-- TODO (KingoftheHomeless): If it matters, optimize the definitions
-- below

------------------------------------------------------------------------------
-- | Like 'reinterpret', but for higher-order effects.
--
-- @since TODO
reinterpretH :: forall e1 e2 r a
                . EffHandlerH e1 r (e2 ': r)
               -> Sem (e1 ': r) a
               -> Sem (e2 ': r) a
reinterpretH = interpretGenericH
{-# INLINE reinterpretH #-}

------------------------------------------------------------------------------
-- | Like 'interpret', but instead of removing the effect @e@, reencodes it in
-- some new effect @f@. This function will fuse when followed by
-- 'Polysemy.State.runState', meaning it's free to 'reinterpret' in terms of
-- the 'Polysemy.State.State' effect and immediately run it.
--
-- @since TODO
reinterpret :: forall e1 e2 r a
              . FirstOrder e1 "reinterpret"
             => (∀ z x. e1 z x -> Sem (e2 ': r) x)
             -> Sem (e1 ': r) a
             -> Sem (e2 ': r) a
reinterpret h =
  reinterpretH $ \e -> raise (h e)
{-# INLINE reinterpret #-}

------------------------------------------------------------------------------
-- | Like 'reinterpret2', but for higher-order effects.
--
-- @since TODO
reinterpret2H :: forall e1 e2 e3 r a
                 . EffHandlerH e1 r (e2 ': e3 ': r)
                -> Sem (e1 ': r) a
                -> Sem (e2 ': e3 ': r) a
reinterpret2H = interpretGenericH
{-# INLINE reinterpret2H #-}

------------------------------------------------------------------------------
-- | Like 'reinterpret', but introduces /two/ intermediary effects.
--
-- @since TODO
reinterpret2 :: forall e1 e2 e3 r a
              . FirstOrder e1 "reinterpret2"
             => (∀ z x. e1 z x -> Sem (e2 ': e3 ': r) x)
             -> Sem (e1 ': r) a
             -> Sem (e2 ': e3 ': r) a
reinterpret2 h =
  reinterpret2H $ \e -> raise (h e)
{-# INLINE reinterpret2 #-}

------------------------------------------------------------------------------
-- | Like 'reinterpret3', but for higher-order effects.
--
-- @since TODO
reinterpret3H :: forall e1 e2 e3 e4 r a
                 . EffHandlerH e1 r (e2 ': e3 ': e4 ': r)
                -> Sem (e1 ': r) a
                -> Sem (e2 ': e3 ': e4 ': r) a
reinterpret3H = interpretGenericH
{-# INLINE reinterpret3H #-}

------------------------------------------------------------------------------
-- | Like 'reinterpret', but introduces /three/ intermediary effects.
--
-- @since TODO
reinterpret3 :: forall e1 e2 e3 e4 r a
              . FirstOrder e1 "reinterpret3"
             => (∀ z x. e1 z x -> Sem (e2 ': e3 ': e4 ': r) x)
             -> Sem (e1 ': r) a
             -> Sem (e2 ': e3 ': e4 ': r) a
reinterpret3 h =
  reinterpret3H $ \e -> raise (h e)
{-# INLINE reinterpret3 #-}

------------------------------------------------------------------------------
-- | Like 'intercept', but for higher-order effects.
--
-- @since TODO
intercept :: forall e r a
              . Member e r
             => EffHandlerH e r r
             -> Sem r a
             -> Sem r a
intercept h = interpretH h . expose
{-# INLINE intercept #-}

------------------------------------------------------------------------------
-- | Like 'interpret', but instead of handling the effect, allows responding to
-- the effect while leaving it unhandled. This allows you, for example, to
-- intercept other effects and insert logic around them.
--
-- @since TODO
interceptH :: forall e r a
              . FirstOrder e "intercept"
             => Member e r
             => (∀ z x. e z x -> Sem r x)
             -> Sem r a
             -> Sem r a
interceptH h =
  intercept $ \e -> raise (h e)
{-# INLINE interceptH #-}

------------------------------------------------------------------------------
-- | Like 'interceptUsing', but for higher-order effects.
--
-- @since TODO
interceptUsing :: forall e r a
                   . ElemOf e r
                  -> EffHandlerH e r r
                  -> Sem r a
                  -> Sem r a
interceptUsing pr h = interpretH h . exposeUsing pr
{-# INLINE interceptUsing #-}

------------------------------------------------------------------------------
-- | A variant of 'intercept' that accepts an explicit proof that the effect
-- is in the effect stack rather then requiring a 'Member' constraint.
--
-- This is useful in conjunction with 'Polysemy.Membership.tryMembership'
-- in order to conditionally perform 'intercept'.
--
-- @since TODO
interceptUsingH :: forall e r a .
                     FirstOrder e "interceptUsing"
                  => Member e r
                  => ElemOf e r
                  -> (∀ z x. e z x -> Sem r x)
                  -> Sem r a
                  -> Sem r a
interceptUsingH pr h =
  interceptUsing pr $ \e -> raise (h e)
{-# INLINE interceptUsingH #-}