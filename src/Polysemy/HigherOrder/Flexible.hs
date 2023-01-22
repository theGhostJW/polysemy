{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}
-- | Tools for more advanced usages of 'Polysemy.interpretH'
--
-- This is a variant of the "Polysemy.HigherOrder" module where many of the
-- combinators have been made (significantly) more flexible and easier to use,
-- but at the cost of efficiency. See "Polysemy.HigherOrder" for more
-- information.
--
-- The most notable differing combinators are 'runH'' and 'runExposeH'', which
-- can sometimes be much easier to use compared to the "Polysemy.HigherOrder"
-- variants.
--
-- The following combinators are identical between "Polysemy.HigherOrder" and
-- "Polysemy.HigherOrder.Flexible": 'restoreH', 'exposeH', 'getStateH',
-- 'processH', 'getInterpreterH', and 'embedH'. Every other combinator differ
-- in signature and implementation between the two modules.
module Polysemy.HigherOrder.Flexible
  ( -- * 'HigherOrder' effect
    HigherOrder

    -- * Running higher-order chunks
  , runH
  , runH'

    -- * Propagating actions
  , propagate
  , propagateUsing

    -- * Processing higher-order chunks
  , withProcessorH
  , controlWithProcessorH
  , processH
  , ProcessorH(..)
  , getProcessorH

    -- * Manipulating effectful state
  , getStateH
  , restoreH
  , exposeH
  , runExposeH
  , runExposeH'

    -- * Retrieving the current interpreter
  , InterpreterH(..)
  , getInterpreterH

  -- * Lowering @'Polysemy.Sem' ('HigherOrder' ... ': r)@ to @'Polysemy.Sem' r@
  , liftWithH
  , controlH

  -- * Retrieving the type parameters of a 'HigherOrder'
  , TypeParamsH(..)
  , getTypeParamsH
  ) where

import Control.Monad
import Polysemy.Internal
import Polysemy.Internal.HigherOrder hiding (
  runH, runH', propagate, propagateUsing, withProcessorH, controlWithProcessorH,
  runExposeH, runExposeH', liftWithH, controlH
  )
import Polysemy.Internal.Union

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
           . (Member e r, Raise rH r)
          => e z a
          -> Sem (HigherOrder z t eH rH rC ': r) a
propagate = propagateUsing membership

-- | Propagate an effect action where the higher-order chunks are of the same
-- monad @z@ as that used by the effect currently being handled, given an
-- explicit proof that the effect exists in the effect stack.
propagateUsing :: forall e r z t eH rH rC a
                . Raise rH r
               => ElemOf e r
               -> e z a
               -> Sem (HigherOrder z t eH rH rC ': r) a
propagateUsing pr = sendViaUsing (There pr) runH

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
-- 'runH' :: z a -> 'Polysemy.Sem' ('Polysemy.HigherOrder' z t e r ': r) a
-- @
--
-- @since 2.0.0.0
runH :: forall r z t e rH rC a
      . Raise rH r
     => z a
     -> Sem (HigherOrder z t e rH rC ': r) a
runH = runExposeH >=> restoreH

-- | Run a monadic action given by a higher-order effect that is currently
-- being interpreted.
--
-- Unlike 'runH', this doesn't recursively apply the current interpreter
-- to the monadic action -- allowing you to run a different interpreter
-- on it instead.
--
-- @since 2.0.0.0
runH' :: forall r z t e rH rC a
       . Raise rH r
      => z a
      -> Sem (e ': HigherOrder z t e rH rC ': r) a
runH' = runExposeH' >=> raise . restoreH

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
              -> Sem r a)
          -> Sem (HigherOrder z t e rH rC ': r) a
liftWithH main = sendUsing Here (LiftWithH main) >>= raise

-- | A particularly useful composition:
-- @'controlH' h = 'liftWithH' h >>= 'restoreH'@
--
-- This is analogous to @controlT@ of @MonadTransControl@.
--
-- Note: the lowering function lowers @'Sem' ('HigherOrder' ... ': r)@ by using
-- the effectful state as it is when 'controlH' is run.
controlH :: forall r z t e rH rC a
          . (   (   forall r' x
                  . Sem (HigherOrder z t e rH r' ': r') x
                 -> Sem r' (t x))
             -> Sem r (t a))
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
            . Raise rH r
           => z a -> Sem (HigherOrder z t e rH rC ': r) (t a)
runExposeH z = do
  InterpreterH interp <- getInterpreterH
  withProcessorH $ \prcs -> raise_ $ interp $ prcs z

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
runExposeH' :: forall r z t e rH rC a
             . Raise rH r
            => z a
            -> Sem (e ': HigherOrder z t e rH rC ': r) (t a)
runExposeH' =
      raise . processH
  >=> transformSem (underRow1 (raiseRow `joinRow` raiseMembership @rH @r))

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
                   -> Sem r a)
               -> Sem (HigherOrder z t e rH rC ': r) a
withProcessorH main = do
  ProcessorH prcs <- getProcessorH
  s <- getStateH
  raise $ main (\z -> prcs s (\_ -> z))

-- | A particularly useful composition:
-- @'controlWithProcessorH' h = 'withProcessorH' h >>= 'restoreH'@
--
-- /Note/: Processed actions make use of the effectful state as it is by
-- the time 'withProcessorH' is run, rather than what it is by the time the
-- processed action is run.
controlWithProcessorH :: forall r z t e rH rC a
                       . ((forall x. z x -> Sem (e ': rH) (t x))
                          -> Sem r (t a))
                      -> Sem (HigherOrder z t e rH rC ': r) a
controlWithProcessorH main = withProcessorH main >>= restoreH
