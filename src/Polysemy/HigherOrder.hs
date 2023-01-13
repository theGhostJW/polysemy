-- | Tools for more advanced usages of 'Polysemy.interpretH'
--
-- Most of the `HigherOrder` combinators this module offers are more restrictive
-- than they need to be be, and interact unintuitively with 'intercept'.
-- This is because they're implemented using 'embedH' for efficiency reasons;
-- see 'embedH' for more information.
--
-- "Polysemy.HigherOrder.Flexible" offers an alternate interface with more
-- relaxed variants of these combinators, and interact intuitively with
-- 'intercept' -- however, their usage could significantly degrade performance,
-- depending on the usage characteristics of the effect it's used with.
-- "Polysemy.HigherOrder.Flexible" is designed to be imported instead of
-- "Polysemy.HigherOrder", or imported qualified. Only two combinators differ
-- significantly in signature -- 'runH'' and 'runExposeH''; the @Flexible@
-- variants are typically easier to use.
--
-- The following combinators are identical between "Polysemy.HigherOrder" and
-- "Polysemy.HigherOrder.Flexible": 'restoreH', 'exposeH', 'getStateH',
-- 'processH', 'getProcessorH', 'getInterpreterH', and 'embedH'. Every other
-- combinator differ in signature and implementation between the two modules.
module Polysemy.HigherOrder
  ( -- * 'HigherOrder' effect
    HigherOrder

    -- * Embedding 'Sem' actions
  , embedH

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

import Polysemy.Internal.HigherOrder
