-- | Description: Reexports of membership related functionality
module Polysemy.Membership
  ( -- * Witnesses
    ElemOf (Here, There)
  , membership
  , sameMember

  -- * Checking membership
  , KnownRow
  , tryMembership

  -- * Using membership
  , sendUsing
  , subsumeUsing
  , transformUsing
  , exposeUsing
  , interceptUsing
  , interceptUsingH

  -- * Membership manipulation
  , transformSem
  , transformMembership
  , Subsume(..)
  , Raise(..)

  -- * RowTransformer
  , RowTransformer
  , idRow
  , joinRow
  , extendRowMany
  , extendRowAltMany
  , extendRowAlt1
  , raiseRow
  , raiseRowMany
  , underRow1
  , underRowMany
  , subsumeRow
  , swapRow
  , exposeRow
  , splitRow

    -- * Miscellaneous
  , Append
  , KnownList(..)
  , SList(SEnd, SCons)
  ) where

import Polysemy.Internal
import Polysemy.Internal.Combinators
import Polysemy.Internal.HigherOrder
import Polysemy.Internal.Sing
import Polysemy.Internal.Union
