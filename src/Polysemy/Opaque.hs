{-# LANGUAGE AllowAmbiguousTypes #-}
-- | The auxiliary effect 'Opaque' used by interpreters of 'Polysemy.Scoped.Scoped'
module Polysemy.Opaque (
  -- * Effect
  Opaque(..),

  -- * Interpreters
  toOpaque,
  fromOpaque,
  toOpaqueAt,
  fromOpaqueAt,
  collectOpaqueBundleAt,
  runOpaqueBundleAt,
  ) where

import Polysemy
import Polysemy.Internal
import Polysemy.Bundle
import Polysemy.Membership
import Polysemy.Internal.Opaque
import Polysemy.Internal.Core
import Polysemy.Internal.Utils
import Polysemy.Newtype

-- | Wrap 'Opaque' around the top effect of the effect stack
toOpaque :: Sem (e ': r) a -> Sem (Opaque e ': r) a
toOpaque = coerceEff
{-# INLINE toOpaque #-}

-- | Unwrap 'Opaque' around the top effect of the effect stack
fromOpaque :: Sem (Opaque e ': r) a -> Sem (e ': r) a
fromOpaque = coerceEff
{-# INLINE fromOpaque #-}

toOpaqueAt :: forall l e r a
            . Sem (Append l (e ': r)) a
           -> Sem (Append l (Opaque e ': r)) a
toOpaqueAt = coerceEffAt @l @(Opaque e) @e @r
{-# INLINE toOpaqueAt #-}

fromOpaqueAt :: forall l e r a
              . Sem (Append l (e ': r)) a
             -> Sem (Append l (Opaque e ': r)) a
fromOpaqueAt = coerceEffAt @l @(Opaque e) @e @r
{-# INLINE fromOpaqueAt #-}

-- Length of mid can be specified through type applications when necessary
--
-- TODO: ponder the inconsistency. The length of @l@ is always ambiguous,
-- so no reason not to use ListOfLength, but @mid@ can very well be definite,
-- hence why it's just KnownList, and its length must be provided through
-- @'[_, _, ..., _]. The fact that the length of @l@ is provided through
-- a number and @mid@ is provided through the skeleton of the list is
-- inconsistent and may be unintuitive.
collectOpaqueBundleAt
  :: forall n mid r l a
   . (ListOfLength "collectOpaqueBundleAt" n l, KnownList mid)
  => Sem (Append l (Append mid r)) a
  -> Sem (Append l (Opaque (Bundle mid) ': r)) a
collectOpaqueBundleAt = hoistSem $ \(Handlers n hs) ->
  let
    (hl, hr) = splitHandlers' @l @(_ ': r) hs
    AHandler h = AHandler $ getHandler' hr Here
    hm = generateHandlers' (singList @mid) $ \pr wav ->
      h (rewriteWeaving (Opaque #. Bundle pr) wav)
  in
    Handlers (n . collectOpaqueBundleAt @n @mid @r @l) $
      hl `concatHandlers'` hm `concatHandlers'` dropHandlers' @'[_] hr

runOpaqueBundleAt
  :: forall n mid r l a
   . (ListOfLength "runOpaqueBundleAt" n l, KnownList mid)
  => Sem (Append l (Opaque (Bundle mid) ': r)) a
  -> Sem (Append l (Append mid r)) a
runOpaqueBundleAt = hoistSem $ \(Handlers n hs) ->
  let
    (hl, hr) = splitHandlers' @l @(Append mid r) hs
    AHandler h = AHandler $ \wav ->
      case rewriteWeaving' (\(Opaque p) -> p) wav of
        Union pr wav' -> getHandler' hr (extendMembershipRight @mid @r pr) wav'
  in
    Handlers (n . runOpaqueBundleAt @n @mid @r @l) $
      hl `concatHandlers'` h `consHandler'` dropHandlers' @mid @r hr
