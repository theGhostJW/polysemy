{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Description: The 'Bundle' effect for bundling effects
module Polysemy.Bundle
  ( -- * Effect
    Bundle (..)
    -- * Actions
  , sendBundle
  , injBundle
    -- * Interpretations
  , runBundle
  , subsumeBundle
  , collectBundle
  , mapMembershipBundle
    -- * Miscellaneous
  , Append
  , KnownList
  , ListOfLength
  ) where

import Polysemy
import Polysemy.Internal
import Polysemy.Internal.Core
import Polysemy.Internal.Union
import Polysemy.Internal.Utils
import Polysemy.Internal.Bundle (simpleSubsumeMembership)
import Polysemy.Internal.Sing

------------------------------------------------------------------------------
-- | Injects an effect into a 'Bundle'. Useful together with 'transform'.
injBundle :: forall e r m a. Member e r => e m a -> Bundle r m a
injBundle = Bundle membership
{-# INLINE injBundle #-}

------------------------------------------------------------------------------
-- | Send uses of an effect to a 'Bundle' containing that effect.
sendBundle
  :: forall e l r a
   . (Member e l, Member (Bundle l) r)
  => Sem (e ': r) a
  -> Sem r a
sendBundle = sendBundleUsing (membership @e @l)
{-# INLINE sendBundle #-}

------------------------------------------------------------------------------
-- | Send uses of an effect to a 'Bundle' containing that effect, given an
-- explicit proof that that the bundle contains that effect.
sendBundleUsing
  :: forall e l r a
   . Member (Bundle l) r
  => ElemOf e l
  -> Sem (e ': r) a
  -> Sem r a
sendBundleUsing pr = transform (Bundle pr)

-- | Rewrite the top effects of the effect stack into a `Bundle` of those
-- effects.
--
-- The number of effects to be rewritten into the `Bundle` can be disambiguated
-- using type applications whenever necessary. For example:
--
-- @
-- transform2Bundle :: Member (Bundle '[e1, e2]) r
--                  => Sem (e1 ': e2 ': r) a -> Sem r a
-- transform2Bundle = subsume . collectBundle @'[_, _]
-- @
--
collectBundle :: forall l r a
               . KnownList l
              => Sem (Append l r) a
              -> Sem (Bundle l ': r) a
collectBundle =
  hoistSem \(Union pr wav) ->
    hoist (collectBundle @l)
      case splitMembership @r (singList @l) pr of
        Left pr' -> Union Here (rewriteWeaving (Bundle pr') wav)
        Right pr' -> Union (There pr') wav

------------------------------------------------------------------------------
-- | Send uses of @'Bundle' l@ to @'Bundle' r@ given an explicit membership
-- proof transformation
mapMembershipBundle :: forall l' l r a
                     . Member (Bundle l') r
                    => (forall e. ElemOf e l -> ElemOf e l')
                    -> Sem (Bundle l ': r) a
                    -> Sem r a
mapMembershipBundle t = transform (\(Bundle pr e) -> Bundle (t pr) e)

------------------------------------------------------------------------------
-- | Run a @'Bundle' r@ by prepending @r@ to the effect stack.
runBundle
  :: forall r' r a
   . KnownList r'
  => Sem (Bundle r' ': r) a
  -> Sem (Append r' r) a
runBundle = hoistSem $ \u -> hoist runBundle $ case decomp u of
  Right (Sent (Bundle pr e) n) ->
    Union (extendMembershipRight @r' @r pr) $ Sent e n
  Right (Weaved (Bundle pr e) trav mkS wv lwr) ->
    Union (extendMembershipRight @r' @r pr) $ Weaved e trav mkS wv lwr
  Left g -> weakenList @r' @r (singList @r') g

------------------------------------------------------------------------------
-- | Run a @'Bundle' l@ if the effect stack contains all effects of @r@.
subsumeBundle
  :: forall r' r a
   . Members r' r
  => Sem (Bundle r' ': r) a
  -> Sem r a
subsumeBundle = hoistSem $ \u -> hoist subsumeBundle $ case decomp u of
  Right (Sent (Bundle pr e) n) ->
    Union (simpleSubsumeMembership pr) $ Sent e n
  Right (Weaved (Bundle pr e) trav mkS wv lwr) ->
    Union (simpleSubsumeMembership pr) $ Weaved e trav mkS wv lwr
  Left g -> g
