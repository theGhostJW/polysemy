{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK not-home #-}

-- | Description: The 'Sem' type and the most basic stack manipulation utilities
module Polysemy.Internal
  ( Sem (..)
  , Member
  , Members
  , send
  , sendVia
  , sendUsing
  , sendViaUsing
  , embed
  , run
  , raise_
  , Raise (..)
  , raise
  , raiseUnder
  , raiseUnder2
  , raiseUnder3
  , raise2Under
  , raise3Under
  , subsume_
  , Subsume (..)
  , subsume
  , subsumeUsing
  , insertAt
  , sinkBelow
  , floatAbove
  , expose
  , exposeUsing
  , Embed (..)
  , usingSem
  , liftSem
  , throughSem
  , hoistSem
  , mapMembership
  , Append
  , InterpreterFor
  , InterpretersFor
  , interpretFast
  ) where

import Data.Kind
import Data.Type.Equality
import Polysemy.Embed.Type
import Polysemy.Internal.Index (InsertAtIndex(insertAtIndex))
import Polysemy.Internal.Kind
import Polysemy.Internal.PluginLookup
import Polysemy.Internal.Union
import Polysemy.Internal.Sing
import Polysemy.Internal.Core


------------------------------------------------------------------------------
-- | Due to a quirk of the GHC plugin interface, it's only easy to find
-- transitive dependencies if they define an orphan instance. This orphan
-- instance allows us to find "Polysemy.Internal" in the polysemy-plugin.
instance PluginLookup Plugin


------------------------------------------------------------------------------
-- | Makes constraints of functions that use multiple effects shorter by
-- translating single list of effects into multiple 'Member' constraints:
--
-- @
-- foo :: 'Members' \'[ 'Polysemy.Output.Output' Int
--                 , 'Polysemy.Output.Output' Bool
--                 , 'Polysemy.State' String
--                 ] r
--     => 'Sem' r ()
-- @
--
-- translates into:
--
-- @
-- foo :: ( 'Member' ('Polysemy.Output.Output' Int) r
--        , 'Member' ('Polysemy.Output.Output' Bool) r
--        , 'Member' ('Polysemy.State' String) r
--        )
--     => 'Sem' r ()
-- @
--
-- @since 0.1.2.0
type family Members es r :: Constraint where
  Members '[]       r = ()
  Members (e ': es) r = (Member e r, Members es r)

------------------------------------------------------------------------------
-- | Rewrite the effect stack of a 'Sem' using with an explicit membership proof
-- transformation.
mapMembership :: forall r r' a
               . (forall e. ElemOf e r -> ElemOf e r')
              -> Sem r a
              -> Sem r' a
mapMembership n = go
  where
    go :: forall x. Sem r x -> Sem r' x
    go = hoistSem $ \(Union pr wav) -> hoist go_ $ Union (n pr) wav
    {-# INLINE go #-}

    go_ :: forall x. Sem r x -> Sem r' x
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINEABLE[0] mapMembership #-}

{-# RULES
"mapMembership/id" [2]
  forall m.
    mapMembership idMembership m = m

"mapMembership/mapMembership" [1]
  forall (f :: forall e. ElemOf e r' -> ElemOf e r'')
         (g :: forall e. ElemOf e r -> ElemOf e r') m.
    mapMembership f (mapMembership g m) = mapMembership (f . g) m
#-}

------------------------------------------------------------------------------
-- | Introduce an arbitrary number of effects on top of the effect stack. This
-- function is highly polymorphic, so it may be good idea to use its more
-- concrete versions (like 'raise') or type annotations to avoid vague errors
-- in ambiguous contexts.
--
-- @since 1.4.0.0
raise_ :: ∀ r r' a. Raise r r' => Sem r a -> Sem r' a
raise_ = mapMembership raiseMembership
{-# INLINE raise_ #-}


-- | See 'raise'.
--
-- @since 1.4.0.0
class Raise (r :: EffectRow) (r' :: EffectRow) where
  raiseMembership :: ElemOf e r -> ElemOf e r'

instance {-# INCOHERENT #-} Raise r r where
  raiseMembership = idMembership
  {-# INLINE raiseMembership #-}

instance {-# OVERLAPPING #-} Raise (e ': r) (e ': r) where
  raiseMembership = idMembership
  {-# INLINE raiseMembership #-}

instance Raise r r' => Raise r (_0 ': r') where
  raiseMembership = There . raiseMembership

------------------------------------------------------------------------------
-- | Introduce an effect into 'Sem'. Analogous to
-- 'Control.Monad.Class.Trans.lift' in the mtl ecosystem. For a variant that
-- can introduce an arbitrary number of effects, see 'raise_'.
raise :: ∀ e r a. Sem r a -> Sem (e ': r) a
raise = raise_
{-# INLINE[3] raise #-}


------------------------------------------------------------------------------
-- | Like 'raise', but introduces a new effect underneath the head of the
-- list. See 'raiseUnder2' or 'raiseUnder3' for introducing more effects. If
-- you need to introduce even more of them, check out 'subsume_'.
--
-- 'raiseUnder' can be used in order to turn transformative interpreters
-- into reinterpreters. This is especially useful if you're writing an
-- interpreter which introduces an intermediary effect, and then want to use
-- an existing interpreter on that effect.
--
-- For example, given:
--
-- @
-- fooToBar :: 'Member' Bar r => 'Sem' (Foo ': r) a -> 'Sem' r a
-- runBar   :: 'Sem' (Bar ': r) a -> 'Sem' r a
-- @
--
-- You can write:
--
-- @
-- runFoo :: 'Sem' (Foo ': r) a -> 'Sem' r a
-- runFoo =
--     runBar     -- Consume Bar
--   . fooToBar   -- Interpret Foo in terms of the new Bar
--   . 'raiseUnder' -- Introduces Bar under Foo
-- @
--
-- @since 1.2.0.0
raiseUnder :: ∀ e2 e1 r a. Sem (e1 ': r) a -> Sem (e1 ': e2 ': r) a
raiseUnder = subsume_
{-# INLINE raiseUnder #-}


------------------------------------------------------------------------------
-- | Like 'raise', but introduces two new effects underneath the head of the
-- list.
--
-- @since 2.0.0.0
raise2Under :: ∀ e2 e3 e1 r a. Sem (e1 ': r) a -> Sem (e1 ': e2 ': e3 ': r) a
raise2Under = subsume_
{-# INLINE raise2Under #-}


------------------------------------------------------------------------------
-- | Like 'raise', but introduces three new effects underneath the head of the
-- list.
--
-- @since 2.0.0.0
raise3Under :: ∀ e2 e3 e4 e1 r a. Sem (e1 ': r) a -> Sem (e1 ': e2 ': e3 ': e4 ': r) a
raise3Under = subsume_
{-# INLINE raise3Under #-}


------------------------------------------------------------------------------
-- | Like 'raise', but introduces an effect two levels underneath the head of
-- the list.
--
-- @since 2.0.0.0
raiseUnder2 :: ∀ e3 e1 e2 r a. Sem (e1 : e2 : r) a -> Sem (e1 : e2 : e3 : r) a
raiseUnder2 = subsume_
{-# INLINE raiseUnder2 #-}


------------------------------------------------------------------------------
-- | Like 'raise', but introduces an effect three levels underneath the head
-- of the list.
--
-- @since 2.0.0.0
raiseUnder3 :: ∀ e4 e1 e2 e3 r a. Sem (e1 : e2 : e3 : r) a -> Sem (e1 : e2 : e3 : e4 : r) a
raiseUnder3 = subsume_
{-# INLINE raiseUnder3 #-}


------------------------------------------------------------------------------
-- | Allows reordering and adding known effects on top of the effect stack, as
-- long as the polymorphic "tail" of new stack is a 'raise'-d version of the
-- original one. This function is highly polymorphic, so it may be a good idea
-- to use its more concrete version ('subsume'), fitting functions from the
-- 'raise' family or type annotations to avoid vague errors in ambiguous
-- contexts.
--
-- @since 1.4.0.0
subsume_ :: ∀ r r' a. Subsume r r' => Sem r a -> Sem r' a
subsume_ = mapMembership subsumeMembership
{-# INLINE subsume_ #-}

class Raise' (r :: EffectRow) (r' :: EffectRow) where
  raiseMembership' :: ElemOf e r -> ElemOf e r'

instance {-# INCOHERENT #-} Raise' r r where
  raiseMembership' = idMembership
  {-# INLINE raiseMembership' #-}

instance {-# OVERLAPPING #-} Raise' (e ': r) (e ': r) where
  raiseMembership' = idMembership
  {-# INLINE raiseMembership' #-}

instance Subsume r r' => Raise' r (_0 ': r') where
  raiseMembership' = There . subsumeMembership

class Subsume' (origR' :: EffectRow) (r :: EffectRow) (r' :: EffectRow) where
  subsumeMembership' :: (ElemOf e r' -> ElemOf e origR')
                     -> ElemOf e r -> ElemOf e origR'

instance Subsume r origR' => Subsume' origR' r r' where
  subsumeMembership' _ = subsumeMembership
  {-# INLINE subsumeMembership' #-}

instance {-# INCOHERENT #-} Subsume' origR r r'
  => Subsume' origR (e ': r) (e ': r') where
  subsumeMembership' t Here = t Here
  subsumeMembership' t (There pr) = subsumeMembership' (t . There) pr

instance {-# INCOHERENT #-} Subsume' origR (e ': r) (e ': r) where
  subsumeMembership' t = t
  {-# INLINE subsumeMembership' #-}

-- | See 'subsume_'.
--
-- @since 1.4.0.0
class Subsume (r :: EffectRow) (r' :: EffectRow) where
  subsumeMembership :: ElemOf e r -> ElemOf e r'

instance {-# INCOHERENT #-} Raise' r r' => Subsume r r' where
  subsumeMembership = raiseMembership'
  {-# INLINE subsumeMembership #-}

instance {-# INCOHERENT #-} Subsume' (e ': r') (e ': r) (e ': r')
      => Subsume (e ': r) (e ': r') where
  subsumeMembership = subsumeMembership' idMembership
  {-# INLINE subsumeMembership #-}

instance Subsume '[] r where
  subsumeMembership = absurdMembership
  {-# INLINE subsumeMembership #-}

instance (Member e r', Subsume r r') => Subsume (e ': r) r' where
  subsumeMembership Here = membership
  subsumeMembership (There pr) = subsumeMembership pr

------------------------------------------------------------------------------
-- | Interprets an effect in terms of another identical effect.
--
-- This is useful for defining interpreters that use 'Polysemy.reinterpretH'
-- without immediately consuming the newly introduced effect.
-- Using such an interpreter recursively may result in duplicate effects,
-- which may then be eliminated using 'subsume'.
--
-- For a version that can introduce an arbitrary number of new effects and
-- reorder existing ones, see 'subsume_'.
--
-- @since 1.2.0.0
subsume :: ∀ e r a. Member e r => Sem (e ': r) a -> Sem r a
subsume = subsume_
{-# INLINE subsume #-}


------------------------------------------------------------------------------
-- | Interprets an effect in terms of another identical effect, given an
-- explicit proof that the effect exists in @r@.
--
-- This is useful in conjunction with 'Polysemy.Membership.tryMembership'
-- in order to conditionally make use of effects. For example:
--
-- @
-- tryListen :: 'Polysemy.Membership.KnownRow' r => 'Sem' r a -> Maybe ('Sem' r ([Int], a))
-- tryListen m = case 'Polysemy.Membership.tryMembership' @('Polysemy.Writer.Writer' [Int]) of
--   Just pr -> Just $ 'subsumeUsing' pr ('Polysemy.Writer.listen' ('raise' m))
--   _       -> Nothing
-- @
--
-- 'subsumeUsing' is also useful when you encounter issues with
-- 'Polysemy.Member', as the membership proof can be used to explicitly target
-- a specific effect.
--
-- @
-- localUnder :: forall i e r a. 'Polysemy.Member' ('Polysemy.Reader.Reader' i) r
--            => (i -> i) -> 'Sem' (e ': r) a -> 'Sem' (e ': r) a
-- localUnder f m = 'Polysemy.Membership.subsumeUsing' @(Reader i) ('Polysemy.Membership.There' 'Polysemy.Membership.membership') ('Polysemy.Reader.local' f ('Polysemy.raise' m))
-- @
--
-- @since 1.3.0.0
subsumeUsing :: ∀ e r a. ElemOf e r -> Sem (e ': r) a -> Sem r a
subsumeUsing pr = mapMembership \case
  Here -> pr
  There pr' -> pr'
{-# INLINE subsumeUsing #-}

------------------------------------------------------------------------------
-- | Moves all uses of an effect @e@ within the argument computation
-- to a new @e@ placed on top of the effect stack. Note that this does not
-- consume the inner @e@.
--
-- This can be used to create interceptors out of interpreters.
-- For example:
--
-- @
-- 'Polysemy.intercept' k = 'Polysemy.interpret' k . 'expose'
-- @
--
-- @since TODO
expose :: Member e r => Sem r a -> Sem (e ': r) a
expose = exposeUsing membership
{-# INLINE expose #-}

------------------------------------------------------------------------------
-- | Introduce a set of effects into 'Sem' at the index @i@, before the effect
-- that previously occupied that position. This is intended to be used with a
-- type application:
--
-- @
-- let
--   sem1 :: Sem [e1, e2, e3, e4, e5] a
--   sem1 = insertAt @2 (sem0 :: Sem [e1, e2, e5] a)
-- @
--
-- @since 1.6.0.0
insertAt
  :: forall index inserted head oldTail tail old full a
   . ( ListOfLength "insertAt" index head
     , old ~ Append head oldTail
     , tail ~ Append inserted oldTail
     , full ~ Append head tail
     , InsertAtIndex index head tail oldTail full inserted)
  => Sem old a
  -> Sem full a
insertAt = mapMembership $
  injectMembership
    @oldTail
    (listOfLength @"insertAt" @index @head)
    (insertAtIndex @Effect @index @head @tail @oldTail @full @inserted)
{-# INLINE insertAt #-}

-- | Given an explicit proof that @e@ exists in @r@, moves all uses of e@
-- within the argument computation to a new @e@ placed on top of the effect
-- stack. Note that this does not consume the inner @e@.
--
-- This is useful in conjunction with 'Polysemy.Internal.Union.tryMembership'
-- and 'interpret'\/'interpretH' in order to conditionally perform
-- 'intercept'-like operations.
--
-- @since 2.0.0.0
exposeUsing :: forall e r a. ElemOf e r -> Sem r a -> Sem (e ': r) a
exposeUsing pr = mapMembership \pr' ->
  case sameMember pr pr' of
    Just Refl -> Here
    _         -> There pr'
{-# INLINE exposeUsing #-}



------------------------------------------------------------------------------
-- | Run a 'Sem' containing no effects as a pure value.
run :: Sem '[] a -> a
run (Sem m) = m absurdU id
{-# INLINE run #-}


------------------------------------------------------------------------------
-- | Type synonym for interpreters that consume an effect without changing the
-- return value. Offered for user convenience.
--
-- @r@ Is kept polymorphic so it's possible to place constraints upon it:
--
-- @
-- teletypeToIO :: 'Member' (Embed IO) r
--              => 'InterpreterFor' Teletype r
-- @
type InterpreterFor e r = ∀ a. Sem (e ': r) a -> Sem r a


------------------------------------------------------------------------------
-- | Variant of 'InterpreterFor' that takes a list of effects.
-- @since 1.5.0.0
type InterpretersFor es r = ∀ a. Sem (Append es r) a -> Sem r a


sinkBelow :: forall l e r a
           . KnownList l => Sem (e ': Append l r) a -> Sem (Append l (e ': r)) a
sinkBelow = mapMembership \case
  Here -> extendMembershipLeft @(e ': r) (singList @l) Here
  There pr -> injectMembership @r (singList @l) (singList @'[e]) pr
{-# INLINE sinkBelow #-}

floatAbove :: forall l e r a
           . KnownList l => Sem (Append l (e ': r)) a -> Sem (e ': Append l r) a
floatAbove = mapMembership \pr ->
  case splitMembership @(e ': r) (singList @l) pr of
    Left pr' -> There (extendMembershipRight @_ @r pr')
    Right Here -> Here
    Right (There pr') ->
      There (extendMembershipLeft @r (singList @l) pr')
{-# INLINE floatAbove #-}

interpretFast :: forall e r. (∀ z x. e z x -> Sem r x) -> InterpreterFor e r
interpretFast h = go
  where
    go :: InterpreterFor e r
    go = throughSem $ \k u c -> case decomp u of
      Left g -> k (hoist go_ g) c
      Right wav -> fromFOEff wav $ \ex e -> runSem (h e) k (c . ex)
    {-# INLINE go #-}

    go_ :: InterpreterFor e r
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINEABLE interpretFast #-}
