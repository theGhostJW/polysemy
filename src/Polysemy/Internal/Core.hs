{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE BangPatterns            #-}
{-# LANGUAGE CPP                     #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE EmptyCase               #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE InstanceSigs            #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PatternSynonyms         #-}
{-# LANGUAGE RoleAnnotations         #-}
{-# LANGUAGE StrictData              #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns            #-}
{-# LANGUAGE MonoLocalBinds          #-}
{-# LANGUAGE QuantifiedConstraints   #-}

{-# OPTIONS_HADDOCK not-home #-}
module Polysemy.Internal.Core where

#if __GLASGOW_HASKELL__ < 808
import Control.Monad.Fail
#endif
import Data.Coerce
import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Fix
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Traversable
import Data.Type.Equality
import Polysemy.Internal.Reflection
import Data.Kind
import Polysemy.Embed.Type
import Polysemy.Fail.Type
import Polysemy.Internal.Fixpoint
import Polysemy.Internal.Kind
import Polysemy.Internal.Opaque
import Polysemy.Internal.NonDet
import Polysemy.Internal.Utils
import Unsafe.Coerce
import GHC.Exts (oneShot, considerAccessible)

-- $setup
-- >>> import Data.Function
-- >>> import Polysemy.State
-- >>> import Polysemy.Error

------------------------------------------------------------------------------
-- | The 'Sem' monad handles computations of arbitrary extensible effects.
-- A value of type @Sem r@ describes a program with the capabilities of
-- @r@. For best results, @r@ should always be kept polymorphic, but you can
-- add capabilities via the 'Polysemy.Member' constraint.
--
-- The value of the 'Sem' monad is that it allows you to write programs
-- against a set of effects without a predefined meaning, and provide that
-- meaning later. For example, unlike with mtl, you can decide to interpret an
-- 'Polysemy.Error.Error' effect traditionally as an 'Either', or instead
-- as (a significantly faster) 'IO' 'Control.Exception.Exception'. These
-- interpretations (and others that you might add) may be used interchangeably
-- without needing to write any newtypes or 'Monad' instances. The only
-- change needed to swap interpretations is to change a call from
-- 'Polysemy.Error.runError' to 'Polysemy.Error.errorToIOFinal'.
--
-- The effect stack @r@ can contain arbitrary other monads inside of it. These
-- monads are lifted into effects via the 'Embed' effect. Monadic values can be
-- lifted into a 'Sem' via 'embed'.
--
-- Higher-order actions of another monad can be lifted into higher-order actions
-- of 'Sem' via the 'Polysemy.Final' effect, which is more powerful
-- than 'Embed', but also less flexible to interpret.
--
-- A 'Sem' can be interpreted as a pure value (via 'run') or as any
-- traditional 'Monad' (via 'Polysemy.runM').
-- Each effect @E@ comes equipped with some interpreters of the form:
--
-- @
-- runE :: 'Sem' (E ': r) a -> 'Sem' r a
-- @
--
-- which is responsible for removing the effect @E@ from the effect stack. It
-- is the order in which you call the interpreters that determines the
-- monomorphic representation of the @r@ parameter.
--
-- Order of interpreters can be important - it determines behaviour of effects
-- that manipulate state or change control flow. For example, when
-- interpreting this action:
--
-- >>> :{
--   example :: Members '[State String, Error String] r => Sem r String
--   example = do
--     put "start"
--     let throwing, catching :: Members '[State String, Error String] r => Sem r String
--         throwing = do
--           modify (++"-throw")
--           throw "error"
--           get
--         catching = do
--           modify (++"-catch")
--           get
--     catch @String throwing (\ _ -> catching)
-- :}
--
-- when handling 'Polysemy.Error.Error' first, state is preserved after error
-- occurs:
--
-- >>> :{
--   example
--     & runError
--     & fmap (either id id)
--     & evalState ""
--     & runM
--     & (print =<<)
-- :}
-- "start-throw-catch"
--
-- while handling 'Polysemy.State.State' first discards state in such cases:
--
-- >>> :{
--   example
--     & evalState ""
--     & runError
--     & fmap (either id id)
--     & runM
--     & (print =<<)
-- :}
-- "start-catch"
--
-- A good rule of thumb is to handle effects which should have \"global\"
-- behaviour over other effects later in the chain.
--
-- After all of your effects are handled, you'll be left with either
-- a @'Sem' '[] a@, a @'Sem' '[ 'Embed' m ] a@, or a @'Sem' '[ 'Polysemy.Final' m ] a@
-- value, which can be consumed respectively by 'run', 'runM', and
-- 'Polysemy.runFinal'.
--
-- ==== Examples
--
-- As an example of keeping @r@ polymorphic, we can consider the type
--
-- @
-- 'Member' ('Polysemy.State.State' String) r => 'Sem' r ()
-- @
--
-- to be a program with access to
--
-- @
-- 'Polysemy.State.get' :: 'Sem' r String
-- 'Polysemy.State.put' :: String -> 'Sem' r ()
-- @
--
-- methods.
--
-- By also adding a
--
-- @
-- 'Member' ('Polysemy.Error' Bool) r
-- @
--
-- constraint on @r@, we gain access to the
--
-- @
-- 'Polysemy.Error.throw' :: Bool -> 'Sem' r a
-- 'Polysemy.Error.catch' :: 'Sem' r a -> (Bool -> 'Sem' r a) -> 'Sem' r a
-- @
--
-- functions as well.
--
-- In this sense, a @'Member' ('Polysemy.State.State' s) r@ constraint is
-- analogous to mtl's @'Control.Monad.State.Class.MonadState' s m@ and should
-- be thought of as such. However, /unlike/ mtl, a 'Sem' monad may have
-- an arbitrary number of the same effect.
--
-- For example, we can write a 'Sem' program which can output either
-- 'Int's or 'Bool's:
--
-- @
-- foo :: ( 'Member' ('Polysemy.Output.Output' Int) r
--        , 'Member' ('Polysemy.Output.Output' Bool) r
--        )
--     => 'Sem' r ()
-- foo = do
--   'Polysemy.Output.output' @Int  5
--   'Polysemy.Output.output' True
-- @
--
-- Notice that we must use @-XTypeApplications@ to specify that we'd like to
-- use the ('Polysemy.Output.Output' 'Int') effect.
--
-- @since 0.1.2.0
newtype Sem (r :: EffectRow) a = Sem
  { runSem
        :: ∀ res
         . (∀ x. Union r (Sem r) x -> (x -> res) -> res)
        -> (a -> res) -> res
  }

------------------------------------------------------------------------------
-- | Like 'runSem' but arguments rearranged for better ergonomics sometimes.
usingSem
    :: (a -> res)
    -> (∀ x. Union r (Sem r) x -> (x -> res) -> res)
    -> Sem r a
    -> res
usingSem c k m = runSem m k c
{-# INLINE usingSem #-}

throughSem
  :: forall r' r
   . (  forall res y
      . (∀ x. Union r' (Sem r') x -> (x -> res) -> res)
     -> Union r (Sem r) y -> (y -> res) -> res
     )
  -> (forall x. Sem r x -> Sem r' x)
throughSem n = \sem -> Sem $ \k ->
  -- eta-expand k in order to oneShot it?
  oneShot $ runSem sem $ \u c -> oneShot (n (\u' -> oneShot (k u')) u) c
{-# INLINE throughSem #-}

------------------------------------------------------------------------------
-- | Extend the stack of a 'Sem' with an explicit 'Union' transformation.
hoistSem
    :: (∀ x. Union r (Sem r) x -> Union r' (Sem r') x)
    -> Sem r a
    -> Sem r' a
hoistSem n = \m -> Sem $ \k -> oneShot (runSem m (\x -> oneShot (k (n x))))
{-# INLINE hoistSem #-}

instance Functor (Sem f) where
  fmap f m = Sem $ \k c -> oneShot (runSem m k) (c . f)
  {-# INLINE fmap #-}

  a <$ m = Sem $ \k c -> oneShot (runSem m k) (\_ -> c a)
  {-# INLINE (<$) #-}

instance Applicative (Sem f) where
  pure a = Sem $ \_ c -> c a
  {-# INLINE pure #-}

  ma <*> mb = Sem $ \k c ->
    oneShot (runSem ma k) (\f -> oneShot (runSem mb k) (c . f))
  {-# INLINE (<*>) #-}

  liftA2 f ma mb = Sem $ \k c ->
    oneShot (runSem ma k) (\a -> oneShot (runSem mb k) (c . f a))
  {-# INLINE liftA2 #-}

  ma <* mb = Sem $ \k c ->
    oneShot (runSem ma k) (\a -> oneShot (runSem mb k) (\_ -> c a))
  {-# INLINE (<*) #-}

  ma *> mb = Sem $ \k c -> oneShot (runSem ma k) (\_ -> oneShot (runSem mb k) c)
  {-# INLINE (*>) #-}

instance Monad (Sem f) where
  ma >>= f = Sem $ \k c ->
    oneShot (runSem ma k) (\a -> oneShot (runSem (f a) k) c)
  {-# INLINE (>>=) #-}


instance (Member NonDet r) => Alternative (Sem r) where
  empty = send Empty
  {-# INLINE empty #-}
  a <|> b = send (Choose a b)
  {-# INLINE (<|>) #-}

-- | @since 0.2.1.0
instance (Member NonDet r) => MonadPlus (Sem r) where
  mzero = empty
  mplus = (<|>)

-- | @since 1.1.0.0
instance (Member Fail r) => MonadFail (Sem r) where
  fail = send .# Fail
  {-# INLINE fail #-}

-- | @since 1.6.0.0
instance Semigroup a => Semigroup (Sem f a) where
  (<>) = liftA2 (<>)

-- | @since 1.6.0.0
instance Monoid a => Monoid (Sem f a) where
  mempty = pure mempty

------------------------------------------------------------------------------
-- | This instance will only lift 'IO' actions. If you want to lift into some
-- other 'MonadIO' type, use this instance, and handle it via the
-- 'Polysemy.IO.embedToMonadIO' interpretation.
instance Member (Embed IO) r => MonadIO (Sem r) where
  liftIO = embed
  {-# INLINE liftIO #-}

instance Member Fixpoint r => MonadFix (Sem r) where
  mfix f = send $ Fixpoint f
  {-# INLINE mfix #-}

data Weave t r m a where
  RestoreW  :: t a -> Weave t r m a
  GetStateW :: ((forall x. x -> t x) -> a) -> Weave t r m a
  LiftWithW :: ((forall r' x. Sem (Weave t r' ': r') x -> Sem r' (t x)) -> a)
            -> Weave t r m a
  EmbedW    :: Sem r a -> Weave t r m a

newtype Traversal t = Traversal {
    getTraversal :: forall f a b. Applicative f => (a -> f b) -> t a -> f (t b)
  }

newtype ViaTraversal (s :: Type) t (a :: Type) =
  ViaTraversal { getViaTraversal :: t a }

instance Reifies s (Traversal t) => Functor (ViaTraversal s t) where
  fmap = fmapDefault
  {-# INLINE fmap #-}

instance Reifies s (Traversal t) => Foldable (ViaTraversal s t) where
  foldMap = foldMapDefault
  {-# INLINE foldMap #-}

instance Reifies s (Traversal t) => Traversable (ViaTraversal s t) where
  traverse f (ViaTraversal t) = ViaTraversal <$> getTraversal (reflect @s) f t
  {-# INLINE traverse #-}

------------------------------------------------------------------------------
-- | An extensible, type-safe union. The @r@ type parameter is a type-level
-- list of effects, any one of which may be held within the 'Union'.
data Union (r :: EffectRow) (mWoven :: Type -> Type) a where
  Union
      :: -- A proof that the effect is actually in @r@.
         {-# UNPACK #-} !(ElemOf e r)
         -- The effect to wrap. The functions 'prj' and 'decomp' can help
         -- retrieve this value later.
      -> !(Weaving e m a)
      -> Union r m a

------------------------------------------------------------------------------
-- | Decompose a 'Union'. Either this union contains an effect @e@---the head
-- of the @r@ list---or it doesn't.
decomp :: Union (e ': r) m a -> Either (Union r m a) (Weaving e m a)
decomp (Union p a) =
  case p of
    Here  -> Right a
    There pr -> Left $ Union pr a
{-# INLINABLE decomp #-}

------------------------------------------------------------------------------
-- | Polysemy's core type that stores effect values together with information
-- about the higher-order interpretation state of its construction site.
data Weaving e m a where
  Sent :: e z a -> !(forall x. z x -> m x) -> Weaving e m a
  Weaved
    :: forall t e z a resultType m.
       { weaveEffect :: e z a
       -- ^ The original effect GADT originally lifted via
       -- a variant of 'Polysemy.Internal.send'.
       -- ^ @z@ is usually @Sem rInitial@, where @rInitial@ is the effect row
       -- that was in scope when this 'Weaving' was originally created.
       , traverseState :: !(Traversal t)
       -- ^ An implementation of 'traverse' for @t@.
       , weaveInitState :: !(forall x. x -> t x)
       -- ^ A piece of state that other effects' interpreters have already
       -- woven through this 'Weaving'.
       , weaveDistrib :: !(forall x. t (z x) -> m (t x))
       -- ^ Distribute @t@ by transforming @z@ into @m@. This is
       -- usually of the form @t ('Polysemy.Sem' (Some ': Effects ': r) x) ->
       --   Sem r (t x)@
       , weaveLowering :: !(forall r x. Sem (Weave t r ': r) x -> Sem r (t x))
       -- TODO document this
       , weaveResult :: !(t a -> resultType)
       -- ^ Even though @t a@ is the moral resulting type of 'Weaving', we
       -- can't expose that fact; such a thing would prevent 'Polysemy.Sem'
       -- from being a 'Monad'.
       } -> Weaving e m resultType

fromFOEff :: Weaving e m a
          -> (forall z b. (b -> a) -> e z b -> res)
          -> res
fromFOEff w c = case w of
  Sent e _ -> oneShot c id e
  Weaved e _ mkS _ _ ex -> oneShot c (ex . mkS) e
{-# INLINEABLE fromFOEff #-}
-- {-# INLINE fromFOEff #-}

fromSimpleHOEff :: Weaving e (Sem r) a
                -> (   forall z t b
                     . (forall x. x -> t x)
                    -> (forall x. z x -> Sem r (t x))
                    -> (t b -> a)
                    -> e z b
                    -> res
                   )
                -> res
fromSimpleHOEff w c = case w of
  Sent e n -> oneShot (c Identity (fmap Identity #. n)) runIdentity e
  Weaved e _ mkS wv _ ex -> oneShot (c mkS (wv . mkS)) ex e
{-# INLINEABLE fromSimpleHOEff #-}
-- {-# INLINE fromSimpleHOEff #-}

hoist :: (∀ x. m x -> n x)
      -> Union r m a
      -> Union r n a
hoist n' (Union w wav) = Union w $ case wav of
  Sent e n -> Sent e (n' . n)
  Weaved e trav mkS wv lwr ex -> Weaved e trav mkS (n' . wv) lwr ex
{-# INLINEABLE hoist #-}
-- {-# INLINE hoist #-}

rewriteComposeWeave :: Sem (Weave (Compose t t') r ': r) x
                    -> Sem (Weave t' (Weave t r ': r) ': Weave t r ': r) x
rewriteComposeWeave = go
  where
    go :: Sem (Weave (Compose t t') r ': r) x
       -> Sem (Weave t' (Weave t r ': r) ': Weave t r ': r) x
    go = throughSem $ \k u c -> case u of
      Union Here wav -> fromFOEff wav $ \ex -> \case
        RestoreW (Compose tt') ->
          k (injUsing (There Here) (RestoreW tt')) \t' ->
          k (injUsing Here (RestoreW t')) (c . ex)
        GetStateW main ->
          (`k` id) $ injUsing (There Here) $ GetStateW $ \mkS ->
          (`k` c) $ injUsing Here $ GetStateW $ \mkS' ->
          ex $ main $ Compose #. mkS . mkS'
        LiftWithW main ->
          (`k` id) $ injUsing (There Here) $ LiftWithW \lwr ->
          (`k` c) $ injUsing Here $ LiftWithW $ \lwr' ->
          ex $ main (fmap Compose #. lwr . lwr' . go_)
        EmbedW m ->
          k (injUsing Here (EmbedW (sendUsing Here (EmbedW m)))) (c . ex)
      Union (There pr) wav -> k (hoist go_ (Union (There (There pr)) wav)) c
    {-# INLINE go #-}

    go_ :: Sem (Weave (Compose t t') r ': r) x
        -> Sem (Weave t' (Weave t r ': r) ': Weave t r ': r) x
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINEABLE rewriteComposeWeave #-}
-- {-# INLINE rewriteComposeWeave #-}

weave :: (Traversable t, forall x y. Coercible x y => Coercible (n x) (n y))
      => t ()
      -> (forall x. t (m x) -> n (t x))
      -> (forall r' x. Sem (Weave t r' ': r') x -> Sem r' (t x))
      -> Union r m a
      -> Union r n (t a)
weave s' wv' lwr' = \(Union pr wav) -> Union pr $ case wav of
  Sent e n -> Weaved e (Traversal traverse) (<$ s') (wv' . fmap n) lwr' id
  Weaved e (Traversal trav) mkS wv lwr ex ->
    let
      cTrav = Traversal (\f -> fmap Compose . traverse (trav f) .# getCompose)
      cEx = fmap ex .# getCompose
    in
      Weaved
        e
        cTrav
        (\x -> Compose $ mkS x <$ s')
        (coerce #. wv' . fmap wv .# getCompose)
        (fmap Compose #. lwr' . lwr . rewriteComposeWeave)
        cEx
{-# INLINABLE weave #-}
{-# SPECIALIZE INLINE
  weave :: Traversable t
        => t ()
        -> (forall x. t (m x) -> Sem r'' (t x))
        -> (forall r' x. Sem (Weave t r' ': r') x -> Sem r' (t x))
        -> Union r m a -> Union r (Sem r'') (t a)
  #-}


rewriteWeaving :: (∀ z x. e z x -> e' z x)
               -> Weaving e m a
               -> Weaving e' m a
rewriteWeaving t = \case
  Sent e n -> Sent (t e) n
  Weaved e trav mkS wv lwr ex -> Weaved (t e) trav mkS wv lwr ex
{-# INLINEABLE rewriteWeaving #-}

------------------------------------------------------------------------------
-- | An effect for collecting multiple effects into one effect.
--
-- Useful for effect newtypes -- effects defined through creating a newtype
-- over an existing effect, and then defining actions and interpretations on
-- the newtype by using 'Polysemy.rewrite' and 'Polysemy.transform'.
--
-- By making a newtype of 'Polysemy.Bundle.Bundle', it's possible to wrap
-- multiple effects in one newtype.
data Bundle r m a where
  Bundle :: {-# UNPACK #-} !(ElemOf e r) -> e m a -> Bundle r m a

rewriteWeaving' :: (∀ z x. e z x -> Bundle r z x)
                -> Weaving e m a
                -> Union r m a
rewriteWeaving' t = \case
  Sent e n
    | Bundle pr e' <- t e -> Union pr (Sent e' n)
  Weaved e trav mkS wv lwr ex
    | Bundle pr e' <- t e -> Union pr (Weaved e' trav mkS wv lwr ex)
{-# INLINEABLE rewriteWeaving' #-}
-- {-# INLINE rewriteWeaving #-}

------------------------------------------------------------------------------
-- | Lift an effect @e@ into a 'Union' capable of holding it.
inj :: forall e r z a. Member e r => e z a -> Union r z a
inj = injUsing membership
{-# INLINEABLE inj #-}
-- {-# INLINE inj #-}

------------------------------------------------------------------------------
-- | Lift an effect @e@ into a 'Union' capable of holding it,
-- given an explicit proof that the effect exists in @r@
injUsing :: forall e r z a.
  ElemOf e r -> e z a -> Union r z a
injUsing pr = injViaUsing pr id
{-# INLINEABLE injUsing #-}
-- {-# INLINE injUsing #-}

------------------------------------------------------------------------------
-- | Lift an effect @e@ into a 'Union' capable of holding it given a natural
-- transformation to transform the monad.
injVia :: forall e r z m a
        . Member e r => (forall x. z x -> m x) -> e z a -> Union r m a
injVia = injViaUsing membership
{-# INLINEABLE injVia #-}
-- {-# INLINE injVia #-}

------------------------------------------------------------------------------
-- | Lift an effect @e@ into a 'Union' capable of holding it,
-- given an explicit proof that the effect exists in @r@, and a
-- natural transformation to transform the monad.
injViaUsing :: forall e r z m a
             . ElemOf e r
            -> (forall x. z x -> m x)
            -> e z a -> Union r m a
injViaUsing pr n e = Union pr (Sent e n)
{-# INLINEABLE injViaUsing #-}
-- {-# INLINE injViaUsing #-}

------------------------------------------------------------------------------
-- | Lift a @'Weaving' e@ into a 'Union' capable of holding it.
injWeaving :: forall e r m a. Member e r => Weaving e m a -> Union r m a
injWeaving = Union membership
{-# INLINEABLE injWeaving #-}
-- {-# INLINE injWeaving #-}

------------------------------------------------------------------------------
-- | Execute an action of an effect.
--
-- This is primarily used to create methods for actions of effects:
--
-- @
-- data FooBar m a where
--   Foo :: String -> m a -> FooBar m a
--   Bar :: FooBar m Int
--
-- foo :: Member FooBar r => String -> Sem r a -> Sem r a
-- foo s m = send (Foo s m)
--
-- bar :: Member FooBar r => Sem r Int
-- bar = send Bar
-- @
--
-- 'Polysemy.makeSem' allows you to eliminate this boilerplate.
send :: Member e r => e (Sem r) a -> Sem r a
send = liftSem . inj
-- {-# INLINE[3] send #-}
{-# INLINEABLE[3] send #-}

------------------------------------------------------------------------------
-- | Execute an action of an effect, given a natural transformation from
-- the monad used for the higher-order chunks in the effect to
-- @'Polysemy.Sem' r@.
--
-- @since 2.0.0.0
sendVia :: forall e z r a
         . Member e r
        => (forall x. z x -> Sem r x)
        -> e z a -> Sem r a
sendVia n = liftSem . injVia n
-- {-# INLINE[3] sendVia #-}
{-# INLINEABLE[3] sendVia #-}

------------------------------------------------------------------------------
-- | Embed an effect into a 'Sem', given an explicit proof
-- that the effect exists in @r@.
--
-- This is useful in conjunction with 'Polysemy.Membership.tryMembership',
-- in order to conditionally make use of effects.
sendUsing :: ElemOf e r -> e (Sem r) a -> Sem r a
sendUsing pr = liftSem . injUsing pr
-- {-# INLINE[3] sendUsing #-}
{-# INLINEABLE[3] sendUsing #-}

------------------------------------------------------------------------------
-- | Embed an effect into a 'Sem', given an explicit proof
-- that the effect exists in @r@, and a natural transformation from the monad
-- used for the higher-order thunks in the effect to @'Polysemy.Sem' r@.
sendViaUsing :: ElemOf e r -> (forall x. z x -> Sem r x) -> e z a -> Sem r a
sendViaUsing pr n = liftSem . injViaUsing pr n
-- {-# INLINE[3] sendViaUsing #-}
{-# INLINEABLE[3] sendViaUsing #-}


------------------------------------------------------------------------------
-- | Embed a monadic action @m@ in 'Sem'.
--
-- @since 1.0.0.0
embed :: Member (Embed m) r => m a -> Sem r a
embed = send .# Embed
{-# INLINEABLE embed #-}
-- {-# INLINE embed #-}

------------------------------------------------------------------------------
-- | Create a 'Sem' from a 'Union' with matching stacks.
liftSem :: Union r (Sem r) a -> Sem r a
liftSem u = Sem $ \k -> oneShot (k u) -- Eta-expansion for better inlining
{-# INLINEABLE liftSem #-}
-- {-# INLINE liftSem #-}


------------------------------------------------------------------------------
-- | A proof that @e@ is an element of @r@.
--
-- Due to technical reasons, @'ElemOf' e r@ is not powerful enough to
-- prove @'Member' e r@; however, it can still be used send actions of @e@
-- into @r@ by using 'Polysemy.Internal.subsumeUsing'.
--
-- @since 1.3.0.0
type role ElemOf nominal nominal
newtype ElemOf (e :: k) (r :: [k]) = UnsafeMkElemOf Int

data MatchHere e r where
  MHYes :: MatchHere e (e ': r)
  MHNo  :: MatchHere e r

data MatchThere e r where
  MTYes :: ElemOf e r -> MatchThere e (e' ': r)
  MTNo  :: MatchThere e r

matchHere :: forall e r. ElemOf e r -> MatchHere e r
matchHere (UnsafeMkElemOf 0) = unsafeCoerce $ MHYes
matchHere _ = MHNo
{-# INLINE matchHere #-}

matchThere :: forall e r. ElemOf e r -> MatchThere e r
matchThere (UnsafeMkElemOf 0) = MTNo
matchThere (UnsafeMkElemOf e) = unsafeCoerce $ MTYes $ UnsafeMkElemOf $ e - 1
{-# INLINE matchThere #-}

absurdMembership :: ElemOf e '[] -> b
absurdMembership !_
  | considerAccessible = errorWithoutStackTrace "bad use of UnsafeMkElemOf"

pattern Here :: () => ((e ': r') ~ r) => ElemOf e r
pattern Here <- (matchHere -> MHYes)
  where
    Here = UnsafeMkElemOf 0

pattern There :: () => ((e' ': r) ~ r') => ElemOf e r -> ElemOf e r'
pattern There e <- (matchThere -> MTYes e)
  where
    There (UnsafeMkElemOf e) = UnsafeMkElemOf $ e + 1

{-# COMPLETE Here, There #-}

------------------------------------------------------------------------------
-- | Checks if two membership proofs are equal. If they are, then that means
-- that the effects for which membership is proven must also be equal.
sameMember :: forall e e' r
            . ElemOf e r
           -> ElemOf e' r
           -> Maybe (e :~: e')
sameMember (UnsafeMkElemOf i) (UnsafeMkElemOf j)
  | i == j    = Just (unsafeCoerce Refl)
  | otherwise = Nothing

------------------------------------------------------------------------------
-- | This class indicates that an effect must be present in the caller's stack.
-- It is the main mechanism by which a program defines its effect dependencies.
class Member (t :: Effect) (r :: EffectRow) where
  -- | Create a proof that the effect @t@ is present in the effect stack @r@.
  membership :: ElemOf t r

instance {-# OVERLAPPING #-} Member t (t ': z) where
  membership = Here

instance Member t z => Member t (_1 ': z) where
  membership = There $ membership @t @z

instance {-# INCOHERENT #-} Member t z => Member t (Opaque q ': z) where
  membership = There $ membership @t @z
