{-# LANGUAGE BangPatterns, AllowAmbiguousTypes, MagicHash #-}
module Polysemy.Internal.RowTransformer where

import Prelude hiding (id, (.))
import Data.Type.Equality
import Data.Kind (Type, Constraint)
import Polysemy.Internal.Kind
import Polysemy.Internal.Membership
import Polysemy.Internal.Utils
import Polysemy.Internal.Sing
import GHC.Exts (Any, Proxy#, proxy#)
import Control.Category
import Unsafe.Coerce

import Data.Vector (Vector)
import qualified Data.Vector as V


data RowTransformer r r' where
  Id :: RowTransformer r r
  Join :: RowTransformer r' r'' -> RowTransformer r r' -> RowTransformer r r''
  Raise :: {-# UNPACK #-} !(SList l) -> RowTransformer r (Append l r)
  Extend :: {-# UNPACK #-} !(SList r) -> RowTransformer l (Append l r)
  ExtendAlt :: Proxy# r -> {-# UNPACK #-} !(SList l) -> RowTransformer l (Append l r)
  Under :: {-# UNPACK #-} !(SList l) -> RowTransformer a b -> RowTransformer (Append l a) (Append l b)
  Subsume :: {-# UNPACK #-} !(ElemOf e r) -> RowTransformer (e ': r) r
  Swap :: Proxy# r -> {-# UNPACK #-} !(SList l) -> {-# UNPACK #-} !(SList mid)
       -> RowTransformer (Append l (Append mid r)) (Append mid (Append l r))
  Split :: {-# UNPACK #-} !(SList l) -> RowTransformer l g -> RowTransformer r g -> RowTransformer (Append l r) g
  Expose :: {-# UNPACK #-} !(ElemOf e r) -> RowTransformer r (e ': r)
  -- Subsume thirsts for this. Can be written using Split and ExtendAlt
  -- Rewrite :: {-# UNPACK #-} !(SList l) -> RowTransformer l r -> RowTransformer (Append l r) r

{-


RowTransformer l (Append l r)

RowTransformer (Append l r) (Append (Append l r) r')

RowTransformer l (Append (Append l r) r')
~
RowTransformer l (Append l (Append r r'))
-}
instance Category RowTransformer where
  id = Id
  (.) = joinRow

joinRow :: RowTransformer r' r'' -> RowTransformer r r' -> RowTransformer r r''
joinRow Id r = r
joinRow r Id = r
-- joinRow (Raise (UnsafeMkSList i)) (Raise (UnsafeMkSList j)) = unsafeCoerce (Raise (UnsafeMkSList (i + j)))
-- joinRow (Extend (UnsafeMkSList i)) (Extend (UnsafeMkSList j)) = unsafeCoerce (Extend (UnsafeMkSList (i + j)))
-- joinRow (ExtendAlt _ (UnsafeMkSList i)) (Extend _) = unsafeCoerce (ExtendAlt proxy# (UnsafeMkSList i))
-- joinRow (ExtendAlt _ (UnsafeMkSList i)) (ExtendAlt _ _) = unsafeCoerce (ExtendAlt proxy# (UnsafeMkSList i))
-- joinRow (Under (UnsafeMkSList i) l) (Under (UnsafeMkSList j) r) = case compare i j of
--   EQ -> unsafeCoerce $ underRowMany (UnsafeMkSList i) (joinRow l (unsafeCoerce r))
--   LT -> unsafeCoerce $ underRowMany (UnsafeMkSList i) (joinRow l (unsafeCoerce $ Under (UnsafeMkSList (j - i)) r))
--   GT -> unsafeCoerce $ underRowMany (UnsafeMkSList j) (joinRow (unsafeCoerce $ Under (UnsafeMkSList (i - j)) l) r)
joinRow l r = Join l r

idRow :: RowTransformer r r
idRow = Id

raiseRow :: RowTransformer r (e ': r)
raiseRow = Raise (SCons SEnd)

extendRowMany :: SList r -> RowTransformer l (Append l r)
extendRowMany SEnd = unsafeCoerce Id
extendRowMany l = Extend l

extendRowAltMany :: forall r l . SList l -> RowTransformer l (Append l r)
extendRowAltMany = ExtendAlt @r proxy#

extendRowAlt1 :: forall r e. RowTransformer '[e] (e ': r)
extendRowAlt1 = ExtendAlt @r proxy# (SCons SEnd)

raiseRowMany :: forall r l. SList l -> RowTransformer r (Append l r)
raiseRowMany SEnd = Id
raiseRowMany i = Raise i

underRow1 :: RowTransformer x y -> RowTransformer (e ': x) (e ': y)
underRow1 = underRowMany (SCons SEnd)

underRowMany :: SList l -> RowTransformer x y -> RowTransformer (Append l x) (Append l y)
underRowMany SEnd m = m
-- underRowMany (UnsafeMkSList i) (Under (UnsafeMkSList j) m) = unsafeCoerce (underRowMany (UnsafeMkSList (i + j)) m)
-- underRowMany _ Id = Id
underRowMany pr m = Under pr m

subsumeRow :: ElemOf e r -> RowTransformer (e ': r) r
subsumeRow = Subsume

swapRow :: forall r l mid. SList l -> SList mid -> RowTransformer (Append l (Append mid r)) (Append mid (Append l r))
swapRow = Swap (proxy# @r)

exposeRow :: ElemOf e r -> RowTransformer r (e ': r)
exposeRow = Expose

raiseUnderRow :: RowTransformer (e ': r) (e ': e' ': r)
raiseUnderRow = underRow1 raiseRow

splitRow :: SList l -> RowTransformer l g -> RowTransformer r g -> RowTransformer (Append l r) g
splitRow SEnd _ h = h
splitRow l f g = Split l f g

transformMembership :: RowTransformer r r' -> ElemOf e r -> ElemOf e r'
transformMembership Id pr = pr
transformMembership (Join l r) pr = transformMembership l (transformMembership r pr)
transformMembership (Raise l) pr = extendMembershipLeft l pr
transformMembership (Extend (_ :: SList r)) pr = extendMembershipRight @_ @r pr
transformMembership (ExtendAlt (_ :: Proxy# r) _) pr = extendMembershipRight @_ @r pr
transformMembership (Under l row) pr = underMembership l (transformMembership row) pr
transformMembership (Subsume pr_) pr = case pr of
  Here -> pr_
  There pr' -> pr'
transformMembership (Swap (_ :: Proxy# r) l mid) pr = swapStacks @r l mid pr
transformMembership (Expose pr_) pr
  | Just Refl <- sameMember pr_ pr = Here
  | otherwise = There pr
transformMembership (Split l f g) pr = case splitMembership l pr of
  Left pr' -> transformMembership f pr'
  Right pr' -> transformMembership g pr'


{-

newtype Handler m res e = Handler (forall x. Weaving e z x -> (x -> res) -> res)

data Handlers r m res where
  Handlers :: (forall x. m x -> z x) -> Vector1 r (Handler z res) -> Handlers r m res


-}

-- newtype FlippedElemOf r e = FlippedElemOf { unflip :: ElemOf e r }
-- empty :: Vector1 '[] h
-- empty = Vector1 V.empty
-- {-# INLINE empty #-}

-- singleton :: h e -> Vector1 '[e] h
-- singleton = unsafeCoerce V.singleton
-- {-# INLINE singleton #-}

-- index :: Vector1 r h -> ElemOf e r -> h e
-- index = unsafeCoerce V.unsafeIndex
-- {-# INLINE index #-}

-- cons :: h e -> Vector1 r h -> Vector1 (e ': r) h
-- cons = unsafeCoerce V.cons
-- {-# INLINE cons #-}

-- head :: Vector1 (e ': r) h -> h e
-- head = unsafeCoerce V.head
-- {-# INLINE head #-}

-- tail :: Vector1 (e ': r) h -> Vector1 r h
-- tail = unsafeCoerce V.unsafeTail
-- {-# INLINE tail #-}

-- splitAt :: SList l -> Vector1 (Append l r) h -> (Vector1 l h, Vector1 r h)
-- splitAt = unsafeCoerce V.splitAt
-- {-# INLINE splitAt #-}

-- identity :: forall r. KnownList r => Vector1 r (FlippedElemOf r)
-- identity = tabulate FlippedElemOf
-- {-# INLINE identity #-}

-- reassoc :: forall l mid r. Append (Append l mid) r :~: Append l (Append mid r)
-- reassoc = unsafeCoerce Refl
-- {-# INLINE reassoc #-}

-- tabulate :: forall r h. KnownList r => (forall e. ElemOf e r -> h e) -> Vector1 r h
-- tabulate gen = Vector1 $ V.generate l (unsafeCoerce gen)
--   where
--     UnsafeMkSList l = singList @r
-- {-# INLINE tabulate #-}

-- fromMembershipTrans :: forall r r'
--                      . KnownList r
--                     => (forall e. ElemOf e r -> ElemOf e r')
--                     -> (forall h. Vector1 r' h -> Vector1 r h)
-- fromMembershipTrans t =
--   \v -> Vector1 $ V.generate l $ index v . t .# UnsafeMkElemOf
--   where
--     UnsafeMkSList l = singList @r
-- {-# INLINE fromMembershipTrans #-}

-- fromVector1Trans :: forall r r'
--                   . KnownList r'
--                  => (forall h. Vector1 r' h -> Vector1 r h)
--                  -> (forall e. ElemOf e r -> ElemOf e r')
-- fromVector1Trans t = unflip #. index (t (identity @r'))
-- {-# INLINE fromVector1Trans #-}
