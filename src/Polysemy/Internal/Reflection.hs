{-# LANGUAGE AllowAmbiguousTypes, MagicHash, FunctionalDependencies #-}
module Polysemy.Internal.Reflection
  ( Reifies (..)
  , reify
  ) where

import Unsafe.Coerce
import Data.Kind (Type)
import GHC.Exts (Proxy#, proxy#)

newtype Tagged s a = Tagged a

unproxy :: (Proxy# s -> a) -> Tagged s a
unproxy f = Tagged (f proxy#)
{-# INLINE unproxy #-}

class Reifies (s :: Type) a | s -> a where
  reflect :: a

data Skolem

newtype Magic a r = Magic (Reifies Skolem a => Tagged Skolem r)

reifyTagged :: forall a r. a -> (forall (s :: Type). Reifies s a => Tagged s r) -> r
reifyTagged a k = unsafeCoerce (Magic k :: Magic a r) a
{-# INLINE reifyTagged #-}

reify :: forall a r. a -> (forall (s :: Type) pr. (pr ~ Proxy#, Reifies s a) => pr s -> r) -> r
reify a k = reifyTagged a (unproxy k)
{-# INLINE reify #-}
