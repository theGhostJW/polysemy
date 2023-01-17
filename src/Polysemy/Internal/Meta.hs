{-# OPTIONS_HADDOCK not-home #-}
{-# LANGUAGE AllowAmbiguousTypes, BangPatterns, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FunctionalDependencies, UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving  #-}

module Polysemy.Internal.Meta where

import Control.Monad

import Data.Functor.Identity
import Data.Kind (Type)
import Data.Unique
import Data.Type.Equality

import Polysemy
import Polysemy.Bundle
import Polysemy.Membership
import Polysemy.Internal
import Polysemy.Internal.Union
import Polysemy.Internal.Utils
import Polysemy.Internal.HigherOrder
import Polysemy.Internal.Reflection
import Polysemy.Internal.Core
import System.IO.Unsafe
import Unsafe.Coerce

type MetaEffect = [(Type -> Type, Effect)] -> Effect

data MetaRun :: Effect where
  MetaRun :: forall eff m a. Unique -> eff m a -> MetaRun m a

type (:%) a b = '(a, b)

data Meta (metaeff :: MetaEffect) :: Effect where
  MetaMetaRun :: forall metaeff m a
               . MetaRun m a -> Meta metaeff m a
  SendMeta :: forall metaeff l z m a
            . metaeff l z a
           -> (forall x. z x -> m x)
           -> (forall eff q x. Unique -> ElemOf '(q, eff) l -> q x -> m x)
           -> Meta metaeff m a

class AllSemRaises l r where

instance AllSemRaises '[] r
instance (t ~ '(Sem (eff ': r), eff), AllSemRaises l' r)
      => AllSemRaises (t ': l') r

proveSemRaise :: forall l r eff z
               . AllSemRaises l r => ElemOf '(z, eff) l -> z :~: Sem (eff ': r)
proveSemRaise !_ = unsafeCoerce Refl
{-# INLINE proveSemRaise #-}

sendMeta :: forall metaeff l r a
          . (Member (Meta metaeff) r, AllSemRaises l r)
         => metaeff l (Sem r) a
         -> Sem r a
sendMeta = sendMetaUsing membership
{-# INLINE sendMeta #-}

sendMetaUsing :: forall metaeff l r a
               . AllSemRaises l r
              => ElemOf (Meta metaeff) r
              -> metaeff l (Sem r) a
              -> Sem r a
sendMetaUsing pr = sendMetaViaUsing pr
                    id
                    (\pr' -> case proveSemRaise @l @r pr' of Refl -> id)
{-# INLINE sendMetaUsing #-}

sendMetaVia :: forall metaeff l m r a
             . Member (Meta metaeff) r
            => (forall x. m x -> Sem r x)
            -> (forall eff z x. ElemOf '(z, eff) l -> z x -> Sem (eff ': r) x)
            -> metaeff l m a
            -> Sem r a
sendMetaVia = sendMetaViaUsing membership
{-# INLINE sendMetaVia #-}

sendMetaViaUsing
  :: forall metaeff l m r a
   . ElemOf (Meta metaeff) r
  -> (forall x. m x -> Sem r x)
  -> (forall eff z x. ElemOf '(z, eff) l -> z x -> Sem (eff ': r) x)
  -> metaeff l m a
  -> Sem r a
sendMetaViaUsing pr to1 to2 p = sendUsing pr $ SendMeta p to1 $ \uniq pr' ->
  transformUsing pr (MetaMetaRun @metaeff . MetaRun uniq) . to2 pr'
{-# INLINE sendMetaViaUsing #-}

metaToMeta ::
  ∀ metaeff1 metaeff0 r.
  Member (Meta metaeff1) r =>
  (forall l m x. metaeff0 l m x -> metaeff1 l m x) ->
  InterpreterFor (Meta metaeff0) r
metaToMeta = metaToMetaUsing membership
{-# INLINE metaToMeta #-}

metaToMetaUsing ::
  ∀ metaeff1 metaeff0 r.
  ElemOf (Meta metaeff1) r ->
  (forall l m x. metaeff0 l m x -> metaeff1 l m x) ->
  InterpreterFor (Meta metaeff0) r
metaToMetaUsing pr n = transformUsing pr \case
  MetaMetaRun metarun -> MetaMetaRun metarun
  SendMeta metaeff to1 to2 -> SendMeta (n metaeff) to1 to2
{-# INLINEABLE metaToMetaUsing #-}

metaIntoMeta ::
  ∀ metaeff1 metaeff0 r.
  (forall l m x. metaeff0 l m x -> metaeff1 l m x) ->
  (forall x. Sem (Meta metaeff0 ': r) x -> Sem (Meta metaeff1 ': r) x)
metaIntoMeta n = rewrite \case
  MetaMetaRun metarun -> MetaMetaRun metarun
  SendMeta metaeff to1 to2 -> SendMeta (n metaeff) to1 to2
{-# INLINEABLE metaIntoMeta #-}

mkIntoMeta :: ∀ metaeff m x. metaeff '[] m x -> Meta metaeff m x
mkIntoMeta e = SendMeta e id (\_ u _ -> absurdMembership u)
{-# INLINE mkIntoMeta #-}

type family ProcessorWithMeta metaeff (b :: Bool) (tail :: EffectRow) where
  ProcessorWithMeta metaeff 'True tail = Meta metaeff ': tail
  ProcessorWithMeta metaeff b tail = tail

newtype ProcessorMetaUsing (b :: Bool) metaeff t rH l = ProcessorMetaUsing {
    unProcessorMetaUsing
      :: forall q eff x y
       . ElemOf '(q, eff) l
      -> t x
      -> (x -> q y)
      -> Sem (eff
              ': ProcessorWithMeta metaeff b
                 (HandlingMeta metaeff t rH l ': rH)) (t y)
  }

newtype ProcessorMeta (b :: Bool) metaeff t rH l = ProcessorMeta {
    unProcessorMeta
      :: forall q eff x y
       . DepMember eff q l
      => t x
      -> (x -> q y)
      -> Sem (eff
              ': ProcessorWithMeta metaeff b
                 (HandlingMeta metaeff t rH l ': rH)) (t y)
  }

data HandlingMeta metaeffect t rH l :: Effect where
  HandlingMetaMetaRun
    :: forall metaeffect t rH l m a
     . MetaRun m a -> HandlingMeta metaeffect t rH l m a
  ProcessMeta
    :: forall eff q metaeffect t rH l m x y
     . ElemOf '(q, eff) l
    -> t x
    -> (x -> q y)
    -> HandlingMeta metaeffect t rH l m
        (Sem (eff ': HandlingMeta metaeffect t rH l ': rH) (t y))
  ProcessMeta'
    :: forall eff q metaeffect t rH l m x y
     . ElemOf '(q, eff) l
    -> t x
    -> (x -> q y)
    -> HandlingMeta metaeffect t rH l m
        (Sem (eff ': Meta metaeffect
              ': HandlingMeta metaeffect t rH l ': rH) (t y))

data Box where
  Box :: a -> Box

newUniqueIO :: Box -> IO Unique
newUniqueIO (Box _) = newUnique
{-# NOINLINE newUniqueIO #-}

newUniqueSem :: Sem r Unique
newUniqueSem = Sem $ \k c ->
  let
    uniq = unsafePerformIO (newUniqueIO (Box k))
    {-# NOINLINE uniq #-}
  in
    uniq `seq` c uniq
{-# NOINLINE newUniqueSem #-}

class DepMember eff z l | z l -> eff where
  depMembership :: ElemOf '(z, eff) l

instance {-# OVERLAPPING #-}
      eff ~ eff'
  => DepMember eff z ('(z, eff') ': l) where
  depMembership = Here

instance DepMember eff z l
      => DepMember eff z (_t : l) where
  depMembership = There depMembership

getProcessorMetaUsing
  :: forall r metaeff z t rH rC l mh
   . mh ~ HandlingMeta metaeff t rH l
  => Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
         (ProcessorMetaUsing 'False metaeff t rH l)
getProcessorMetaUsing = return (ProcessorMetaUsing metaProcessorUsing)
{-# INLINE getProcessorMetaUsing #-}

getProcessorMetaUsing'
  :: forall r metaeff z t rH rC l mh
   . mh ~ HandlingMeta metaeff t rH l
  => Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
         (ProcessorMetaUsing 'True metaeff t rH l)
getProcessorMetaUsing' = return (ProcessorMetaUsing metaProcessorUsing')
{-# INLINE getProcessorMetaUsing' #-}

getProcessorMeta
  :: forall r metaeff z t rH rC l mh
   . mh ~ HandlingMeta metaeff t rH l
  => Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
         (ProcessorMeta 'False metaeff t rH l)
getProcessorMeta = return (ProcessorMeta (metaProcessorUsing depMembership))
{-# INLINE getProcessorMeta #-}

getProcessorMeta'
  :: forall r metaeff z t rH rC l mh
   . mh ~ HandlingMeta metaeff t rH l
  => Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
         (ProcessorMeta 'True metaeff t rH l)
getProcessorMeta' = return (ProcessorMeta (metaProcessorUsing' depMembership))
{-# INLINE getProcessorMeta' #-}

metaProcessorUsing
  :: forall q eff metaeff t r l x y
   . ElemOf '(q, eff) l
  -> t x
  -> (x -> q y)
  -> Sem (eff ': HandlingMeta metaeff t r l ': r) (t y)
metaProcessorUsing =
  \pr t ex -> join $ sendUsing (There Here) (ProcessMeta pr t ex)
{-# INLINE metaProcessorUsing #-}

metaProcessorUsing'
  :: forall q eff metaeff t r l x y
   . ElemOf '(q, eff) l
  -> t x
  -> (x -> q y)
  -> Sem (eff ': Meta metaeff ': HandlingMeta metaeff t r l ': r) (t y)
metaProcessorUsing' =
  \pr t ex -> join $ sendUsing (There (There Here)) (ProcessMeta' pr t ex)
{-# INLINE metaProcessorUsing' #-}

processMetaUsing :: forall r eff q metaeff z t rH rC l a mh
                  . mh ~ HandlingMeta metaeff t rH l
                 => ElemOf '(q, eff) l
                 -> q a
                 -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
                        (Sem (eff ': mh ': rH) (t a))
processMetaUsing pr q = do
  ProcessorMetaUsing prcs <- getProcessorMetaUsing
  t <- getStateH
  return $ prcs pr t (\_ -> q)

processMetaUsing' :: forall r eff q metaeff z t rH rC l a mh
                   . mh ~ HandlingMeta metaeff t rH l
                  => ElemOf '(q, eff) l
                  -> q a
                  -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
                         (Sem (eff ': Meta metaeff ': mh ': rH) (t a))
processMetaUsing' pr q = do
  ProcessorMetaUsing prcs <- getProcessorMetaUsing'
  t <- getStateH
  return $ prcs pr t (\_ -> q)

runMeta :: forall r eff q metaeff z t rH rC l a b mh
         . (DepMember eff q l, mh ~ HandlingMeta metaeff t rH l)
        => (Sem (eff ': mh ': rH) (t a) -> Sem rC (t b))
        -> q a
        -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runMeta = runMetaUsing depMembership
{-# INLINEABLE runMeta #-}

runMetaUsing :: forall r eff q metaeff z t rH rC l a b mh
              . mh ~ HandlingMeta metaeff t rH l
             => ElemOf '(q, eff) l
             -> (Sem (eff ': mh ': rH) (t a) -> Sem rC (t b))
             -> q a
             -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runMetaUsing pr interp = runExposeMetaUsing pr interp >=> restoreH
{-# INLINEABLE runMetaUsing #-}

runMeta' :: forall r eff q metaeff z t rH rC l a b mh
          . (DepMember eff q l , mh ~ HandlingMeta metaeff t rH l)
         => (Sem (eff ': Meta metaeff ': mh ': rH) (t a) -> Sem rC (t b))
         -> q a
         -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runMeta' = runMetaUsing' depMembership
{-# INLINEABLE runMeta' #-}

runMetaUsing' :: forall r eff q metaeff z t rH rC l a b mh
               . mh ~ HandlingMeta metaeff t rH l
              => ElemOf '(q, eff) l
              -> (Sem (eff ': Meta metaeff ': mh ': rH) (t a) -> Sem rC (t b))
              -> q a
              -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runMetaUsing' pr interp = runExposeMetaUsing' pr interp >=> restoreH
{-# INLINEABLE runMetaUsing' #-}

runExposeMeta :: forall r eff q metaeff z t rH rC l a b mh
               . (DepMember eff q l, mh ~ HandlingMeta metaeff t rH l)
              => (Sem (eff ': mh ': rH) (t a) -> Sem rC b)
              -> q a
              -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runExposeMeta = runExposeMetaUsing depMembership
{-# INLINEABLE runExposeMeta #-}

runExposeMeta' :: forall r eff q metaeff z t rH rC l a b mh
                . (DepMember eff q l, mh ~ HandlingMeta metaeff t rH l)
               => (Sem (eff ': Meta metaeff ': mh ': rH) (t a) -> Sem rC b)
               -> q a
               -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runExposeMeta' = runExposeMetaUsing' depMembership
{-# INLINEABLE runExposeMeta' #-}

runExposeMetaUsing :: forall r eff q metaeff z t rH rC l a b mh
                    . mh ~ HandlingMeta metaeff t rH l
                   => ElemOf '(q, eff) l
                   -> (Sem (eff ': mh ': rH) (t a) -> Sem rC b)
                   -> q a
                   -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runExposeMetaUsing pr interp = processMetaUsing pr >=> embedH . interp
{-# INLINEABLE runExposeMetaUsing #-}

runExposeMetaUsing' :: forall r metaeff eff q z t rH rC l a b mh
                     . mh ~ HandlingMeta metaeff t rH l
                    => ElemOf '(q, eff) l
                    -> (Sem (eff ': Meta metaeff ': mh ': rH) (t a) -> Sem rC b)
                    -> q a
                    -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runExposeMetaUsing' pr interp = processMetaUsing' pr >=> embedH . interp
{-# INLINEABLE runExposeMetaUsing' #-}

type MetaHandler metaeff r =
   (   forall l t z x mh
     . (Traversable t, mh ~ HandlingMeta metaeff t r l)
    => metaeff l z x
    -> Sem (HigherOrder z t (Meta metaeff) (mh ': r) (mh ': r) ': mh ': r) x
   )

exposeMetaRun :: forall eff metaeffect t rH l r a
               . ElemOf (HandlingMeta metaeffect t rH l) r
              -> Unique -> Sem r a -> Sem (eff ': r) a
exposeMetaRun pr uniq = go
  where
    go :: forall x. Sem r x -> Sem (eff ': r) x
    go = throughSem $ \k (Union pr' wav) c ->
      case sameMember pr pr' of
        Just Refl ->
          let u' = wav & rewriteWeaving' \case
                HandlingMetaMetaRun (MetaRun uniq' act)
                  | uniq' == uniq -> Bundle Here (unsafeCoerce act)
                handlingmeta -> Bundle (There pr) handlingmeta
          in
            k (hoist go_ u') c
        _ -> k (hoist go_ (Union (There pr') wav)) c
    {-# INLINE go #-}

    go_ :: forall x. Sem r x -> Sem (eff ': r) x
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINE exposeMetaRun #-}

interpretMeta
  :: forall metaeff r
   . MetaHandler metaeff r
  -> InterpreterFor (Meta metaeff) r
interpretMeta h =
    interpretFast \case
      MetaRun q _ ->
        errorWithoutStackTrace $
          "Unhandled MetaRun with unique hash " ++ show (hashUnique q)
  . go
  . raiseUnder
  where
    go :: InterpreterFor (Meta metaeff) (MetaRun ': r)
    go = throughSem $ \k u c -> case decomp u of
      Left g -> k (hoist go_ g) c
      Right (Sent (MetaMetaRun metarun) n) ->
        k (Union Here $ Sent metarun (go_ . n)) c
      Right (Weaved (MetaMetaRun metarun) trav mkS wv lwr ex) ->
        k (Union Here $ Weaved metarun trav mkS (go_ . wv) lwr ex) c
      Right (Sent (SendMeta (metaeff :: metaeff l z _x) to1 to2) n) ->
        let
          handleHandlingMetaSpecific
            :: forall q x. HandlingMeta metaeff Identity r l q x -> x
          handleHandlingMetaSpecific = \case
            ProcessMeta pr (Identity x) ex -> do
              uniq <- newUniqueSem
              n (to2 uniq pr (ex x))
                & go_
                & rewrite HandlingMetaMetaRun
                & exposeMetaRun Here uniq
                &# fmap Identity
            ProcessMeta' pr (Identity x) ex -> do
              uniq <- newUniqueSem
              n (to2 uniq pr (ex x))
                & metaRunIntoHandlingMeta
                & exposeMetaRun (There Here) uniq
                &# fmap Identity
            _ -> errorWithoutStackTrace
                  "handleHandlingMetaSpecific: not specially handled "
          {-# INLINE handleHandlingMetaSpecific #-}

          goSent :: forall rC x mh
                  . mh ~ HandlingMeta metaeff Identity r l
                 => Sem (HigherOrder z Identity (Meta metaeff)
                          (mh ': r) rC ': rC) x
                 -> Sem rC x
          goSent = throughSem $ \k' u' c' -> case decomp u' of
            Right wav -> fromFOEff wav $ \ex' -> \case
              GetInterpreterH -> c' $ ex' $
                InterpreterH (rewrite HandlingMetaMetaRun
                              . go_
                              . handlingMetaToMeta handleHandlingMetaSpecific)
              GetProcessorH -> c' $ ex' $
                ProcessorH $ \(Identity t) fz ->
                  (fmap Identity #. metaToHandlingMeta . n . to1 . fz) t
              RestoreH (Identity a) -> c' $ ex' a
              LiftWithH main -> c' $ ex' $ main $ fmap Identity #. goSent_
              EmbedH m' -> runSem m' k' (c' . ex')
              GetStateH -> c' $ ex' $ Identity ()
              PropagateH pr e' n' ->
                k' (Union pr (Sent e' (fmap runIdentity #. n' id .# Identity)))
                   (c' . ex')
            Left g -> k' (hoist goSent_ g) c'
          {-# INLINE goSent #-}

          goSent_ :: forall rC x mh
                   . mh ~ HandlingMeta metaeff Identity r l
                  => Sem (HigherOrder z Identity (Meta metaeff)
                           (mh ': r) rC ': rC) x
                  -> Sem rC x
          goSent_ = goSent
          {-# NOINLINE goSent_ #-}

        in
          runSem (handlingMetaIntoMetaRun handleHandlingMetaSpecific
                    (goSent (h metaeff))) k c
      Right (Weaved (SendMeta (metaeff :: metaeff l z _x) to1 to2)
              (trav :: Traversal t) _ wv lwr ex) ->
        reify trav $ \(_ :: pr s) ->
          let
            handleHandlingMetaSpecific
              :: forall q x
               . HandlingMeta metaeff (ViaTraversal s t) r l q x -> x
            handleHandlingMetaSpecific = \case
              ProcessMeta pr t ex' -> do
                uniq <- newUniqueSem
                wv (getViaTraversal (fmap (to2 uniq pr . ex') t))
                  & go_
                  & rewrite HandlingMetaMetaRun
                  & exposeMetaRun Here uniq
                  &# fmap ViaTraversal
              ProcessMeta' pr t ex' -> do
                uniq <- newUniqueSem
                wv (getViaTraversal (fmap (to2 uniq pr . ex') t))
                  & metaRunIntoHandlingMeta
                  & exposeMetaRun (There Here) uniq
                  &# fmap ViaTraversal
              _ -> errorWithoutStackTrace
                    "handleHandlingMetaSpecific: not specially handled "
            {-# INLINE handleHandlingMetaSpecific #-}

            goWeaved :: forall rC x mh
                    . mh ~ HandlingMeta metaeff (ViaTraversal s t) r l
                   => Sem (HigherOrder z (ViaTraversal s t) (Meta metaeff)
                            (mh ': r) rC ': rC) x
                   -> Sem (Weave t rC ': rC) x
            goWeaved = throughSem $ \k' u' c' -> case decompCoerce u' of
              Right wav -> fromFOEff wav $ \ex' -> \case
                GetInterpreterH -> c' $ ex' $
                  InterpreterH (rewrite HandlingMetaMetaRun
                                . go_
                                . handlingMetaToMeta handleHandlingMetaSpecific)
                GetProcessorH ->
                    c' $ ex' $ ProcessorH $ \t fz ->
                      (fmap ViaTraversal
                       #. metaToHandlingMeta
                       . wv
                       .# getViaTraversal) (fmap (to1 . fz) t)
                RestoreH (ViaTraversal t) ->
                  k' (injUsing Here (RestoreW t)) (c' . ex')
                LiftWithH main ->
                  (`k'` c') $ injUsing Here $ LiftWithW $ \lwr' ->
                    ex' $ main $ (fmap ViaTraversal #. lwr' . goWeaved_)
                EmbedH m' -> k' (injUsing Here $ EmbedW m') (c' . ex')
                GetStateH ->
                  k' (injUsing Here (GetStateW (\w -> ViaTraversal (w ()))))
                     (c' . ex')
                PropagateH pr e' n ->
                  (`k'` id) $ injUsing Here $ GetStateW $ \mkS' ->
                  (`k'` id) $ injUsing Here $ LiftWithW $ \lwr' ->
                  k' (injUsing Here (
                         EmbedW $ liftSem $ Union pr
                         $ Weaved e' trav mkS'
                            (fmap getViaTraversal #. n id .# ViaTraversal)
                            lwr'
                            id)) $ \ta ->
                  k' (injUsing Here $ RestoreW ta) (c' . ex')
              Left g -> k' (hoist goWeaved_ g) c'
            {-# INLINE goWeaved #-}

            goWeaved_ :: forall rC x mh
                       . mh ~ HandlingMeta metaeff (ViaTraversal s t) r l
                      => Sem (HigherOrder z (ViaTraversal s t) (Meta metaeff)
                               (mh ': r) rC ': rC) x
                      -> Sem (Weave t rC ': rC) x
            goWeaved_ = goWeaved
            {-# NOINLINE goWeaved_ #-}
          in
            runSem (handlingMetaIntoMetaRun handleHandlingMetaSpecific
                      (lwr (goWeaved (h metaeff)))) k (c . ex)
    {-# INLINE go #-}

    go_ :: InterpreterFor (Meta metaeff) (MetaRun ': r)
    go_ = go
    {-# NOINLINE go_ #-}

    metaRunIntoHandlingMeta
      :: forall meta t r' l y
       . Sem (meta ': MetaRun ': r') y
      -> Sem (meta ': HandlingMeta metaeff t r l ': r') y
    metaRunIntoHandlingMeta = throughSem $ \k (Union pr wav) c ->
      case pr of
        Here -> k (hoist metaRunIntoHandlingMeta_ (Union Here wav)) c
        There Here ->
          k (hoist metaRunIntoHandlingMeta_
              (Union (There Here) (rewriteWeaving HandlingMetaMetaRun wav))) c
        There (There pr') ->
          k (hoist metaRunIntoHandlingMeta_ (Union (There (There pr')) wav)) c
    {-# INLINE metaRunIntoHandlingMeta #-}

    metaRunIntoHandlingMeta_
      :: forall meta t r' l y
       . Sem (meta ': MetaRun ': r') y
      -> Sem (meta ': HandlingMeta metaeff t r l ': r') y
    metaRunIntoHandlingMeta_ = metaRunIntoHandlingMeta
    {-# NOINLINE metaRunIntoHandlingMeta_#-}


    metaToHandlingMeta
      :: forall t r' l y
       . Sem (Meta metaeff ': MetaRun ': r') y
      -> Sem (Meta metaeff ': HandlingMeta metaeff t r l ': r') y
    metaToHandlingMeta = goMTHM
      where
        goMTHM :: forall y'
                . Sem (Meta metaeff ': MetaRun ': r') y'
               -> Sem (Meta metaeff ': HandlingMeta metaeff t r l ': r') y'
        goMTHM = throughSem $ \k u c -> case u of
          Union Here (Sent (MetaMetaRun metarun) n) ->
            k (Union (There Here)
                (Sent (HandlingMetaMetaRun metarun) (goMTHM_ . n))) c
          Union Here (Weaved (MetaMetaRun metarun) trav mkS wv lwr ex) ->
            k (Union (There Here)
                (Weaved (HandlingMetaMetaRun metarun)
                  trav mkS (goMTHM . wv) lwr ex)) c
          Union Here wav -> k (hoist goMTHM_ (Union Here wav)) c
          Union (There Here) (Sent metarun n) ->
            k (Union (There Here)
                (Sent (HandlingMetaMetaRun metarun) (goMTHM_ . n))) c
          Union (There Here) (Weaved metarun trav mkS wv lwr ex) ->
            k (Union (There Here)
                (Weaved (HandlingMetaMetaRun metarun)
                  trav mkS (goMTHM_ . wv) lwr ex)) c
          Union (There (There pr)) wav ->
            k (hoist goMTHM_ (Union (There (There pr)) wav)) c
        {-# INLINE goMTHM #-}

        goMTHM_ :: forall y'
                . Sem (Meta metaeff ': MetaRun ': r') y'
               -> Sem (Meta metaeff ': HandlingMeta metaeff t r l ': r') y'
        goMTHM_ = goMTHM
        {-# NOINLINE goMTHM_ #-}
    {-# INLINE metaToHandlingMeta #-}

    handlingMetaToMeta
      :: forall t meta r' l x
       . (forall q y. HandlingMeta metaeff t r l q y -> y)
      -> Sem (meta ': HandlingMeta metaeff t r l ': r') x
      -> Sem (meta ': MetaRun ': r') x
    handlingMetaToMeta specific = goHMTM
      where
        goHMTM :: forall y
                . Sem (meta ': HandlingMeta metaeff t r l ': r') y
               -> Sem (meta ': MetaRun ': r') y
        goHMTM = throughSem $ \k u c ->
          case u of
            Union Here wav -> k (hoist goHMTM_ (Union Here wav)) c
            Union (There Here) wav -> case wav of
              Sent (HandlingMetaMetaRun metarun) n ->
                k (Union (There Here) (Sent metarun (goHMTM_ . n))) c
              Weaved (HandlingMetaMetaRun metarun) trav mkS wv lwr ex ->
                k (Union (There Here) (Weaved metarun
                                trav mkS (goHMTM_ . wv) lwr ex)) c
              _ -> fromFOEff wav $ \ex e ->
                let !x' = specific e in c (ex x')
            Union (There (There pr)) wav ->
              k (hoist goHMTM_ (Union (There (There pr)) wav)) c
        {-# INLINE goHMTM #-}

        goHMTM_ :: forall y
                 . Sem (meta ': HandlingMeta metaeff t r l ': r') y
                -> Sem (meta ': MetaRun ': r') y
        goHMTM_ = goHMTM
        {-# NOINLINE goHMTM_ #-}
    {-# INLINE handlingMetaToMeta #-}

    handlingMetaIntoMetaRun
      :: forall t l r' x
       . (forall q y. HandlingMeta metaeff t r l q y -> y)
      -> Sem (HandlingMeta metaeff t r l ': r') x
      -> Sem (MetaRun ': r') x
    handlingMetaIntoMetaRun specific = goHMIMR
      where
        goHMIMR
          :: Sem (HandlingMeta metaeff t r l ': r') y
          -> Sem (MetaRun ': r') y
        goHMIMR = throughSem $ \k u c ->
          case decompCoerce u of
            Left g -> k (hoist goHMIMR_ g) c
            Right wav -> case wav of
              Sent (HandlingMetaMetaRun metarun) n ->
                k (Union Here (Sent metarun (goHMIMR_ . n))) c
              Weaved (HandlingMetaMetaRun metarun) trav mkS wv lwr ex ->
                k (Union Here (Weaved metarun
                                trav mkS (goHMIMR_ . wv) lwr ex)) c
              _ -> fromFOEff wav $ \ex e ->
                let !x' = specific e in c (ex x')
        {-# INLINE goHMIMR #-}

        goHMIMR_
          :: forall y
           . Sem (HandlingMeta metaeff t r l ': r') y
          -> Sem (MetaRun ': r') y
        goHMIMR_ = goHMIMR
        {-# NOINLINE goHMIMR_ #-}
    {-# INLINE handlingMetaIntoMetaRun #-}

reinterpretMeta
  :: forall metaeff e2 r
   . MetaHandler metaeff (e2 ': r)
  -> (forall x. Sem (Meta metaeff ': r) x -> Sem (e2 ': r) x)
reinterpretMeta h = interpretMeta h . raiseUnder
{-# INLINE reinterpretMeta #-}

reinterpretMeta2
  :: forall metaeff e2 e3 r
   . MetaHandler metaeff (e2 ': e3 ': r)
  -> (forall x. Sem (Meta metaeff ': r) x -> Sem (e2 ': e3 ': r) x)
reinterpretMeta2 h = interpretMeta h . raise2Under
{-# INLINE reinterpretMeta2 #-}

reinterpretMeta3
  :: forall metaeff e2 e3 e4 r
   . MetaHandler metaeff (e2 ': e3 ': e4 ': r)
  -> (forall x. Sem (Meta metaeff ': r) x -> Sem (e2 ': e3 ': e4 ': r) x)
reinterpretMeta3 h = interpretMeta h . raise3Under
{-# INLINE reinterpretMeta3 #-}
