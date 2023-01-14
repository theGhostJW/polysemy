{-# OPTIONS_HADDOCK not-home #-}
{-# LANGUAGE AllowAmbiguousTypes, BangPatterns, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FunctionalDependencies, UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving  #-}

module Polysemy.Internal.Meta where

import Control.Monad

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
  proveSemRaise :: forall eff z. ElemOf '(z, eff) l -> z :~: Sem (eff ': r)

instance AllSemRaises '[] r where
  proveSemRaise = absurdMembership

instance (t ~ '(Sem (eff ': r), eff), AllSemRaises l' r)
      => AllSemRaises (t ': l') r where
  proveSemRaise Here = Refl
  proveSemRaise (There pr) = proveSemRaise pr

sendMeta :: forall metaeff l r a
          . (Member (Meta metaeff) r, AllSemRaises l r)
         => metaeff l (Sem r) a
         -> Sem r a
sendMeta = sendMetaUsing membership

sendMetaUsing :: forall metaeff l r a
               . AllSemRaises l r
              => ElemOf (Meta metaeff) r
              -> metaeff l (Sem r) a
              -> Sem r a
sendMetaUsing pr = sendMetaViaUsing pr
                    id
                    (\pr' -> case proveSemRaise @l @r pr' of Refl -> id)

sendMetaVia :: forall metaeff l m r a
             . Member (Meta metaeff) r
            => (forall x. m x -> Sem r x)
            -> (forall eff z x. ElemOf '(z, eff) l -> z x -> Sem (eff ': r) x)
            -> metaeff l m a
            -> Sem r a
sendMetaVia = sendMetaViaUsing membership

sendMetaViaUsing :: forall metaeff l m r a
                  . ElemOf (Meta metaeff) r
                 -> (forall x. m x -> Sem r x)
                 -> (forall eff z x. ElemOf '(z, eff) l -> z x -> Sem (eff ': r) x)
                 -> metaeff l m a
                 -> Sem r a
sendMetaViaUsing pr to1 to2 p = sendUsing pr $ SendMeta p to1 $ \uniq pr' ->
  transformUsing pr (MetaMetaRun @metaeff . MetaRun uniq) . to2 pr'

metaToMeta ::
  ∀ metaeff0 metaeff1 r.
  Member (Meta metaeff1) r =>
  (forall l m x. metaeff0 l m x -> metaeff1 l m x) ->
  InterpreterFor (Meta metaeff0) r
metaToMeta = metaToMetaUsing membership

metaToMetaUsing ::
  ∀ metaeff0 metaeff1 r.
  ElemOf (Meta metaeff1) r ->
  (forall l m x. metaeff0 l m x -> metaeff1 l m x) ->
  InterpreterFor (Meta metaeff0) r
metaToMetaUsing pr n = transformUsing pr \case
  MetaMetaRun metarun -> MetaMetaRun metarun
  SendMeta metaeff to1 to2 -> SendMeta (n metaeff) to1 to2

metaIntoMeta ::
  ∀ metaeff0 metaeff1 r.
  (forall l m x. metaeff0 l m x -> metaeff1 l m x) ->
  (forall x. Sem (Meta metaeff0 ': r) x -> Sem (Meta metaeff1 ': r) x)
metaIntoMeta n = rewrite \case
  MetaMetaRun metarun -> MetaMetaRun metarun
  SendMeta metaeff to1 to2 -> SendMeta (n metaeff) to1 to2

mkIntoMeta :: ∀ metaeff m x. metaeff '[] m x -> Meta metaeff m x
mkIntoMeta e = SendMeta e id (\_ u _ -> absurdMembership u)

data HandlingMeta metaeffect t rH l :: Effect where
  HandlingMetaMetaRun
    :: forall metaeffect t rH l m a
     . MetaRun m a -> HandlingMeta metaeffect t rH l m a
  ProcessMeta
    :: forall eff z metaeffect t rH l m a b
     . Unique
    -> ElemOf '(z, eff) l
    -> t a
    -> (a -> z b)
    -> HandlingMeta metaeffect t rH l m
        (Sem (Meta metaeffect ': HandlingMeta metaeffect t rH l ': rH) (t b))

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

exposeMetaRun :: forall eff metaeffect t rH l r a
               . ElemOf (HandlingMeta metaeffect t rH l) r
              -> Unique -> Sem r a -> Sem (eff ': r) a
exposeMetaRun pr uniq =
  raise
  >>> interceptUsingH (There pr) \case
        HandlingMetaMetaRun (MetaRun uniq' act)
          | uniq' == uniq -> propagateUsing Here (unsafeCoerce act)
        metarun -> propagateUsing (There pr) metarun

getProcessorMetaUsing
  :: forall r eff q metaeff z t rH rC l mh
   . mh ~ HandlingMeta metaeff t rH l
  => ElemOf '(q, eff) l
  -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
         (ProcessorH q t eff (mh ': rH))
getProcessorMetaUsing pr = do
  InterpreterH interp <- getInterpreterH
  return $ ProcessorH $ \t ex -> do
    -- TODO: create the unique inside or outside the processor?
    -- I'm not sure. Inside is guaranteed safe, though.
    uniq <- newUniqueSem
    m <- sendUsing (There Here) (ProcessMeta uniq pr t ex)
    exposeMetaRun Here uniq (interp m)

getProcessorMetaUsing'
  :: forall r eff q metaeff z t rH rC l mh
   . mh ~ HandlingMeta metaeff t rH l
  => ElemOf '(q, eff) l
  -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
         (ProcessorH q t eff (Meta metaeff ': mh ': rH))
getProcessorMetaUsing' pr = do
  return $ ProcessorH $ \t ex -> do
    uniq <- newUniqueSem
    m <- sendUsing (There (There Here)) (ProcessMeta uniq pr t ex)
    exposeMetaRun (There Here) uniq m

getProcessorMeta
  :: forall r eff q metaeff z t rH rC l mh
   . (DepMember eff q l, mh ~ HandlingMeta metaeff t rH l)
  => Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
         (ProcessorH q t eff (mh ': rH))
getProcessorMeta = getProcessorMetaUsing depMembership

getProcessorMeta'
  :: forall r eff q metaeff z t rH rC l mh
   . (DepMember eff q l, mh ~ HandlingMeta metaeff t rH l)
  => Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
         (ProcessorH q t eff (Meta metaeff ': mh ': rH))
getProcessorMeta' = getProcessorMetaUsing' depMembership

processMetaUsing :: forall r eff q metaeff z t rH rC l a mh
                  . mh ~ HandlingMeta metaeff t rH l
                 => ElemOf '(q, eff) l
                 -> q a
                 -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
                        (Sem (eff ': mh ': rH) (t a))
processMetaUsing pr q = do
  ProcessorH prcs <- getProcessorMetaUsing pr
  t <- getStateH
  return $ prcs t (\_ -> q)

processMetaUsing' :: forall r eff q metaeff z t rH rC l a mh
                   . mh ~ HandlingMeta metaeff t rH l
                  => ElemOf '(q, eff) l
                  -> q a
                  -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
                         (Sem (eff ': Meta metaeff ': mh ': rH) (t a))
processMetaUsing' pr q = do
  ProcessorH prcs <- getProcessorMetaUsing' pr
  t <- getStateH
  return $ prcs t (\_ -> q)

runMeta :: forall r eff q metaeff z t rH rC l a b mh
         . (DepMember eff q l , mh ~ HandlingMeta metaeff t rH l)
        => (Sem (eff ': mh ': rH) (t a) -> Sem rC (t b))
        -> q a
        -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runMeta = runMetaUsing depMembership

runMetaUsing :: forall r eff q metaeff z t rH rC l a b mh
              . mh ~ HandlingMeta metaeff t rH l
             => ElemOf '(q, eff) l
             -> (Sem (eff ': mh ': rH) (t a) -> Sem rC (t b))
             -> q a
             -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runMetaUsing pr interp = runExposeMetaUsing pr interp >=> restoreH

runMeta' :: forall r eff q metaeff z t rH rC l a b mh
          . (DepMember eff q l , mh ~ HandlingMeta metaeff t rH l)
         => (Sem (eff ': Meta metaeff ': mh ': rH) (t a) -> Sem rC (t b))
         -> q a
         -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runMeta' = runMetaUsing' depMembership

runMetaUsing' :: forall r eff q metaeff z t rH rC l a b mh
               . mh ~ HandlingMeta metaeff t rH l
              => ElemOf '(q, eff) l
              -> (Sem (eff ': Meta metaeff ': mh ': rH) (t a) -> Sem rC (t b))
              -> q a
              -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runMetaUsing' pr interp = runExposeMetaUsing' pr interp >=> restoreH

runExposeMeta :: forall r eff q metaeff z t rH rC l a b mh
               . (DepMember eff q l, mh ~ HandlingMeta metaeff t rH l)
              => (Sem (eff ': mh ': rH) (t a) -> Sem rC b)
              -> q a
              -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runExposeMeta = runExposeMetaUsing depMembership

runExposeMeta' :: forall r eff q metaeff z t rH rC l a b mh
                . (DepMember eff q l, mh ~ HandlingMeta metaeff t rH l)
               => (Sem (eff ': Meta metaeff ': mh ': rH) (t a) -> Sem rC b)
               -> q a
               -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runExposeMeta' = runExposeMetaUsing' depMembership

runExposeMetaUsing :: forall r eff q metaeff z t rH rC l a b mh
                    . mh ~ HandlingMeta metaeff t rH l
                   => ElemOf '(q, eff) l
                   -> (Sem (eff ': mh ': rH) (t a) -> Sem rC b)
                   -> q a
                   -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runExposeMetaUsing pr interp = processMetaUsing pr >=> embedH . interp

runExposeMetaUsing' :: forall r metaeff eff q z t rH rC l a b mh
                     . mh ~ HandlingMeta metaeff t rH l
                    => ElemOf '(q, eff) l
                    -> (Sem (eff ': Meta metaeff ': mh ': rH) (t a) -> Sem rC b)
                    -> q a
                    -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runExposeMetaUsing' pr interp = processMetaUsing' pr >=> embedH . interp

type MetaHandler metaeff r =
   (   forall l t z x mh
     . (Traversable t, mh ~ HandlingMeta metaeff t r l)
    => metaeff l z x
    -> Sem (HigherOrder z t (Meta metaeff) (mh ': r) (mh ': r) ': mh ': r) x
   )

interpretMeta
  :: forall metaeff r
   . MetaHandler metaeff r
  -> InterpreterFor (Meta metaeff) r
interpretMeta h =
    interpretH \case
      MetaRun q _ ->
        errorWithoutStackTrace $
          "Unhandled MetaRun with unique hash " ++ show (hashUnique q)
  . reinterpretH \case
      MetaMetaRun metarun -> propagate metarun
      SendMeta (metaeff :: metaeff l z x) to1 to2 -> do
        ProcessorH processor <- getProcessorH
        (_ :: TypeParamsH k t meta r_ r_) <- getTypeParamsH
        let
          metaRunToHandlingMeta
            :: forall y mh
             . mh ~ HandlingMeta metaeff t r l
            => Sem (meta ': MetaRun ': r) y
            -> Sem (meta ': mh ': r) y
          metaRunToHandlingMeta =
            (raiseUnder2 . raiseUnder2)
            >>> interpretH \case
              MetaMetaRun metarun ->
                propagateUsing (There (There Here)) (HandlingMetaMetaRun metarun)
              sendmeta -> propagate sendmeta
            >>> transformUsing (There Here) HandlingMetaMetaRun

          metaHandlerIntoMetaRun
            :: forall r' y
             . Sem (HandlingMeta metaeff t r l ': r') y
            -> Sem (MetaRun ': r') y
          metaHandlerIntoMetaRun = reinterpretH \case
            HandlingMetaMetaRun metarun -> propagate metarun
            ProcessMeta uniq pr t q -> return $
              processor t ( to2 uniq pr . q)
              & metaRunToHandlingMeta

          metaHandlerToOther
            :: forall r'
             . (forall n y. MetaRun n y -> Bundle r' n y)
            -> InterpreterFor (HandlingMeta metaeff t r l) r'
          metaHandlerToOther toBdl = interpretH \case
            HandlingMetaMetaRun metarun | Bundle pr act <- toBdl metarun ->
              propagateUsing pr act
            ProcessMeta uniq pr t q -> return $
              processor t (to2 uniq pr . q)
              & metaRunToHandlingMeta

          rewriteHigherOrderCommon
            :: forall rA rB r' q y mh
             . mh ~ HandlingMeta metaeff t r l
            => HigherOrder z t meta (mh ': r) rA q y
            -> Sem (HigherOrder k t meta (MetaRun ': r) rB ': r') y
          rewriteHigherOrderCommon = \case
            GetProcessorH -> do
              ProcessorH prcs <- getProcessorH
              return $ ProcessorH $ \t fz ->
                metaRunToHandlingMeta $ prcs t (to1 . fz)
            GetInterpreterH -> do
              InterpreterH interp <- getInterpreterH
              return $ InterpreterH $
                sinkBelow @'[_]
                >>> raiseUnder2
                >>> metaHandlerToOther (Bundle (There Here))
                >>> interp
                >>> rewrite HandlingMetaMetaRun
            LiftWithH main -> liftWithH $ \lwr -> return $
              main (lwr . rewriteHigherOrder)
            RestoreH t -> restoreH t
            GetStateH -> getStateH
            _ -> errorWithoutStackTrace
                  "rewriteHigherOrderCommon: not commonly handled"

          rewriteHigherOrderFirst
            :: forall r' y mh
             . mh ~ HandlingMeta metaeff t r l
            => Sem (HigherOrder z t meta (mh ': r) (mh ': r) ': r') y
            -> Sem (HigherOrder k t meta (MetaRun ': r) (MetaRun ': r) ': r') y
          rewriteHigherOrderFirst = reinterpret \case
            EmbedH m -> embedH (metaHandlerIntoMetaRun m)
            PropagateH Here e n' -> case e of
              HandlingMetaMetaRun metarun ->
                sendUsing Here $
                  PropagateH Here metarun
                    (\ex -> metaHandlerIntoMetaRun . n' ex)
              ProcessMeta uniq pr t q -> return $
                processor t (to2 uniq pr . q)
                & metaRunToHandlingMeta
            PropagateH (There pr) e n' ->
              sendUsing Here $
                PropagateH (There pr) e (\ex -> metaHandlerIntoMetaRun . n' ex)
            e -> rewriteHigherOrderCommon e

          rewriteHigherOrder
            :: forall rC y mh
             . mh ~ HandlingMeta metaeff t r l
            => Sem (HigherOrder z t meta (mh ': r) rC ': rC) y
            -> Sem (HigherOrder k t meta (MetaRun ': r) rC ': rC) y
          rewriteHigherOrder = reinterpret \case
            EmbedH m -> embedH m
            PropagateH n' pr e -> sendUsing Here $ PropagateH n' pr e
            e -> rewriteHigherOrderCommon e

        h metaeff
          & (raiseUnder2 . raiseUnder2)
          & rewriteHigherOrderFirst
          & subsumeUsing (There Here)
          & metaHandlerToOther (Bundle membership)

reinterpretMeta
  :: forall metaeff e2 r
   . MetaHandler metaeff (e2 ': r)
  -> (forall x. Sem (Meta metaeff ': r) x -> Sem (e2 ': r) x)
reinterpretMeta h = interpretMeta h . raiseUnder

reinterpretMeta2
  :: forall metaeff e2 e3 r
   . MetaHandler metaeff (e2 ': e3 ': r)
  -> (forall x. Sem (Meta metaeff ': r) x -> Sem (e2 ': e3 ': r) x)
reinterpretMeta2 h = interpretMeta h . raise2Under

reinterpretMeta3
  :: forall metaeff e2 e3 e4 r
   . MetaHandler metaeff (e2 ': e3 ': e4 ': r)
  -> (forall x. Sem (Meta metaeff ': r) x -> Sem (e2 ': e3 ': e4 ': r) x)
reinterpretMeta3 h = interpretMeta h . raise3Under
