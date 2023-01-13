-- | Description: The meta-effect 'Meta'
module Polysemy.Meta.Flexible (
  -- * Effect
  Meta,
  MetaEffect,
  (:%),
  mkIntoMeta,

  -- * Actions
  sendMeta,
  sendMetaUsing,

  -- ** Last-resort actions
  sendMetaVia,
  sendMetaViaUsing,

  -- * Interpreters
  interpretMeta,
  reinterpretMeta,
  reinterpretMeta2,
  reinterpretMeta3,
  metaToMeta,
  metaToMetaUsing,
  metaIntoMeta,

  -- * 'interpretMeta' Combinators
  HandlingMeta,
  runMeta,
  runMeta',
  runExposeMeta,
  runExposeMeta',
  getProcessorMeta,
  getProcessorMeta',

  -- ** Last-resort 'interpretMeta' combinators
  runMetaUsing,
  runMetaUsing',
  runExposeMetaUsing,
  runExposeMetaUsing',
  processMetaUsing,
  processMetaUsing',

  -- * Auxiliary type classes
  DepMember,
  AllSemRaises,
  ) where

import Control.Monad
import Polysemy hiding (runH, runH')
import Polysemy.Membership
import Polysemy.HigherOrder.Flexible
import Polysemy.Internal.Meta hiding (
  runMeta,
  runMeta',
  runExposeMeta,
  runExposeMeta',
  runMetaUsing,
  runMetaUsing',
  runExposeMetaUsing,
  runExposeMetaUsing',
  )

runMeta :: forall r eff q metaeff z t rH rC l a mh
         . ( DepMember eff q l, Raise (mh ': rH) r
           , mh ~ HandlingMeta metaeff t rH l)
        => q a
        -> Sem (eff
                ': HigherOrder z t (Meta metaeff) (mh ': rH) rC
                ': r) a
runMeta = runMetaUsing depMembership

runMetaUsing :: forall r eff q metaeff z t rH rC l a mh
              . (Raise (mh ': rH) r, mh ~ HandlingMeta metaeff t rH l)
             => ElemOf '(q, eff) l
             -> q a
             -> Sem (eff
                     ': HigherOrder z t (Meta metaeff) (mh ': rH) rC
                     ': r) a
runMetaUsing pr = runExposeMetaUsing pr >=> raise . restoreH

runMeta' :: forall r eff q metaeff z t rH rC l a mh
          . (DepMember eff q l, Raise (mh ': rH) r,
             mh ~ HandlingMeta metaeff t rH l)
         => q a
         -> Sem (eff
                 ': Meta metaeff
                 ': HigherOrder z t (Meta metaeff) (mh ': rH) rC
                 ': r) a
runMeta' = runMetaUsing' depMembership

runMetaUsing' :: forall r eff q metaeff z t rH rC l a mh
               . (Raise (mh ': rH) r, mh ~ HandlingMeta metaeff t rH l)
              => ElemOf '(q, eff) l
              -> q a
              -> Sem (eff
                      ': Meta metaeff
                      ': HigherOrder z t (Meta metaeff) (mh ': rH) rC
                      ': r) a
runMetaUsing' pr = runExposeMetaUsing' pr >=> raise . raise . restoreH

runExposeMeta :: forall r eff q metaeff z t rH rC l a mh
               . (DepMember eff q l, Raise (mh ': rH) r,
                  mh ~ HandlingMeta metaeff t rH l)
              => q a
              -> Sem (eff
                      ': HigherOrder z t (Meta metaeff) (mh ': rH) rC
                      ': r) (t a)
runExposeMeta = runExposeMetaUsing depMembership

runExposeMeta' :: forall r eff q metaeff z t rH rC l a mh
                . (DepMember eff q l, Raise (mh ': rH) r,
                  mh ~ HandlingMeta metaeff t rH l)
               => q a
               -> Sem (eff
                       ': Meta metaeff
                       ': HigherOrder z t (Meta metaeff) (mh ': rH) rC
                       ': r) (t a)
runExposeMeta' = runExposeMetaUsing' depMembership

runExposeMetaUsing :: forall r eff q metaeff z t rH rC l a mh
                    . (Raise (mh ': rH) r, mh ~ HandlingMeta metaeff t rH l)
                   => ElemOf '(q, eff) l
                   -> q a
                   -> Sem (eff
                           ': HigherOrder z t (Meta metaeff) (mh ': rH) rC
                           ': r) (t a)
runExposeMetaUsing pr = raise . processMetaUsing pr >=> mapMembership \case
  Here -> Here
  There pr' -> There $ There $ raiseMembership @(mh ': rH) @r pr'

runExposeMetaUsing' :: forall r metaeff eff q z t rH rC l a mh
                    . (Raise (mh ': rH) r, mh ~ HandlingMeta metaeff t rH l)
                    => ElemOf '(q, eff) l
                    -> q a
                    -> Sem (eff
                            ': Meta metaeff
                            ': HigherOrder z t (Meta metaeff) (mh ': rH) rC
                            ': r) (t a)
runExposeMetaUsing' pr =
  raise . raise . processMetaUsing' pr >=> mapMembership \case
    Here -> Here
    There Here -> There Here
    There (There pr') -> There $ There $ There $ raiseMembership @(mh ': rH) @r pr'
