{-# language AllowAmbiguousTypes, BangPatterns, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances, FunctionalDependencies, UndecidableInstances #-}

-- | Description: The meta-effect 'Meta'
module Polysemy.Meta (
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
  getProcessorMetaUsing,
  getProcessorMetaUsing',

  -- * Auxiliary type classes
  DepMember,
  AllSemRaises,
  ) where

import Polysemy.Internal.Meta
