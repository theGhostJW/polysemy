{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | A module you can import to import a rewrite rule that converts usages of
-- 'Polysemy.raise' within the 'Polysemy.HigherOrder' environment to usages of
-- the much more efficient 'Polysemy.embedH'. This causes an inconsistent
-- interaction with 'Polysemy.intercept': you cannot intercept any actions from
-- an action embedded using 'Polysemy.embedH', and so with this module imported
-- that will also impact usages of 'Polysemy.raise' that have been rewritten to
-- 'Polysemy.embedH'.
module Polysemy.HigherOrder.RewriteRule () where

import Polysemy.Internal
import Polysemy.Internal.HigherOrder

{-# RULES
  "raise/embedH" raise = embedH
  #-}
