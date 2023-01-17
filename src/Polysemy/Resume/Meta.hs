module Polysemy.Resume.Meta (
  -- * Effect
  Resumable,

  -- * Actions
  resume,

  -- * Interpretations
  runResumableBase,
  ) where

import Polysemy
import Polysemy.HigherOrder
import Polysemy.Meta
import Polysemy.Membership
import Polysemy.Opaque
import Polysemy.Newtype
import Polysemy.Internal.Utils

data ResumableMeta err eff :: MetaEffect where
  ResumableMeta :: z a
                -> ResumableMeta err eff '[z :% eff] m (Either err a)

newtype Resumable err eff m a =
  Resumable (Meta (ResumableMeta err eff) m a)

resume :: forall err eff r a
        . Member (Resumable err eff) r
       => Sem (eff ': r) a -> (err -> Sem r a) -> Sem r a
resume m h =
  ResumableMeta (raiseUnder m)
  & sendMetaUsing Here
  & subsumeCoerce @(Resumable err eff)
  >>= either h return

runResumableBase :: forall err eff r
               . (   forall q x
                   . Sem (eff ': Opaque q ': r) x
                  -> Sem (Opaque q ': r) (Either err x)
                 )
              -> InterpreterFor (Resumable err eff) r
runResumableBase interp =
  coerceEff
  >>> interpretMeta @(ResumableMeta err eff) \case
    ResumableMeta m ->
      runExposeMeta
        (toOpaqueAt @'[_]
         >>> interp
         >>> fromOpaque
         ) m >>= \case
        Left e -> return (Left e)
        Right ta -> Right <$> restoreH ta
