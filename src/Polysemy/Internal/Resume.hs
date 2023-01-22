module Polysemy.Internal.Resume where
{-
import Polysemy
import Polysemy.Internal.Scoped

data Resumable err eff m a where
  ResumableRun :: forall err eff m a
                . Run eff m a -> Resumable err eff m a
  Resume :: forall err eff m a
          . (Word -> m a) -> Resumable err eff m (Either err a)

resume :: forall err eff r a
        . Member (Resumable err eff) r
       => Sem (eff ': r) a -> (err -> Sem r a) -> Sem r a
resume m h = (>>= either h return) $ send @(Resumable err eff) $ Resume $ \w ->
  transform @(Resumable err eff) (ResumableRun . Run w) m
{-# INLINE resume #-}

-- runResumable :: forall err eff r
--               . (  forall q x
--                   . Sem (eff ': Opaque q ': r) x
--                  -> Sem (Opaque q ': r) (Either err x)
--                 )
--              -> InterpreterFor (Resumable err eff) r
-}
