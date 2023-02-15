module SandboxSTLC where

import STLC

exContext :: Context
exContext = [(Global "T", HasKind Star), (Global "t", HasType (TFree (Global "T")))]

exId :: TermInfer
exId = Ann (Lam (Inf (Bound 0))) (Fun (TFree (Global "T")) (TFree (Global "T")))

exAppl :: TermInfer
exAppl = exId :@: Inf (Free (Global "t"))
