module Sandbox where

-- import STLC

-- exContext :: Context
-- exContext = [(Global "T", HasKind Star), (Global "t", HasType (TFree (Global "T")))]

-- exId :: TermInfer
-- exId = Ann (Lam (iBound 0))) (Fun (TFree (Global "T")) (TFree (Global "T")))

-- exAppl :: TermInfer
-- exAppl = exId :@: iFree (Global "t"))

import DTLC

boolContext :: Context
boolContext =
  [ (Global "Bool", VStar),
    (Global "true", VNeutral (NFree (Global "Bool"))),
    (Global "false", VNeutral (NFree (Global "Bool")))
  ]

lId :: TermInfer
lId =
  Ann
    (Lam (Lam (iBound 0))) -- \_ -> \x -> x
    (iPi iStar (iPi (iBound 0) (iBound 1))) -- % a : * -> % _ : a -> a

idApplication :: TermInfer
idApplication =
  lId
    :@: iFree (Global "Bool")
    :@: iFree (Global "true")

-- | (a : *) -> (_: ((_ : a) -> a)) -> (_ : a) -> a
lNat :: TermInfer
lNat =
  Pi
    iStar
    ( Inf
        ( Pi
            ( Inf
                ( Pi
                    (iBound 0)
                    (iBound 1)
                )
            )
            ( Inf
                ( Pi
                    (iBound 1)
                    (iBound 2)
                )
            )
        )
    )

l0 :: TermInfer
l0 =
  Ann
    (Lam (Lam (Lam (iBound 0))))
    (Inf lNat)

l1 :: TermInfer
l1 =
  Ann
    (Lam (Lam (Lam (Inf (Bound 1 :@: Inf (l0 :@: iBound 2 :@: iBound 1 :@: iBound 0))))))
    (Inf lNat)

l2 :: TermInfer
l2 =
  Ann
    (Lam (Lam (Lam (Inf (Bound 1 :@: Inf (l1 :@: iBound 2 :@: iBound 1 :@: iBound 0))))))
    (Inf lNat)

l3 :: TermInfer
l3 =
  Ann
    (Lam (Lam (Lam (Inf (Bound 1 :@: Inf (l2 :@: iBound 2 :@: iBound 1 :@: iBound 0))))))
    (Inf lNat)

lBool :: TermInfer
lBool =
  Pi
    iStar
    ( iPi
        (iBound 0)
        ( Inf
            ( Pi
                (iBound 1)
                (iBound 2)
            )
        )
    )

lTrue :: TermInfer
lTrue =
  Ann
    (Lam (Lam (Lam (iBound 1))))
    (Inf lBool)

lFalse :: TermInfer
lFalse =
  Ann
    (Lam (Lam (Lam (iBound 0))))
    (Inf lBool)

lIf :: TermInfer
lIf =
  Ann
    (Lam (Lam (Lam (Lam (Inf (Bound 2 :@: iBound 3 :@: iBound 1 :@: iBound 0))))))
    ( iPi
        iStar
        ( iPi
            (Inf lBool)
            ( iPi
                (iBound 1)
                ( iPi
                    (iBound 2)
                    (iBound 3)
                )
            )
        )
    )

lQ :: TermInfer
lQ =
  Ann
    (Lam (Inf (lIf :@: iStar :@: iBound 0 :@: Inf lBool :@: Inf lNat)))
    (iPi (Inf lBool) iStar)

-- | This doesn't work sadly :(
lPair :: TermInfer
lPair =
  Pi iStar (iPi iStar (Lam (Inf (lIf :@: iStar :@: iBound 0 :@: iBound 2 :@: iBound 1))))