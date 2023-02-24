module SandboxEDTLC where

import EDTLC

boolContext :: Context
boolContext =
  [ (Global "Bool", VStar 0),
    (Global "true", VNeutral (NFree (Global "Bool"))),
    (Global "false", VNeutral (NFree (Global "Bool")))
  ]

lId :: TermInfer
lId =
  Ann
    (Lam (Lam (iBound 0))) -- \_ -> \x -> x
    (Pi star0 (Pi (Bound 0) (Bound 1))) -- % a : * -> % _ : a -> a

idApplication :: TermInfer
idApplication =
  lId
    :@: iFree (Global "Bool")
    :@: iFree (Global "true")

-- | (a : *) -> (_: ((_ : a) -> a)) -> (_ : a) -> a
lNat :: TermInfer
lNat =
  Pi
    star0
    ( Pi
        ( Pi
            (Bound 0)
            (Bound 1)
        )
        ( Pi
            (Bound 1)
            (Bound 2)
        )
    )

l0 :: TermInfer
l0 =
  Ann
    (Lam (Lam (Lam (iBound 0))))
    lNat

l1 :: TermInfer
l1 =
  Ann
    (Lam (Lam (Lam (Inf (Bound 1 :@: Inf (l0 :@: iBound 2 :@: iBound 1 :@: iBound 0))))))
    lNat

l2 :: TermInfer
l2 =
  Ann
    (Lam (Lam (Lam (Inf (Bound 1 :@: Inf (l1 :@: iBound 2 :@: iBound 1 :@: iBound 0))))))
    lNat

l3 :: TermInfer
l3 =
  Ann
    (Lam (Lam (Lam (Inf (Bound 1 :@: Inf (l2 :@: iBound 2 :@: iBound 1 :@: iBound 0))))))
    lNat

lBool :: TermInfer
lBool =
  Pi
    star0
    ( Pi
        (Bound 0)
        ( Pi
            (Bound 1)
            (Bound 2)
        )
    )

lTrue :: TermInfer
lTrue =
  Ann
    (Lam (Lam (Lam (iBound 1))))
    lBool

lFalse :: TermInfer
lFalse =
  Ann
    (Lam (Lam (Lam (iBound 0))))
    lBool

lIf :: TermInfer
lIf =
  Ann
    (Lam (Lam (Lam (Lam (Inf (Bound 2 :@: iBound 3 :@: iBound 1 :@: iBound 0))))))
    ( Pi
        star0
        ( Pi
            lBool
            ( Pi
                (Bound 1)
                ( Pi
                    (Bound 2)
                    (Bound 3)
                )
            )
        )
    )

-- lQ :: TermInfer
-- lQ =
--   Ann
--     (Lam (Inf (lIf :@: iStar0 :@: iBound 0 :@: Inf lBool :@: Inf lNat)))
--     (Pi lBool star0)

lPair :: TermInfer
lPair =
  Ann
    ( Lam $
        Lam $
          iPi (Pi (Bound 1) (Pi (Bound 1) star0)) star0
    )
    (Pi star0 (Pi star0 (Star 1)))

-- evil :: TermInfer
-- evil =
--   Ann
--     (Lam (Lam (Lam (Inf (Bound 1 :@: iBound 1 :@: iBound 0)))))
--     (iPi iStar (iPi (iPi (iBound 0) (iBound 1)) (iPi (iBound 1) (iBound 2))))