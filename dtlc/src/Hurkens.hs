module Hurkens where

import DTLC

empty :: TermInfer
empty = Pi iStar (iBound 0)

neg :: TermInfer
neg =
  Ann
    (Lam (iPi (iBound 0) (Inf empty)))
    (iPi iStar iStar)

pow :: TermInfer
pow =
  Ann
    (Lam (iPi (iBound 0) iStar))
    (iPi iStar iStar)

powPow :: TermInfer
powPow =
  Ann
    (Lam (pow .@. (pow .@. iBound 0)))
    (iPi iStar iStar)

universe :: TermInfer
universe =
  Pi iStar $
    iPi (iPi (powPow .@. iBound 0) (iBound 1)) $
      powPow .@. iBound 1

iUniverse = Inf universe

tau :: TermInfer
tau =
  Ann
    ( Lam $
        Lam $
          Lam $
            Lam $
              Bound 3
                .@. Lam
                  (Bound 1 .@. (Bound 2 .@. (Bound 0 :@: iBound 3 .@. iBound 2)))
    )
    (iPi (powPow .@. iUniverse) iUniverse)

sigma :: TermInfer
sigma =
  Ann
    ( Lam $
        Bound 0 :@: iUniverse .@. Inf tau
    )
    (iPi iUniverse (powPow .@. iUniverse))

inductive :: TermInfer
inductive =
  Ann
    ( Lam $
        iPi iUniverse $
          iPi (sigma :@: iBound 0 .@. iBound 1) $
            Bound 2 .@. iBound 1
    )
    (powPow .@. iUniverse)

omega :: TermInfer
omega = tau :@: Inf inductive

wellFounded :: TermInfer
wellFounded =
  Ann
    ( Lam
        ( iPi (pow .@. iUniverse) $
            iPi (inductive .@. iBound 0) $
              Bound 1 .@. iBound 2
        )
    )
    (pow .@. iUniverse)

wellFoundedOmega :: TermInfer
wellFoundedOmega =
  Ann
    ( Lam $
        Lam $
          Bound 0 :@: Inf omega
            .@. Lam
              (Bound 1 .@. (tau .@. (sigma .@. iBound 0)))
    )
    (wellFounded .@. Inf omega)

lessThan :: TermInfer
lessThan =
  Ann
    ( Lam $
        Lam $
          iPi (pow .@. iUniverse) $
            iPi (sigma :@: iBound 1 .@. iBound 0) $
              Bound 1 .@. iBound 3
    )
    (iPi iUniverse (iPi iUniverse iStar))

delta :: TermInfer
delta =
  Ann
    ( Lam $
        neg .@. (lessThan :@: (tau .@. (sigma .@. iBound 0)) .@. iBound 0)
    )
    (pow .@. iUniverse)

inductiveDelta :: TermInfer
inductiveDelta =
  Ann
    ( Lam $
        Lam $
          Lam $
            Bound 0 :@: Inf delta :@: iBound 1
              .@. Lam
                ( Bound 1
                    .@. Lam
                      (Bound 1 .@. (tau .@. (sigma .@. iBound 0)))
                )
    )
    (inductive .@. Inf delta)

negWellFoundedOmega :: TermInfer
negWellFoundedOmega =
  Ann
    ( Lam $
        Bound 0 :@: Inf delta :@: Inf inductiveDelta
          .@. Lam
            ( Bound 1
                .@. Lam
                  (Bound 1 .@. (tau .@. (sigma .@. iBound 0)))
            )
    )
    (neg .@. (wellFounded .@. Inf omega))

false :: TermInfer
false = negWellFoundedOmega :@: Inf wellFoundedOmega