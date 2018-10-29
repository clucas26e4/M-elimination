module Syntax.LHSeq.Properties where

  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary

  {- Syntax -}
  open import Syntax.LTerm
  open import Syntax.ListLTerm
  open import Syntax.ListLTerm.Properties
  open import Syntax.LSeq
  open import Syntax.LHSeq


  LHSeqExchangeSym :
    {G G' : LHSeq} ->
    (G=G' : LHSeqExchange G G') ->
    LHSeqExchange G' G
--{{{    
  LHSeqExchangeSym idHE =
    idHE
  LHSeqExchangeSym (exHE G=G') =
    exHE (LHSeqExchangeSym G=G')
  LHSeqExchangeSym exHE-head = 
    exHE-head
  LHSeqExchangeSym (transHE G=G' G=G'') =
    transHE (LHSeqExchangeSym G=G'') (LHSeqExchangeSym G=G')
  LHSeqExchangeSym (indHE G G' G=G') =
    indHE G' G (LHSeqExchangeSym G=G')
--}}}

  LHSeqExchangeCong :
    {G G' G'' : LHSeq} ->
    (G=G' : G ≡ G') ->
    (G=G'' : LHSeqExchange G G'') ->
    LHSeqExchange G' G''
--{{{
  LHSeqExchangeCong refl G=G'' = G=G''
--}}}

  unionKeepLHSeqExchangeRight :
    (G1 : LHSeq) ->
    {G2 G3 : LHSeq} ->
    LHSeqExchange G2 G3 ->
    LHSeqExchange (unionLHSeq G1 G2) (unionLHSeq G1 G3)
--{{{
  unionKeepLHSeqExchangeRight G1 idHE =
    idHE
  unionKeepLHSeqExchangeRight G1 (exHE G2=G3) =
    exHE
      (unionKeepLHSeqExchangeRight G1 G2=G3)
  unionKeepLHSeqExchangeRight G1 exHE-head =
    exHE
      idHE
  unionKeepLHSeqExchangeRight G1 (transHE G2=G3 G2=G4) =
    transHE
      (unionKeepLHSeqExchangeRight G1 G2=G3)
      (unionKeepLHSeqExchangeRight G1 G2=G4)
  unionKeepLHSeqExchangeRight G1 (indHE G G' G2=G3) =
    indHE
      (unionLHSeq G1 G)
      (unionLHSeq G1 G')
      (unionKeepLHSeqExchangeRight G1 G2=G3)
--}}}

  unionKeepLHSeqExchangeLeft :
    {G1 G3 : LHSeq} ->
    (G1=G3 : LHSeqExchange G1 G3) ->
    (G2 : LHSeq) ->
    LHSeqExchange (unionLHSeq G1 G2) (unionLHSeq G3 G2)
--{{{
  unionKeepLHSeqExchangeLeft {G1} {G3} G1=G3 (head H) =
    indHE
      G1
      G3
      G1=G3
  unionKeepLHSeqExchangeLeft {G1} {G3} G1=G3 (G2 ∣ H) =
    indHE
      (unionLHSeq G1 G2)
      (unionLHSeq G3 G2)
      (unionKeepLHSeqExchangeLeft G1=G3 G2)
--}}}

  LHSeqExchangeUnion :
    (G G' : LHSeq) ->
    LHSeqExchange (unionLHSeq G G') (unionLHSeq G' G)
--{{{
  LHSeqExchangeUnion (head H₁) (head H) =
    exHE-head
  LHSeqExchangeUnion (G ∣ H₁) (head H) =
    transHE
      (exHE
        idHE)
      (indHE
        (G ∣ H)
        (unionLHSeq (head H) G)
        (LHSeqExchangeUnion G (head H)))
  LHSeqExchangeUnion (head H₁) (G' ∣ H) = 
    transHE
      (indHE
        (unionLHSeq (head H₁) G')
        (G' ∣ H₁)
        (LHSeqExchangeUnion (head H₁) G'))
      (exHE
        idHE)
  LHSeqExchangeUnion (G ∣ H₁) (G' ∣ H) = 
    transHE
      {G₂ = unionLHSeq G' G ∣ H₁ ∣ H}
      (indHE
        (unionLHSeq (G ∣ H₁) G')
        (unionLHSeq G' G ∣ H₁)
        (LHSeqExchangeUnion (G ∣ H₁) G'))
      (transHE
        (exHE
          (LHSeqExchangeUnion G' G))
        (indHE
          (unionLHSeq G (G' ∣ H))
          (unionLHSeq (G' ∣ H) G)
          (LHSeqExchangeUnion G (G' ∣ H))))
--}}}

  unionLHSeqExchangeLast :
    (G H : LHSeq) ->
    (T : ListLTerm) ->
    (D : ListLTerm) ->
    LHSeqExchange (unionLHSeq (G ∣ (T , D)) H) (unionLHSeq G H ∣ (T , D))
--{{{
  unionLHSeqExchangeLast G (head H) T D =
    exHE
      idHE
  unionLHSeqExchangeLast G (H ∣ H₁) T D =
    transHE
      (indHE
        (unionLHSeq (G ∣ (T , D)) H)
        (unionLHSeq G H ∣ (T , D))
        (unionLHSeqExchangeLast G H T D))
      (exHE
        idHE)
--}}}


  unfoldCorrect :
    (G : LHSeq) ->
    unfolded (unfold G)
  unfoldCorrect (head (T , D)) =
    headU (unfoldListCorrect T) (unfoldListCorrect D)
  unfoldCorrect (G ∣ (T , D)) =
    consU (unfoldCorrect G) (unfoldListCorrect T) (unfoldListCorrect D)

  unfoldedUnique :
    {G : LHSeq} ->
    (uG : unfolded G) ->
    (uG' : unfolded G) ->
    uG ≡ uG'
  unfoldedUnique (headU x x₁) (headU x₂ x₃) =
    cong₂
      (λ x' y -> headU x' y)
      (unfoldedListUnique x x₂)
      (unfoldedListUnique x₁ x₃)
  unfoldedUnique (consU uG x x₁) (consU uG' x₂ x₃) =
    cong₃
      (λ x' y z -> consU x' y z)
      (unfoldedUnique uG uG')
      (unfoldedListUnique x x₂)
      (unfoldedListUnique x₁ x₃)

  LHSeqExchangeKeepUnfolded :
    {G G' : LHSeq} ->
    (G=G' : LHSeqExchange G G') ->
    unfolded G ->
    unfolded G'
  LHSeqExchangeKeepUnfolded idHE uG =
    uG
  LHSeqExchangeKeepUnfolded (exHE G=G') (consU (consU uG x₂ x₃) x x₁) =
    consU (consU (LHSeqExchangeKeepUnfolded G=G' uG) x x₁) x₂ x₃
  LHSeqExchangeKeepUnfolded exHE-head (consU (headU x₂ x₃) x x₁) = 
    consU (headU x x₁) x₂ x₃
  LHSeqExchangeKeepUnfolded (transHE G=G' G=G'') uG =
    LHSeqExchangeKeepUnfolded
      G=G''
      (LHSeqExchangeKeepUnfolded G=G' uG)
  LHSeqExchangeKeepUnfolded (indHE G G' G=G') (consU uG x x₁) =
    consU (LHSeqExchangeKeepUnfolded G=G' uG) x x₁
