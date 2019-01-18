module Syntax.MGA-SR-Can.M-Elim-Can where
  {- STDLIB -}
  open import Equality
  open import Nat
  open import Data.Product
  open import Induction.WellFounded

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.LTerm
  open import Syntax.ListLTerm
  open import Syntax.LSeq
  open import Syntax.LHSeq
  open import Syntax.LHSeqList
  open import Syntax.MGA-SR-Can
  open import Syntax.MGA-SR-Can.M-Elim-Can.Step2
  open import Syntax.MGA-SR-Can.MGA-SR-CanwM
  
  M-rule :
    (G : LHSeq) ->
    (T T' D D' : ListLTerm) ->
    MGA-SR† (G ∣ (T , D)) ->
    MGA-SR† (G ∣ (T' , D')) ->
    MGA-SR† (G ∣ (union T T' , union D D'))
  M-rule G T T' D D' p p₁ =
    applyContraction
      G
      (head (union T T' , union D D'))
      (mElim
        G
        G
        T
        T'
        D
        D'
        p
        p₁
        (ℕ-acc (#◆ p)))

  M-head-rule :
    (T T' D D' : ListLTerm) ->
    MGA-SR† (head (T , D)) ->
    MGA-SR† (head (T' , D')) ->
    MGA-SR† (head (union T T' , union D D'))
  M-head-rule T T' D D' p p₁ =
    mElim-headGH
      T
      T'
      D
      D'
      p
      p₁
      (ℕ-acc (#◆ p))

  fromMGA-SR†toMGA-SR :
    {G : LHSeq} ->
    MGA-SR† G ->
    MGA-SR G
  fromMGA-SR†toMGA-SR ax = 
    ax
  fromMGA-SR†toMGA-SR (W G Γ1 Γ2 Δ1 Δ2 p) = 
    W G Γ1 Γ2 Δ1 Δ2 (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (C G Γ Δ p) = 
    C G Γ Δ (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (S G Γ1 Γ2 Δ1 Δ2 refl refl p) = 
    S G Γ1 Γ2 Δ1 Δ2 refl refl (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (Id-rule G Γ Δ A p) = 
    Id-rule G Γ Δ A (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (W-head Γ1 Γ2 Δ1 Δ2 p) =
    W-head Γ1 Γ2 Δ1 Δ2 (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (C-head Γ Δ p) = 
    C-head Γ Δ (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (S-head Γ1 Γ2 Δ1 Δ2 refl refl p) = 
    S-head Γ1 Γ2 Δ1 Δ2 refl refl (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (Id-rule-head Γ Δ A p) = 
    Id-rule-head Γ Δ A (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (U-L G Γ Δ A n1 n2 refl p) = 
    U-L G Γ Δ A n1 n2 refl (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (U-R G Γ Δ A n1 n2 refl p) = 
    U-R G Γ Δ A n1 n2 refl (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (F-L G Γ Δ A n1 n2 refl p) = 
    F-L G Γ Δ A n1 n2 refl (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (F-R G Γ Δ A n1 n2 refl p) = 
    F-R G Γ Δ A n1 n2 refl (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (U-L-head Γ Δ A n1 n2 refl p) = 
    U-L-head Γ Δ A n1 n2 refl (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (U-R-head Γ Δ A n1 n2 refl p) = 
    U-R-head Γ Δ A n1 n2 refl (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (F-L-head Γ Δ A n1 n2 refl p) = 
    F-L-head Γ Δ A n1 n2 refl (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (F-R-head Γ Δ A n1 n2 refl p) = 
    F-R-head Γ Δ A n1 n2 refl (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (E-L G Γ Δ A p) = 
    E-L G Γ Δ A (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (E-R G Γ Δ A p) = 
    E-R G Γ Δ A (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (E-L-head Γ Δ A p) = 
    E-L-head Γ Δ A (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (E-R-head Γ Δ A p) = 
    E-R-head Γ Δ A (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (plus-L G Γ Δ A B n p) = 
    plus-L G Γ Δ A B n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (plus-R G Γ Δ A B n p) = 
    plus-R G Γ Δ A B n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (max-L G Γ Δ A B n p p₁) = 
    max-L G Γ Δ A B n (fromMGA-SR†toMGA-SR p) (fromMGA-SR†toMGA-SR p₁)
  fromMGA-SR†toMGA-SR (max-R G Γ Δ A B n p) = 
    max-R G Γ Δ A B n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (plus-L-head Γ Δ A B n p) = 
    plus-L-head Γ Δ A B n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (plus-R-head Γ Δ A B n p) = 
    plus-R-head Γ Δ A B n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (max-L-head Γ Δ A B n p p₁) = 
    max-L-head Γ Δ A B n (fromMGA-SR†toMGA-SR p) (fromMGA-SR†toMGA-SR p₁)
  fromMGA-SR†toMGA-SR (max-R-head Γ Δ A B n p) = 
    max-R-head Γ Δ A B n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (Z-L G Γ Δ n p) = 
    Z-L G Γ Δ n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (Z-R G Γ Δ n p) = 
    Z-R G Γ Δ n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (minus-L G Γ Δ A n p) = 
    minus-L G Γ Δ A n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (minus-R G Γ Δ A n p) = 
    minus-R G Γ Δ A n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (min-L G Γ Δ A B n p) = 
    min-L G Γ Δ A B n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (min-R G Γ Δ A B n p p₁) = 
    min-R G Γ Δ A B n (fromMGA-SR†toMGA-SR p) (fromMGA-SR†toMGA-SR p₁)
  fromMGA-SR†toMGA-SR (Z-L-head Γ Δ n p) = 
    Z-L-head Γ Δ n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (Z-R-head Γ Δ n p) = 
    Z-R-head Γ Δ n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (minus-L-head Γ Δ A n p) = 
    minus-L-head Γ Δ A n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (minus-R-head Γ Δ A n p) = 
    minus-R-head Γ Δ A n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (min-L-head Γ Δ A B n p) = 
    min-L-head Γ Δ A B n (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (min-R-head Γ Δ A B n p p₁) = 
    min-R-head Γ Δ A B n (fromMGA-SR†toMGA-SR p) (fromMGA-SR†toMGA-SR p₁)
  fromMGA-SR†toMGA-SR (◆1-rule Γ Δ ◆Γ ◆Δ refl refl k p) = 
    ◆1-rule Γ Δ ◆Γ ◆Δ refl refl k (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (◆-rule Γ Δ ◆Γ ◆Δ refl refl p) = 
    ◆-rule Γ Δ ◆Γ ◆Δ refl refl (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (1-rule G Γ Δ k p) = 
    1-rule G Γ Δ k (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (1-rule-head Γ Δ k p) = 
    1-rule-head Γ Δ k (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (seq-exchange G Γ Γ' Δ Δ' x x₁ p) = 
    seq-exchange G Γ Γ' Δ Δ' x x₁ (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (seq-exchange-head Γ Γ' Δ Δ' x x₁ p) = 
    seq-exchange-head Γ Γ' Δ Δ' x x₁ (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (hseq-exchange G G' x p) = 
    hseq-exchange G G' x (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (can-rule G T D A p) =
    can-rule G T D A (fromMGA-SR†toMGA-SR p)
  fromMGA-SR†toMGA-SR (can-rule-head T D A p) =
    can-rule-head T D A (fromMGA-SR†toMGA-SR p)

  fromMGA-SRtoMGA-SR† :
    {G : LHSeq} ->
    MGA-SR G ->
    MGA-SR† G
  fromMGA-SRtoMGA-SR† ax = 
    ax
  fromMGA-SRtoMGA-SR† (W G Γ1 Γ2 Δ1 Δ2 p) = 
    W G Γ1 Γ2 Δ1 Δ2 (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (C G Γ Δ p) = 
    C G Γ Δ (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (S G Γ1 Γ2 Δ1 Δ2 refl refl p) = 
    S G Γ1 Γ2 Δ1 Δ2 refl refl (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (Id-rule G Γ Δ A p) = 
    Id-rule G Γ Δ A (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (W-head Γ1 Γ2 Δ1 Δ2 p) =
    W-head Γ1 Γ2 Δ1 Δ2 (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (C-head Γ Δ p) = 
    C-head Γ Δ (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (S-head Γ1 Γ2 Δ1 Δ2 refl refl p) = 
    S-head Γ1 Γ2 Δ1 Δ2 refl refl (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (Id-rule-head Γ Δ A p) = 
    Id-rule-head Γ Δ A (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (U-L G Γ Δ A n1 n2 refl p) = 
    U-L G Γ Δ A n1 n2 refl (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (U-R G Γ Δ A n1 n2 refl p) = 
    U-R G Γ Δ A n1 n2 refl (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (F-L G Γ Δ A n1 n2 refl p) = 
    F-L G Γ Δ A n1 n2 refl (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (F-R G Γ Δ A n1 n2 refl p) = 
    F-R G Γ Δ A n1 n2 refl (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (U-L-head Γ Δ A n1 n2 refl p) = 
    U-L-head Γ Δ A n1 n2 refl (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (U-R-head Γ Δ A n1 n2 refl p) = 
    U-R-head Γ Δ A n1 n2 refl (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (F-L-head Γ Δ A n1 n2 refl p) = 
    F-L-head Γ Δ A n1 n2 refl (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (F-R-head Γ Δ A n1 n2 refl p) = 
    F-R-head Γ Δ A n1 n2 refl (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (E-L G Γ Δ A p) = 
    E-L G Γ Δ A (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (E-R G Γ Δ A p) = 
    E-R G Γ Δ A (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (E-L-head Γ Δ A p) = 
    E-L-head Γ Δ A (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (E-R-head Γ Δ A p) = 
    E-R-head Γ Δ A (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (plus-L G Γ Δ A B n p) = 
    plus-L G Γ Δ A B n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (plus-R G Γ Δ A B n p) = 
    plus-R G Γ Δ A B n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (max-L G Γ Δ A B n p p₁) = 
    max-L G Γ Δ A B n (fromMGA-SRtoMGA-SR† p) (fromMGA-SRtoMGA-SR† p₁)
  fromMGA-SRtoMGA-SR† (max-R G Γ Δ A B n p) = 
    max-R G Γ Δ A B n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (plus-L-head Γ Δ A B n p) = 
    plus-L-head Γ Δ A B n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (plus-R-head Γ Δ A B n p) = 
    plus-R-head Γ Δ A B n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (max-L-head Γ Δ A B n p p₁) = 
    max-L-head Γ Δ A B n (fromMGA-SRtoMGA-SR† p) (fromMGA-SRtoMGA-SR† p₁)
  fromMGA-SRtoMGA-SR† (max-R-head Γ Δ A B n p) = 
    max-R-head Γ Δ A B n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (Z-L G Γ Δ n p) = 
    Z-L G Γ Δ n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (Z-R G Γ Δ n p) = 
    Z-R G Γ Δ n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (minus-L G Γ Δ A n p) = 
    minus-L G Γ Δ A n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (minus-R G Γ Δ A n p) = 
    minus-R G Γ Δ A n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (min-L G Γ Δ A B n p) = 
    min-L G Γ Δ A B n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (min-R G Γ Δ A B n p p₁) = 
    min-R G Γ Δ A B n (fromMGA-SRtoMGA-SR† p) (fromMGA-SRtoMGA-SR† p₁)
  fromMGA-SRtoMGA-SR† (Z-L-head Γ Δ n p) = 
    Z-L-head Γ Δ n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (Z-R-head Γ Δ n p) = 
    Z-R-head Γ Δ n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (minus-L-head Γ Δ A n p) = 
    minus-L-head Γ Δ A n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (minus-R-head Γ Δ A n p) = 
    minus-R-head Γ Δ A n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (min-L-head Γ Δ A B n p) = 
    min-L-head Γ Δ A B n (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (min-R-head Γ Δ A B n p p₁) = 
    min-R-head Γ Δ A B n (fromMGA-SRtoMGA-SR† p) (fromMGA-SRtoMGA-SR† p₁)
  fromMGA-SRtoMGA-SR† (◆1-rule Γ Δ ◆Γ ◆Δ refl refl k p) = 
    ◆1-rule Γ Δ ◆Γ ◆Δ refl refl k (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (◆-rule Γ Δ ◆Γ ◆Δ refl refl p) = 
    ◆-rule Γ Δ ◆Γ ◆Δ refl refl (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (1-rule G Γ Δ k p) = 
    1-rule G Γ Δ k (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (1-rule-head Γ Δ k p) = 
    1-rule-head Γ Δ k (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (seq-exchange G Γ Γ' Δ Δ' x x₁ p) = 
    seq-exchange G Γ Γ' Δ Δ' x x₁ (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (seq-exchange-head Γ Γ' Δ Δ' x x₁ p) = 
    seq-exchange-head Γ Γ' Δ Δ' x x₁ (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (hseq-exchange G G' x p) = 
    hseq-exchange G G' x (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (M G T T' D D' refl refl p p') = 
    M-rule
      G
      T
      T'
      D
      D'
      (fromMGA-SRtoMGA-SR† p)
      (fromMGA-SRtoMGA-SR† p')
  fromMGA-SRtoMGA-SR† (M-head T T' D D' refl refl p p') =
    M-head-rule
      T
      T'
      D
      D'
      (fromMGA-SRtoMGA-SR† p)
      (fromMGA-SRtoMGA-SR† p')
  fromMGA-SRtoMGA-SR† (can-rule G T D A p) =
    can-rule G T D A (fromMGA-SRtoMGA-SR† p)
  fromMGA-SRtoMGA-SR† (can-rule-head T D A p) =
    can-rule-head T D A (fromMGA-SRtoMGA-SR† p)
