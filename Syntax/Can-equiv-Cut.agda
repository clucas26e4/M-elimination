module Syntax.Can-equiv-Cut where
  {- STDLIB -}
  open import Equality
  open import Nat

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.ListTerm.Properties
  open import Syntax.Seq
  open import Syntax.HSeq
  open import Syntax.MGA-Can
  open import Syntax.MGA-Cut

  cutToCan :
    {G : HSeq} ->
    MGA G ->
    MGA-Can G
  cutToCan (ax A) = 
    ax A
  cutToCan Δ-ax = 
    Δ-ax
  cutToCan 1-ax = 
    1-ax
  cutToCan (W G Γ1 Γ2 Δ1 Δ2 p) = 
    W G Γ1 Γ2 Δ1 Δ2 (cutToCan p)
  cutToCan (C G Γ Δ p) = 
    C G Γ Δ (cutToCan p)
  cutToCan (S G Γ1 Γ2 Δ1 Δ2 x x₁ p) = 
    S G Γ1 Γ2 Δ1 Δ2 x x₁ (cutToCan p)
  cutToCan (M G T T' D D' x x₁ p p₁) = 
    M G T T' D D' x x₁ (cutToCan p) (cutToCan p₁)
  cutToCan (W-head Γ1 Γ2 Δ1 Δ2 p) = 
    W-head Γ1 Γ2 Δ1 Δ2 (cutToCan p)
  cutToCan (C-head Γ Δ p) = 
    C-head Γ Δ (cutToCan p)
  cutToCan (S-head Γ1 Γ2 Δ1 Δ2 x x₁ p) = 
    S-head Γ1 Γ2 Δ1 Δ2 x x₁ (cutToCan p)
  cutToCan (M-head T T' D D' x x₁ p p₁) = 
    M-head T T' D D' x x₁ (cutToCan p) (cutToCan p₁)
  cutToCan (Z-L G Γ Δ p) = 
    Z-L G Γ Δ (cutToCan p)
  cutToCan (Z-R G Γ Δ p) = 
    Z-R G Γ Δ (cutToCan p)
  cutToCan (minus-L G Γ Δ A p) = 
    minus-L G Γ Δ A (cutToCan p)
  cutToCan (minus-R G Γ Δ A p) = 
    minus-R G Γ Δ A (cutToCan p)
  cutToCan (plus-L G Γ Δ A B p) = 
    plus-L G Γ Δ A B (cutToCan p)
  cutToCan (plus-R G Γ Δ A B p) = 
    plus-R G Γ Δ A B (cutToCan p)
  cutToCan (max-L G Γ Δ A B p p₁) = 
    max-L G Γ Δ A B (cutToCan p) (cutToCan p₁)
  cutToCan (max-R G Γ Δ A B p) = 
    max-R G Γ Δ A B (cutToCan p)
  cutToCan (min-L G Γ Δ A B p) = 
    min-L G Γ Δ A B (cutToCan p)
  cutToCan (min-R G Γ Δ A B p p₁) = 
    min-R G Γ Δ A B (cutToCan p) (cutToCan p₁)
  cutToCan (Z-L-head Γ Δ p) = 
    Z-L-head Γ Δ (cutToCan p)
  cutToCan (Z-R-head Γ Δ p) = 
    Z-R-head Γ Δ (cutToCan p)
  cutToCan (minus-L-head Γ Δ A p) = 
    minus-L-head Γ Δ A (cutToCan p)
  cutToCan (minus-R-head Γ Δ A p) = 
    minus-R-head Γ Δ A (cutToCan p)
  cutToCan (plus-L-head Γ Δ A B p) = 
    plus-L-head Γ Δ A B (cutToCan p)
  cutToCan (plus-R-head Γ Δ A B p) = 
    plus-R-head Γ Δ A B (cutToCan p)
  cutToCan (max-L-head Γ Δ A B p p₁) = 
    max-L-head Γ Δ A B (cutToCan p) (cutToCan p₁)
  cutToCan (max-R-head Γ Δ A B p) = 
    max-R-head Γ Δ A B (cutToCan p)
  cutToCan (min-L-head Γ Δ A B p) = 
    min-L-head Γ Δ A B (cutToCan p)
  cutToCan (min-R-head Γ Δ A B p p₁) = 
    min-R-head Γ Δ A B (cutToCan p) (cutToCan p₁)
  cutToCan (seq-exchange G Γ Γ' Δ Δ' x x₁ p) = 
    seq-exchange G Γ Γ' Δ Δ' x x₁ (cutToCan p)
  cutToCan (seq-exchange-head Γ Γ' Δ Δ' x x₁ p) = 
    seq-exchange-head Γ Γ' Δ Δ' x x₁ (cutToCan p)
  cutToCan (hseq-exchange G G' x p) = 
    hseq-exchange G G' x (cutToCan p)
  cutToCan (◆-rule Γ Δ ◆Γ ◆Δ k x x₁ x₂ p) = 
    ◆-rule Γ Δ ◆Γ ◆Δ k x x₁ x₂ (cutToCan p)
  cutToCan (cut-head Γ₁ Γ₂ Δ₁ Δ₂ A refl refl p p₁) =
    can-rule-head
      (union Γ₁ Γ₂)
      (union Δ₁ Δ₂)
      A
      (seq-exchange-head
        (union (Γ₁ ∷ A) Γ₂)
        (union Γ₁ Γ₂ ∷ A)
        (union Δ₁ Δ₂ ∷ A)
        (union Δ₁ Δ₂ ∷ A)
        (exchangeUnionLast
          Γ₁
          Γ₂
          A)
        idLE
        (M-head
          (Γ₁ ∷ A)
          Γ₂
          Δ₁
          (Δ₂ ∷ A)
          refl
          refl
          (cutToCan p)
          (cutToCan p₁)))
  cutToCan (cut G Γ₁ Γ₂ Δ₁ Δ₂ A refl refl p p₁) = 
    can-rule
      G
      (union Γ₁ Γ₂)
      (union Δ₁ Δ₂)
      A
      (seq-exchange
        G
        (union (Γ₁ ∷ A) Γ₂)
        (union Γ₁ Γ₂ ∷ A)
        (union Δ₁ Δ₂ ∷ A)
        (union Δ₁ Δ₂ ∷ A)
        (exchangeUnionLast
          Γ₁
          Γ₂
          A)
        idLE
        (M
          G
          (Γ₁ ∷ A)
          Γ₂
          Δ₁
          (Δ₂ ∷ A)
          refl
          refl
          (cutToCan p)
          (cutToCan p₁)))

  canToCut :
    {G : HSeq} ->
    MGA-Can G ->
    MGA G
  canToCut (ax A) = 
    ax A
  canToCut Δ-ax = 
    Δ-ax
  canToCut 1-ax = 
    1-ax
  canToCut (W G Γ1 Γ2 Δ1 Δ2 p) = 
    W G Γ1 Γ2 Δ1 Δ2 (canToCut p)
  canToCut (C G Γ Δ p) = 
    C G Γ Δ (canToCut p)
  canToCut (S G Γ1 Γ2 Δ1 Δ2 x x₁ p) = 
    S G Γ1 Γ2 Δ1 Δ2 x x₁ (canToCut p)
  canToCut (M G T T' D D' x x₁ p p₁) = 
    M G T T' D D' x x₁ (canToCut p) (canToCut p₁)
  canToCut (W-head Γ1 Γ2 Δ1 Δ2 p) = 
    W-head Γ1 Γ2 Δ1 Δ2 (canToCut p)
  canToCut (C-head Γ Δ p) = 
    C-head Γ Δ (canToCut p)
  canToCut (S-head Γ1 Γ2 Δ1 Δ2 x x₁ p) = 
    S-head Γ1 Γ2 Δ1 Δ2 x x₁ (canToCut p)
  canToCut (M-head T T' D D' x x₁ p p₁) = 
    M-head T T' D D' x x₁ (canToCut p) (canToCut p₁)
  canToCut (Z-L G Γ Δ p) = 
    Z-L G Γ Δ (canToCut p)
  canToCut (Z-R G Γ Δ p) = 
    Z-R G Γ Δ (canToCut p)
  canToCut (minus-L G Γ Δ A p) = 
    minus-L G Γ Δ A (canToCut p)
  canToCut (minus-R G Γ Δ A p) = 
    minus-R G Γ Δ A (canToCut p)
  canToCut (plus-L G Γ Δ A B p) = 
    plus-L G Γ Δ A B (canToCut p)
  canToCut (plus-R G Γ Δ A B p) = 
    plus-R G Γ Δ A B (canToCut p)
  canToCut (max-L G Γ Δ A B p p₁) = 
    max-L G Γ Δ A B (canToCut p) (canToCut p₁)
  canToCut (max-R G Γ Δ A B p) = 
    max-R G Γ Δ A B (canToCut p)
  canToCut (min-L G Γ Δ A B p) = 
    min-L G Γ Δ A B (canToCut p)
  canToCut (min-R G Γ Δ A B p p₁) = 
    min-R G Γ Δ A B (canToCut p) (canToCut p₁)
  canToCut (Z-L-head Γ Δ p) = 
    Z-L-head Γ Δ (canToCut p)
  canToCut (Z-R-head Γ Δ p) = 
    Z-R-head Γ Δ (canToCut p)
  canToCut (minus-L-head Γ Δ A p) = 
    minus-L-head Γ Δ A (canToCut p)
  canToCut (minus-R-head Γ Δ A p) = 
    minus-R-head Γ Δ A (canToCut p)
  canToCut (plus-L-head Γ Δ A B p) = 
    plus-L-head Γ Δ A B (canToCut p)
  canToCut (plus-R-head Γ Δ A B p) = 
    plus-R-head Γ Δ A B (canToCut p)
  canToCut (max-L-head Γ Δ A B p p₁) = 
    max-L-head Γ Δ A B (canToCut p) (canToCut p₁)
  canToCut (max-R-head Γ Δ A B p) = 
    max-R-head Γ Δ A B (canToCut p)
  canToCut (min-L-head Γ Δ A B p) = 
    min-L-head Γ Δ A B (canToCut p)
  canToCut (min-R-head Γ Δ A B p p₁) = 
    min-R-head Γ Δ A B (canToCut p) (canToCut p₁)
  canToCut (seq-exchange G Γ Γ' Δ Δ' x x₁ p) = 
    seq-exchange G Γ Γ' Δ Δ' x x₁ (canToCut p)
  canToCut (seq-exchange-head Γ Γ' Δ Δ' x x₁ p) = 
    seq-exchange-head Γ Γ' Δ Δ' x x₁ (canToCut p)
  canToCut (hseq-exchange G G' x p) = 
    hseq-exchange G G' x (canToCut p)
  canToCut (◆-rule Γ Δ ◆Γ ◆Δ k x x₁ x₂ p) = 
    ◆-rule Γ Δ ◆Γ ◆Δ k x x₁ x₂ (canToCut p)
  canToCut (can-rule G Γ Δ A p) = 
    C
      G
      Γ
      Δ
      (S
        G
        Γ
        Γ
        Δ
        Δ
        refl
        refl
        (cut
          G
          Γ
          Γ
          Δ
          Δ
          (A +S (-S A))
          refl
          refl
          (plus-L
            G
            Γ
            Δ
            A
            (-S A)
            (minus-L
              G
              (Γ ∷ A)
              Δ
              A
              (canToCut p)))
          (plus-R
            G
            Γ
            Δ
            A
            (-S A)
            (minus-R
              G
              Γ
              (Δ ∷ A)
              A
              (canToCut p)))))
  canToCut (can-rule-head Γ Δ A p) = 
    C-head
      Γ
      Δ
      (S-head
        Γ
        Γ
        Δ
        Δ
        refl
        refl
        (cut-head
          Γ
          Γ
          Δ
          Δ
          (A +S (-S A))
          refl
          refl
          (plus-L-head
            Γ
            Δ
            A
            (-S A)
            (minus-L-head
              (Γ ∷ A)
              Δ
              A
              (canToCut p)))
          (plus-R-head
            Γ
            Δ
            A
            (-S A)
            (minus-R-head
              Γ
              (Δ ∷ A)
              A
              (canToCut p)))))
