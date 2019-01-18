module Syntax.MGA-Cut.Completeness where
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.ListTerm.Properties
  open import Syntax.Seq
  open import Syntax.HSeq
  open import Syntax.MGA-Cut

  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties
  open import Semantic.Interpretation

  substKeepProof :
    {G : HSeq} ->
    (p : MGA G) ->
    (k : ℕ) ->
    (A : Term) ->
    MGA (substHSeq G k A)
  substKeepProof (ax A₁) k A =
    ax (A₁ s[ A / k ])
  substKeepProof Δ-ax k A = 
    Δ-ax
  substKeepProof 1-ax k A = 
    1-ax
  substKeepProof (W G Γ1 Γ2 Δ1 Δ2 p) k A = 
    W
      (substHSeq G k A)
      (substList Γ1 k A)
      (substList Γ2 k A)
      (substList Δ1 k A)
      (substList Δ2 k A)
      (substKeepProof p k A)
  substKeepProof (C G Γ Δ p) k A = 
    C
      (substHSeq G k A)
      (substList Γ k A)
      (substList Δ k A)
      (substKeepProof p k A)
  substKeepProof (S G Γ1 Γ2 Δ1 Δ2 refl refl p) k A = {!
    S
      (substHSeq G k A)
      (substList Γ1 k A)
      (substList Γ2 k A)
      (substList Δ1 k A)
      (substList Δ2 k A)
      refl
      refl
      (substKeepProof p k A)!}
  substKeepProof (M G T T' D D' refl refl p p₁) k A = {!!}
  substKeepProof (W-head Γ1 Γ2 Δ1 Δ2 p) k A = 
    W-head
      (substList Γ1 k A)
      (substList Γ2 k A)
      (substList Δ1 k A)
      (substList Δ2 k A)
      (substKeepProof p k A)
  substKeepProof (C-head Γ Δ p) k A = 
    C-head
      (substList Γ k A)
      (substList Δ k A)
      (substKeepProof p k A)
  substKeepProof (S-head Γ1 Γ2 Δ1 Δ2 refl refl p) k A = {!!}
  substKeepProof (M-head T T' D D' refl refl p p₁) k A = {!!}
  substKeepProof (Z-L G Γ Δ p) k A = 
    Z-L
      (substHSeq G k A)
      (substList Γ k A)
      (substList Δ k A)
      (substKeepProof p k A)
  substKeepProof (Z-R G Γ Δ p) k A = 
    Z-R
      (substHSeq G k A)
      (substList Γ k A)
      (substList Δ k A)
      (substKeepProof p k A)
  substKeepProof (minus-L G Γ Δ A₁ p) k A = 
    minus-L
      (substHSeq G k A)
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (substKeepProof p k A)
  substKeepProof (minus-R G Γ Δ A₁ p) k A = 
    minus-R
      (substHSeq G k A)
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (substKeepProof p k A)
  substKeepProof (plus-L G Γ Δ A₁ B p) k A = 
    plus-L
      (substHSeq G k A)
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (B s[ A / k ])
      (substKeepProof p k A)
  substKeepProof (plus-R G Γ Δ A₁ B p) k A = 
    plus-R
      (substHSeq G k A)
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (B s[ A / k ])
      (substKeepProof p k A)
  substKeepProof (max-L G Γ Δ A₁ B p p₁) k A = 
    max-L
      (substHSeq G k A)
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (B s[ A / k ])
      (substKeepProof p k A)
      (substKeepProof p₁ k A)
  substKeepProof (max-R G Γ Δ A₁ B p) k A = 
    max-R
      (substHSeq G k A)
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (B s[ A / k ])
      (substKeepProof p k A)
  substKeepProof (min-L G Γ Δ A₁ B p) k A = 
    min-L
      (substHSeq G k A)
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (B s[ A / k ])
      (substKeepProof p k A)
  substKeepProof (min-R G Γ Δ A₁ B p p₁) k A = 
    min-R
      (substHSeq G k A)
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (B s[ A / k ])
      (substKeepProof p k A)
      (substKeepProof p₁ k A)
  substKeepProof (Z-L-head Γ Δ p) k A = 
    Z-L-head
      (substList Γ k A)
      (substList Δ k A)
      (substKeepProof p k A)
  substKeepProof (Z-R-head Γ Δ p) k A = 
    Z-R-head
      (substList Γ k A)
      (substList Δ k A)
      (substKeepProof p k A)
  substKeepProof (minus-L-head Γ Δ A₁ p) k A = 
    minus-L-head
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (substKeepProof p k A)
  substKeepProof (minus-R-head Γ Δ A₁ p) k A = 
    minus-R-head
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (substKeepProof p k A)
  substKeepProof (plus-L-head Γ Δ A₁ B p) k A = 
    plus-L-head
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (B s[ A / k ])
      (substKeepProof p k A)
  substKeepProof (plus-R-head Γ Δ A₁ B p) k A = 
    plus-R-head
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (B s[ A / k ])
      (substKeepProof p k A)
  substKeepProof (max-L-head Γ Δ A₁ B p p₁) k A = 
    max-L-head
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (B s[ A / k ])
      (substKeepProof p k A)
      (substKeepProof p₁ k A)
  substKeepProof (max-R-head Γ Δ A₁ B p) k A = 
    max-R-head
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (B s[ A / k ])
      (substKeepProof p k A)
  substKeepProof (min-L-head Γ Δ A₁ B p) k A = 
    min-L-head
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (B s[ A / k ])
      (substKeepProof p k A)
  substKeepProof (min-R-head Γ Δ A₁ B p p₁) k A = 
    min-R-head
      (substList Γ k A)
      (substList Δ k A)
      (A₁ s[ A / k ])
      (B s[ A / k ])
      (substKeepProof p k A)
      (substKeepProof p₁ k A)
  substKeepProof (seq-exchange G Γ Γ' Δ Δ' x x₁ p) k A = {!!}
  substKeepProof (seq-exchange-head Γ Γ' Δ Δ' x x₁ p) k A = {!!}
  substKeepProof (hseq-exchange G G' x p) k A = {!!}
  substKeepProof (◆-rule Γ Δ ◆Γ ◆Δ k₁ refl refl refl p) k A = {!!}
  substKeepProof (cut-head Γ₁ Γ₂ Δ₁ Δ₂ A₁ refl refl p p₁) k A = {!!}
  substKeepProof (cut G Γ₁ Γ₂ Δ₁ Δ₂ A₁ refl refl p p₁) k A = {!!}

  mutual
    completeness1 :
      {A B : Term} ->
      A ≡ₛ B ->
      MGA (head ([] ∷ A , [] ∷ B))
    completeness1 {A} reflₛ =
      ax A
    completeness1 (transₛ {A} {B} {B'} A=B B=B') =
      cut-head [] ([] ∷ A) ([] ∷ B') [] B refl refl
        (completeness1 B=B')
        (completeness1 A=B)
    completeness1 (symₛ A=B) =
      completeness2 A=B
    completeness1 (ctxtₛ ● A=B) =
      completeness1 A=B
    completeness1 (ctxtₛ (CC x) A=B) =
      ax x
    completeness1 (ctxtₛ (varC x) A=B) =
      ax (varAG x)
    completeness1 (ctxtₛ botC A=B) =
      ax botAG
    completeness1 (ctxtₛ {A} {B} (Ctxt ⊔C Ctxt₁) A=B) =
      max-L-head
        []
        ([] ∷ ((_#[_]# Ctxt B) ⊔S (_#[_]# Ctxt₁ B)))
        (_#[_]# Ctxt A)
        (_#[_]# Ctxt₁ A)
        (max-R-head
          ([] ∷ (_#[_]# Ctxt A))
          []
          (_#[_]# Ctxt B)
          (_#[_]# Ctxt₁ B)
          (W-head
            ([] ∷ _#[_]# Ctxt A)
            ([] ∷ _#[_]# Ctxt A)
            ([] ∷ _#[_]# Ctxt B)
            ([] ∷ _#[_]# Ctxt₁ B)
            (completeness1 (ctxtₛ Ctxt A=B))))
        (max-R-head
          ([] ∷ (_#[_]# Ctxt₁ A))
          []
          (_#[_]# Ctxt B)
          (_#[_]# Ctxt₁ B)
          (hseq-exchange
            (head (([] ∷ _#[_]# Ctxt₁ A) , [] ∷ _#[_]# Ctxt₁ B) ∣ ([] ∷ _#[_]# Ctxt₁ A , [] ∷ _#[_]# Ctxt B))
            (head (([] ∷ (_#[_]# Ctxt₁ A)) , ([] ∷ (_#[_]# Ctxt B))) ∣ (([] ∷ (_#[_]# Ctxt₁ A)) , ([] ∷ (_#[_]# Ctxt₁ B))))
            exHE-head
            (W-head
              ([] ∷ _#[_]# Ctxt₁ A)
              ([] ∷ _#[_]# Ctxt₁ A)
              ([] ∷ _#[_]# Ctxt₁ B)
              ([] ∷ _#[_]# Ctxt B)
              (completeness1 (ctxtₛ Ctxt₁ A=B)))))
    completeness1 (ctxtₛ {A} {B} (Ctxt +C Ctxt₁) A=B) =
      plus-R-head
        ([] ∷ ((_#[_]# Ctxt A) +S (_#[_]# Ctxt₁ A)))
        []
        (_#[_]# Ctxt B)
        (_#[_]# Ctxt₁ B)
        (plus-L-head
          []
          ([] ∷ _#[_]# Ctxt B ∷ _#[_]# Ctxt₁ B)
          (_#[_]# Ctxt A)
          (_#[_]# Ctxt₁ A)
          (M-head
            ([] ∷ _#[_]# Ctxt A)
            ([] ∷ _#[_]# Ctxt₁ A)
            ([] ∷ _#[_]# Ctxt B)
            ([] ∷ _#[_]# Ctxt₁ B)
            refl
            refl
            (completeness1 (ctxtₛ Ctxt A=B))
            (completeness1 (ctxtₛ Ctxt₁ A=B))))
    completeness1 (ctxtₛ {A} {B} (Ctxt ⊓C Ctxt₁) A=B) = 
      min-R-head
        ([] ∷ ((_#[_]# Ctxt A) ⊓S (_#[_]# Ctxt₁ A)))
        []
        (_#[_]# Ctxt B)
        (_#[_]# Ctxt₁ B)
        (min-L-head
          []
          ([] ∷ (_#[_]# Ctxt B))
          (_#[_]# Ctxt A)
          (_#[_]# Ctxt₁ A)
          (W-head
            ([] ∷ _#[_]# Ctxt A)
            ([] ∷ _#[_]# Ctxt₁ A)
            ([] ∷ _#[_]# Ctxt B)
            ([] ∷ _#[_]# Ctxt B)
            (completeness1 (ctxtₛ Ctxt A=B))))
        (min-L-head
          []
          ([] ∷ (_#[_]# Ctxt₁ B))
          (_#[_]# Ctxt A)
          (_#[_]# Ctxt₁ A)
          (hseq-exchange
            (head (([] ∷ _#[_]# Ctxt₁ A) , [] ∷ _#[_]# Ctxt₁ B) ∣ ([] ∷ _#[_]# Ctxt A , [] ∷ _#[_]# Ctxt₁ B))
            (head (([] ∷ (_#[_]# Ctxt A)) , ([] ∷ (_#[_]# Ctxt₁ B))) ∣ (([] ∷ (_#[_]# Ctxt₁ A)) , ([] ∷ (_#[_]# Ctxt₁ B))))
            exHE-head
            (W-head
              ([] ∷ _#[_]# Ctxt₁ A)
              ([] ∷ _#[_]# Ctxt A)
              ([] ∷ _#[_]# Ctxt₁ B)
              ([] ∷ _#[_]# Ctxt₁ B)
              (completeness1 (ctxtₛ Ctxt₁ A=B)))))
    completeness1 (ctxtₛ {A} {B} (-C Ctxt) A=B) = 
      minus-L-head
        []
        ([] ∷ (-S (_#[_]# Ctxt B)))
        (_#[_]# Ctxt A)
        (seq-exchange-head
          []
          []
          ([] ∷ (_#[_]# Ctxt A) ∷ (-S (_#[_]# Ctxt B)))
          ([] ∷ (-S (_#[_]# Ctxt B)) ∷ (_#[_]# Ctxt A))
          idLE
          (exLE
            (idLE {[]}))
          (minus-R-head
            []
            ([] ∷ (_#[_]# Ctxt A))
            (_#[_]# Ctxt B)
            (completeness2 (ctxtₛ Ctxt A=B))))
    completeness1 (ctxtₛ {A} {B} (◆C Ctxt) A=B) = 
      ◆-rule
        ([] ∷ ◆ (Ctxt #[ A ]#))
        ([] ∷ ◆ (Ctxt #[ B ]#))
        (◆∷ [] (Ctxt #[ A ]#) ◆[])
        (◆∷ [] (Ctxt #[ B ]#) ◆[])
        0
        refl
        refl
        refl
        (completeness1 (ctxtₛ Ctxt A=B))
    completeness1 (ctxtₛ oneC A=B) = 
      ax one
    completeness1 (substₛ {A} {B} {B'} {k} A=B) =
      substKeepProof
        (completeness1 A=B)
        k
        A
    completeness1 (asso-+S {A} {B} {B'}) =
      plus-R-head
        ([] ∷ (A +S (B +S B')))
        []
        (A +S B)
        B'
        (plus-L-head
          []
          ([] ∷ (A +S B) ∷ B')
          A
          (B +S B')
          (plus-L-head
            ([] ∷ A)
            ([] ∷ (A +S B) ∷ B')
            B
            B'
            (M-head
              ([] ∷ A ∷ B)
              ([] ∷ B')
              ([] ∷ (A +S B))
              ([] ∷ B')
              refl
              refl
              (plus-R-head
                ([] ∷ A ∷ B)
                []
                A
                B
                (M-head
                  ([] ∷ A)
                  ([] ∷ B)
                  ([] ∷ A)
                  ([] ∷ B)
                  refl
                  refl
                  (ax A)
                  (ax B)))
              (ax B'))))
    completeness1 (commu-+S {A} {B}) =
      plus-R-head
        ([] ∷ (A +S B))
        []
        B
        A
        (plus-L-head
          []
          ([] ∷ B ∷ A)
          A
          B
          (seq-exchange-head
            ([] ∷ A ∷ B)
            ([] ∷ A ∷ B)
            ([] ∷ A ∷ B)
            ([] ∷ B ∷ A)
            idLE
            (exLE idLE)
            (M-head
              ([] ∷ A)
              ([] ∷ B)
              ([] ∷ A)
              ([] ∷ B)
              refl
              refl
              (ax A)
              (ax B))))
    completeness1 (neutral-+S {A}) =
      plus-L-head
        []
        ([] ∷ A)
        A
        botAG
        (Z-L-head
          ([] ∷ A)
          ([] ∷ A)
          (ax A))
    completeness1 (opp-+S {A}) =
      Z-R-head
        ([] ∷ (A -S A))
        []
        (plus-L-head
          []
          []
          A
          (-S A)
          (minus-L-head
            ([] ∷ A)
            []
            A
            (ax A)))
    completeness1 (asso-⊔S {A} {B} {B'}) =
      max-L-head
        []
        ([] ∷ ((A ⊔S B) ⊔S B'))
        A
        (B ⊔S B')
        (max-R-head
          ([] ∷ A)
          []
          (A ⊔S B)
          B'
          (W-head
            ([] ∷ A)
            ([] ∷ A)
            ([] ∷ (A ⊔S B))
            ([] ∷ B')
            (max-R-head
              ([] ∷ A)
              []
              A
              B
              (W-head
                ([] ∷ A)
                ([] ∷ A)
                ([] ∷ A)
                ([] ∷ B)
                (ax A)))))
        (max-L-head
          []
          ([] ∷ ((A ⊔S B) ⊔S B'))
          B
          B'
          (max-R-head
            ([] ∷ B)
            []
            (A ⊔S B)
            B'
            (W-head
              ([] ∷ B)
              ([] ∷ B)
              ([] ∷ (A ⊔S B))
              ([] ∷ B')
              (max-R-head
                ([] ∷ B)
                []
                A
                B
                (hseq-exchange
                  (head (([] ∷ B) , [] ∷ B) ∣ ([] ∷ B , [] ∷ A))
                  (head (([] ∷ B) , ([] ∷ A)) ∣ (([] ∷ B) , ([] ∷ B)))
                  exHE-head
                  (W-head
                    ([] ∷ B)
                    ([] ∷ B)
                    ([] ∷ B)
                    ([] ∷ A)
                    (ax B))))))
          (max-R-head
            ([] ∷ B')
            []
            (A ⊔S B)
            B'
            (hseq-exchange
              (head (([] ∷ B') , [] ∷ B') ∣ ([] ∷ B' , [] ∷ (A ⊔S B)))
              (head (([] ∷ B') , ([] ∷ (A ⊔S B))) ∣ (([] ∷ B') , ([] ∷ B')))
              exHE-head
              (W-head
                ([] ∷ B')
                ([] ∷ B')
                ([] ∷ B')
                ([] ∷ (A ⊔S B))
                (ax B')))))
    completeness1 (commu-⊔S {A} {B}) =
      max-L-head
        []
        ([] ∷ (B ⊔S A))
        A
        B
        (max-R-head
          ([] ∷ A)
          []
          B
          A
          (hseq-exchange
            (head ([] ∷ A , [] ∷ A) ∣ ([] ∷ A , [] ∷ B))
            (head (([] ∷ A) , ([] ∷ B)) ∣ (([] ∷ A) , ([] ∷ A)))
            exHE-head
            (W-head
              ([] ∷ A)
              ([] ∷ A)
              ([] ∷ A)
              ([] ∷ B)
              (ax A))))
        (max-R-head
          ([] ∷ B)
          []
          B
          A
          (W-head
            ([] ∷ B)
            ([] ∷ B)
            ([] ∷ B)
            ([] ∷ A)
            (ax B)))
    completeness1 (abso-⊔S {A} {B}) =
      max-L-head
        []
        ([] ∷ A)
        A
        (A ⊓S B)
        (ax A)
        (min-L-head
          []
          ([] ∷ A)
          A
          B
          (W-head
            ([] ∷ A)
            ([] ∷ B)
            ([] ∷ A)
            ([] ∷ A)
            (ax A)))
    completeness1 (asso-⊓S {A} {B} {B'}) =
      min-R-head
        ([] ∷ (A ⊓S (B ⊓S B')))
        []
        (A ⊓S B)
        B'
        (min-R-head
          ([] ∷ (A ⊓S (B ⊓S B')))
          []
          A
          B
          (min-L-head
            []
            ([] ∷ A)
            A
            (B ⊓S B')
            (W-head
              ([] ∷ A)
              ([] ∷ (B ⊓S B'))
              ([] ∷ A)
              ([] ∷ A)
              (ax A)))
          (min-L-head
            []
            ([] ∷ B)
            A
            (B ⊓S B')
            (hseq-exchange
              (head ([] ∷ (B ⊓S B') , [] ∷ B) ∣ ([] ∷ A , [] ∷ B))
              (head (([] ∷ A) , ([] ∷ B)) ∣ (([] ∷ (B ⊓S B')) , ([] ∷ B)))
              exHE-head
              (W-head
                ([] ∷ (B ⊓S B'))
                ([] ∷ A)
                ([] ∷ B)
                ([] ∷ B)
                (min-L-head
                  []
                  ([] ∷ B)
                  B
                  B'
                  (W-head
                    ([] ∷ B)
                    ([] ∷ B')
                    ([] ∷ B)
                    ([] ∷ B)
                    (ax B)))))))
        (min-L-head
          []
          ([] ∷ B')
          A
          (B ⊓S B')
          (hseq-exchange
            (head ([] ∷ (B ⊓S B') , [] ∷ B') ∣ ([] ∷ A , [] ∷ B'))
            (head (([] ∷ A) , ([] ∷ B')) ∣ (([] ∷ (B ⊓S B')) , ([] ∷ B')))
            exHE-head
            (W-head
              ([] ∷ (B ⊓S B'))
              ([] ∷ A)
              ([] ∷ B')
              ([] ∷ B')
              (min-L-head
                []
                ([] ∷ B')
                B
                B'
                (hseq-exchange
                  (head ([] ∷ B' , [] ∷ B') ∣ ([] ∷ B , [] ∷ B'))
                  (head (([] ∷ B) , ([] ∷ B')) ∣ (([] ∷ B') , ([] ∷ B')))
                  exHE-head
                  (W-head
                    ([] ∷ B')
                    ([] ∷ B)
                    ([] ∷ B')
                    ([] ∷ B')
                    (ax B')))))))
    completeness1 (commu-⊓S {A} {B}) =
      min-R-head
        ([] ∷ (A ⊓S B))
        []
        B
        A
        (min-L-head
          []
          ([] ∷ B)
          A
          B
          (hseq-exchange
            (head ([] ∷ B , [] ∷ B) ∣ ([] ∷ A , [] ∷ B))
            (head ([] ∷ A , [] ∷ B) ∣ ([] ∷ B , [] ∷ B))
            exHE-head
            (W-head
              ([] ∷ B)
              ([] ∷ A)
              ([] ∷ B)
              ([] ∷ B)
              (ax B))))
        (min-L-head
          []
          ([] ∷ A)
          A
          B
          (W-head
            ([] ∷ A)
            ([] ∷ B)
            ([] ∷ A)
            ([] ∷ A)
            (ax A)))
    completeness1 (abso-⊓S {A} {B}) =
      min-L-head
        []
        ([] ∷ A)
        A
        (A ⊔S B)
        (W-head
          ([] ∷ A)
          ([] ∷ (A ⊔S B))
          ([] ∷ A)
          ([] ∷ A)
          (ax A))
    completeness1 (compa-+S {A} {B} {B'}) =
      min-L-head
        []
        ([] ∷ (A ⊓S B +S B'))
        (A ⊓S B +S B')
        (B +S B')
        (W-head
          ([] ∷ (A ⊓S B +S B'))
          ([] ∷ (B +S B'))
          ([] ∷ (A ⊓S B +S B'))
          ([] ∷ (A ⊓S B +S B'))
          (ax (A ⊓S B +S B')))
    completeness1 0≤1 =
      min-L-head
        []
        ([] ∷ botAG)
        botAG
        one
        (W-head
          ([] ∷ botAG)
          ([] ∷ one)
          ([] ∷ botAG)
          ([] ∷ botAG)
          (ax botAG))
    completeness1 ◆Zero =
      Z-R-head
        ([] ∷ ◆ botAG)
        []
        (◆-rule
          ([] ∷ ◆ botAG)
          []
          (◆∷ [] botAG ◆[])
          ◆[]
          0
          refl
          refl
          refl
          (Z-L-head
            []
            []
            Δ-ax))
    completeness1 ◆1≤1 =
      min-L-head
        []
        ([] ∷ ◆ one)
        (◆ one)
        one
        (W-head
          ([] ∷ ◆ one)
          ([] ∷ one)
          ([] ∷ ◆ one)
          ([] ∷ ◆ one)
          (ax (◆ one)))
    completeness1 (◆Linear A B) =
      plus-R-head
        ([] ∷ ◆ (A +S B))
        []
        (◆ A)
        (◆ B)
        (◆-rule
          ([] ∷ ◆ (A +S B))
          ([] ∷ ◆ A ∷ ◆ B)
          (◆∷ [] (A +S B) ◆[])
          (◆∷ ([] ∷ ◆ A) B (◆∷ [] A ◆[]))
          0
          refl
          refl
          refl
          (plus-L-head
            []
            ([] ∷ A ∷ B)
            A
            B
            (M-head
              ([] ∷ A)
              ([] ∷ B)
              ([] ∷ A)
              ([] ∷ B)
              refl
              refl
              (ax A)
              (ax B))))
    completeness1 (◆Monotony A B) = 
      min-L-head
        []
        ([] ∷ ◆ (A ⊓S B))
        (◆ (A ⊓S B))
        (◆ A)
        (W-head
          ([] ∷ ◆ (A ⊓S B))
          ([] ∷ ◆ A)
          ([] ∷ ◆ (A ⊓S B))
          ([] ∷ ◆ (A ⊓S B))
          (ax (◆ (A ⊓S B))))

    completeness2 :
      {A B : Term} ->
      A ≡ₛ B ->
      MGA (head ([] ∷ B , [] ∷ A))
    completeness2 (reflₛ {A}) =
      ax A
    completeness2 (transₛ {A} {B} {B'} A=B A=B₁) =
      cut-head
        []
        ([] ∷ B')
        ([] ∷ A)
        []
        B
        refl
        refl
        (completeness2 A=B)
        (completeness2 A=B₁)
    completeness2 (symₛ A=B) =
      completeness1 A=B
    completeness2 (ctxtₛ ● A=B) =
      completeness2 A=B
    completeness2 (ctxtₛ (CC x) A=B) =
      ax x
    completeness2 (ctxtₛ (varC x) A=B) =
      ax (varAG x)
    completeness2 (ctxtₛ botC A=B) =
      ax botAG
    completeness2 (ctxtₛ {B} {A} (Ctxt ⊔C Ctxt₁) A=B) = 
      max-L-head
        []
        ([] ∷ ((_#[_]# Ctxt B) ⊔S (_#[_]# Ctxt₁ B)))
        (_#[_]# Ctxt A)
        (_#[_]# Ctxt₁ A)
        (max-R-head
          ([] ∷ (_#[_]# Ctxt A))
          []
          (_#[_]# Ctxt B)
          (_#[_]# Ctxt₁ B)
          (W-head
            ([] ∷ _#[_]# Ctxt A)
            ([] ∷ _#[_]# Ctxt A)
            ([] ∷ _#[_]# Ctxt B)
            ([] ∷ _#[_]# Ctxt₁ B)
            (completeness2 (ctxtₛ Ctxt A=B))))
        (max-R-head
          ([] ∷ (_#[_]# Ctxt₁ A))
          []
          (_#[_]# Ctxt B)
          (_#[_]# Ctxt₁ B)
          (hseq-exchange
            (head (([] ∷ _#[_]# Ctxt₁ A) , [] ∷ _#[_]# Ctxt₁ B) ∣ ([] ∷ _#[_]# Ctxt₁ A , [] ∷ _#[_]# Ctxt B))
            (head (([] ∷ (_#[_]# Ctxt₁ A)) , ([] ∷ (_#[_]# Ctxt B))) ∣ (([] ∷ (_#[_]# Ctxt₁ A)) , ([] ∷ (_#[_]# Ctxt₁ B))))
            exHE-head
            (W-head
              ([] ∷ _#[_]# Ctxt₁ A)
              ([] ∷ _#[_]# Ctxt₁ A)
              ([] ∷ _#[_]# Ctxt₁ B)
              ([] ∷ _#[_]# Ctxt B)
              (completeness2 (ctxtₛ Ctxt₁ A=B)))))
    completeness2 (ctxtₛ {B} {A} (Ctxt +C Ctxt₁) A=B) = 
      plus-R-head
        ([] ∷ ((_#[_]# Ctxt A) +S (_#[_]# Ctxt₁ A)))
        []
        (_#[_]# Ctxt B)
        (_#[_]# Ctxt₁ B)
        (plus-L-head
          []
          ([] ∷ _#[_]# Ctxt B ∷ _#[_]# Ctxt₁ B)
          (_#[_]# Ctxt A)
          (_#[_]# Ctxt₁ A)
          (M-head
            ([] ∷ _#[_]# Ctxt A)
            ([] ∷ _#[_]# Ctxt₁ A)
            ([] ∷ _#[_]# Ctxt B)
            ([] ∷ _#[_]# Ctxt₁ B)
            refl
            refl
            (completeness2 (ctxtₛ Ctxt A=B))
            (completeness2 (ctxtₛ Ctxt₁ A=B))))
    completeness2 (ctxtₛ {B} {A} (Ctxt ⊓C Ctxt₁) A=B) = 
      min-R-head
        ([] ∷ ((_#[_]# Ctxt A) ⊓S (_#[_]# Ctxt₁ A)))
        []
        (_#[_]# Ctxt B)
        (_#[_]# Ctxt₁ B)
        (min-L-head
          []
          ([] ∷ (_#[_]# Ctxt B))
          (_#[_]# Ctxt A)
          (_#[_]# Ctxt₁ A)
          (W-head
            ([] ∷ _#[_]# Ctxt A)
            ([] ∷ _#[_]# Ctxt₁ A)
            ([] ∷ _#[_]# Ctxt B)
            ([] ∷ _#[_]# Ctxt B)
            (completeness2 (ctxtₛ Ctxt A=B))))
        (min-L-head
          []
          ([] ∷ (_#[_]# Ctxt₁ B))
          (_#[_]# Ctxt A)
          (_#[_]# Ctxt₁ A)
          (hseq-exchange
            (head (([] ∷ _#[_]# Ctxt₁ A) , [] ∷ _#[_]# Ctxt₁ B) ∣ ([] ∷ _#[_]# Ctxt A , [] ∷ _#[_]# Ctxt₁ B))
            (head (([] ∷ (_#[_]# Ctxt A)) , ([] ∷ (_#[_]# Ctxt₁ B))) ∣ (([] ∷ (_#[_]# Ctxt₁ A)) , ([] ∷ (_#[_]# Ctxt₁ B))))
            exHE-head
            (W-head
              ([] ∷ _#[_]# Ctxt₁ A)
              ([] ∷ _#[_]# Ctxt A)
              ([] ∷ _#[_]# Ctxt₁ B)
              ([] ∷ _#[_]# Ctxt₁ B)
              (completeness2 (ctxtₛ Ctxt₁ A=B)))))
    completeness2 (ctxtₛ {B} {A} (-C Ctxt) A=B) = 
      minus-L-head
        []
        ([] ∷ (-S (_#[_]# Ctxt B)))
        (_#[_]# Ctxt A)
        (seq-exchange-head
          []
          []
          ([] ∷ (_#[_]# Ctxt A) ∷ (-S (_#[_]# Ctxt B)))
          ([] ∷ (-S (_#[_]# Ctxt B)) ∷ (_#[_]# Ctxt A))
          idLE
          (exLE
            (idLE {[]}))
          (minus-R-head
            []
            ([] ∷ (_#[_]# Ctxt A))
            (_#[_]# Ctxt B)
            (completeness1 (ctxtₛ Ctxt A=B))))
    completeness2 (ctxtₛ {B} {A} (◆C Ctxt) A=B) = 
      ◆-rule
        ([] ∷ ◆ (Ctxt #[ A ]#))
        ([] ∷ ◆ (Ctxt #[ B ]#))
        (◆∷ [] (Ctxt #[ A ]#) ◆[])
        (◆∷ [] (Ctxt #[ B ]#) ◆[])
        0
        refl
        refl
        refl
        (completeness2 (ctxtₛ Ctxt A=B))
    completeness2 (ctxtₛ oneC A=B) = 
      ax one
    completeness2 (substₛ {A} {k = k} A=B) = 
      substKeepProof
        (completeness2 A=B)
        k
        A
    completeness2 (asso-+S {A} {B} {B'}) = 
      plus-L-head
        []
        ([] ∷ (A +S (B +S B')))
        (A +S B)
        B'
        (plus-R-head
          ([] ∷ (A +S B) ∷ B')
          []
          A
          (B +S B')
          (plus-R-head
            ([] ∷ (A +S B) ∷ B')
            ([] ∷ A)
            B
            B'
            (M-head
              ([] ∷ (A +S B))
              ([] ∷ B')
              ([] ∷ A ∷ B)
              ([] ∷ B')
              refl
              refl
              (plus-L-head
                []
                ([] ∷ A ∷ B)
                A
                B
                (M-head
                  ([] ∷ A)
                  ([] ∷ B)
                  ([] ∷ A)
                  ([] ∷ B)
                  refl
                  refl
                  (ax A)
                  (ax B)))
              (ax B'))))
    completeness2 (commu-+S {B} {A}) =
      plus-R-head
        ([] ∷ (A +S B))
        []
        B
        A
        (plus-L-head
          []
          ([] ∷ B ∷ A)
          A
          B
          (seq-exchange-head
            ([] ∷ A ∷ B)
            ([] ∷ A ∷ B)
            ([] ∷ A ∷ B)
            ([] ∷ B ∷ A)
            idLE
            (exLE idLE)
            (M-head
              ([] ∷ A)
              ([] ∷ B)
              ([] ∷ A)
              ([] ∷ B)
              refl
              refl
              (ax A)
              (ax B))))
    completeness2 (neutral-+S {A}) = 
      plus-R-head
        ([] ∷ A)
        []
        A
        botAG
        (Z-R-head
          ([] ∷ A)
          ([] ∷ A)
          (ax A))
    completeness2 (opp-+S {A}) =
      plus-R-head
        ([] ∷ botAG)
        []
        A
        (-S A)
        (Z-L-head
          []
          ([] ∷ A ∷ (-S A))
          (minus-R-head
            []
            ([] ∷ A)
            A
            (ax A)))
    completeness2 (asso-⊔S {A} {B} {B'}) =
      max-L-head
        []
        ([] ∷ (A ⊔S (B ⊔S B')))
        (A ⊔S B)
        B'
        (max-L-head
          []
          ([] ∷ (A ⊔S (B ⊔S B')))
          A
          B
          (max-R-head
            ([] ∷ A)
            []
            A
            (B ⊔S B')
            (W-head
              ([] ∷ A)
              ([] ∷ A)
              ([] ∷ A)
              ([] ∷ (B ⊔S B'))
              (ax A)))
          (max-R-head
            ([] ∷ B)
            []
            A
            (B ⊔S B')
            (max-R
              (head ([] ∷ B , [] ∷ A))
              ([] ∷ B)
              []
              B
              B'
              (hseq-exchange
                (head ([] ∷ B , [] ∷ B) ∣ ([] ∷ B , [] ∷ A) ∣ ([] ∷ B , [] ∷ B'))
                (head (([] ∷ B) , ([] ∷ A)) ∣ (([] ∷ B) , ([] ∷ B)) ∣ (([] ∷ B) , ([] ∷ B')))
                (indHE
                  (head ([] ∷ B , [] ∷ B) ∣ ([] ∷ B , [] ∷ A))
                  (head ([] ∷ B , [] ∷ A) ∣ ([] ∷ B , [] ∷ B))
                  exHE-head)
                (W
                  (head ([] ∷ B , [] ∷ B))
                  ([] ∷ B)
                  ([] ∷ B)
                  ([] ∷ A)
                  ([] ∷ B')
                  (W-head
                    ([] ∷ B)
                    ([] ∷ B)
                    ([] ∷ B)
                    ([] ∷ A)
                    (ax B)))))))
        (max-R-head
          ([] ∷ B')
          []
          A
          (B ⊔S B')
          (hseq-exchange
            (head (([] ∷ B') , ([] ∷ (B ⊔S B'))) ∣ (([] ∷ B') , ([] ∷ A)))
            (head (([] ∷ B') , ([] ∷ A)) ∣ (([] ∷ B') , ([] ∷ (B ⊔S B'))))
            exHE-head
            (W-head
              ([] ∷ B')
              ([] ∷ B')
              ([] ∷ (B ⊔S B'))
              ([] ∷ A)
              (max-R-head
                ([] ∷ B')
                []
                B
                B'
                (hseq-exchange
                  (head (([] ∷ B') , ([] ∷ B')) ∣ (([] ∷ B') , ([] ∷ B)))
                  (head (([] ∷ B') , ([] ∷ B)) ∣ (([] ∷ B') , ([] ∷ B')))
                  exHE-head
                  (W-head
                    ([] ∷ B')
                    ([] ∷ B')
                    ([] ∷ B')
                    ([] ∷ B)
                    (ax B')))))))
    completeness2 (commu-⊔S {B} {A}) = 
      max-L-head
        []
        ([] ∷ (B ⊔S A))
        A
        B
        (max-R-head
          ([] ∷ A)
          []
          B
          A
          (hseq-exchange
            (head ([] ∷ A , [] ∷ A) ∣ ([] ∷ A , [] ∷ B))
            (head (([] ∷ A) , ([] ∷ B)) ∣ (([] ∷ A) , ([] ∷ A)))
            exHE-head
            (W-head
              ([] ∷ A)
              ([] ∷ A)
              ([] ∷ A)
              ([] ∷ B)
              (ax A))))
        (max-R-head
          ([] ∷ B)
          []
          B
          A
          (W-head
            ([] ∷ B)
            ([] ∷ B)
            ([] ∷ B)
            ([] ∷ A)
            (ax B)))
    completeness2 (abso-⊔S {A} {B}) =
      max-R-head
        ([] ∷ A)
        []
        A
        (A ⊓S B)
        (W-head
          ([] ∷ A)
          ([] ∷ A)
          ([] ∷ A)
          ([] ∷ (A ⊓S B))
          (ax A))
    completeness2 (asso-⊓S {A} {B} {B'}) = 
      min-R-head
        ([] ∷ ((A ⊓S B) ⊓S B'))
        []
        A
        (B ⊓S B')
        (min-L-head
          []
          ([] ∷ A)
          (A ⊓S B)
          B'
          (W-head
            ([] ∷ (A ⊓S B))
            ([] ∷ B')
            ([] ∷ A)
            ([] ∷ A)
            (min-L-head
              []
              ([] ∷ A)
              A
              B
              (W-head
                ([] ∷ A)
                ([] ∷ B)
                ([] ∷ A)
                ([] ∷ A)
                (ax A)))))
        (min-R-head
          ([] ∷ ((A ⊓S B) ⊓S B'))
          []
          B
          B'
          (min-L-head
            []
            ([] ∷ B)
            (A ⊓S B)
            B'
            (W-head
              ([] ∷ (A ⊓S B))
              ([] ∷ B')
              ([] ∷ B)
              ([] ∷ B)
              (min-L-head
                []
                ([] ∷ B)
                A
                B
                (hseq-exchange
                  (head ([] ∷ B , [] ∷ B) ∣ ([] ∷ A , [] ∷ B))
                  (head (([] ∷ A) , ([] ∷ B)) ∣ (([] ∷ B) , ([] ∷ B)))
                  exHE-head
                  (W-head
                    ([] ∷ B)
                    ([] ∷ A)
                    ([] ∷ B)
                    ([] ∷ B)
                    (ax B))))))
          (min-L-head
            []
            ([] ∷ B')
            (A ⊓S B)
            B'
            (hseq-exchange
              (head ([] ∷ B' , [] ∷ B') ∣ ([] ∷ (A ⊓S B) , [] ∷ B'))
              (head (([] ∷ (A ⊓S B)) , ([] ∷ B')) ∣ (([] ∷ B') , ([] ∷ B')))
              exHE-head
              (W-head
                ([] ∷ B')
                ([] ∷ (A ⊓S B))
                ([] ∷ B')
                ([] ∷ B')
                (ax B')))))
    completeness2 (commu-⊓S {B} {A}) = 
      min-R-head
        ([] ∷ (A ⊓S B))
        []
        B
        A
        (min-L-head
          []
          ([] ∷ B)
          A
          B
          (hseq-exchange
            (head ([] ∷ B , [] ∷ B) ∣ ([] ∷ A , [] ∷ B))
            (head ([] ∷ A , [] ∷ B) ∣ ([] ∷ B , [] ∷ B))
            exHE-head
            (W-head
              ([] ∷ B)
              ([] ∷ A)
              ([] ∷ B)
              ([] ∷ B)
              (ax B))))
        (min-L-head
          []
          ([] ∷ A)
          A
          B
          (W-head
            ([] ∷ A)
            ([] ∷ B)
            ([] ∷ A)
            ([] ∷ A)
            (ax A)))
    completeness2 (abso-⊓S {A} {B}) =
      min-R-head
        ([] ∷ A)
        []
        A
        (A ⊔S B)
        (ax A)
        (max-R-head
          ([] ∷ A)
          []
          A
          B
          (W-head
            ([] ∷ A)
            ([] ∷ A)
            ([] ∷ A)
            ([] ∷ B)
            (ax A)))
    completeness2 (compa-+S {A} {B} {B'}) =
      min-R-head
        ([] ∷ (A ⊓S B +S B'))
        []
        (A ⊓S B +S B')
        (B +S B')
        (ax (A ⊓S B +S B'))
        (plus-L-head
          []
          ([] ∷ (B +S B'))
          (A ⊓S B)
          B'
          (plus-R-head
            ([] ∷ (A ⊓S B) ∷ B')
            []
            B
            B'
            (M-head
              ([] ∷ (A ⊓S B))
              ([] ∷ B')
              ([] ∷ B)
              ([] ∷ B')
              refl
              refl
              (min-L-head
                []
                ([] ∷ B)
                A
                B
                (hseq-exchange
                  (head ([] ∷ B , [] ∷ B) ∣ ([] ∷ A , [] ∷ B))
                  (head ([] ∷ A , [] ∷ B) ∣ ([] ∷ B , [] ∷ B))
                  exHE-head
                  (W-head
                    ([] ∷ B)
                    ([] ∷ A)
                    ([] ∷ B)
                    ([] ∷ B)
                    (ax B))))
              (ax B'))))
    completeness2 0≤1 =
      min-R-head
        ([] ∷ botAG)
        []
        botAG
        one
        (ax botAG)
        (Z-L-head
          []
          ([] ∷ one)
          1-ax)
    completeness2 ◆Zero =
      Z-L-head
        []
        ([] ∷ ◆ botAG)
        (◆-rule
          []
          ([] ∷ ◆ botAG)
          ◆[]
          (◆∷ [] botAG ◆[])
          0
          refl
          refl
          refl
          (Z-R-head
            []
            []
            Δ-ax))
    completeness2 ◆1≤1 =
      min-R-head
        ([] ∷ ◆ one)
        []
        (◆ one)
        one
        (ax (◆ one))
        (◆-rule
          ([] ∷ ◆ one)
          []
          (◆∷ [] one ◆[])
          ◆[]
          1
          refl
          refl
          refl
          (ax one))
    completeness2 (◆Linear A B) =
      plus-L-head
        []
        ([] ∷ ◆ (A +S B))
        (◆ A)
        (◆ B)
        (◆-rule
          ([] ∷ ◆ A ∷ ◆ B)
          ([] ∷ ◆ (A +S B))
          (◆∷ ([] ∷ ◆ A) B (◆∷ [] A ◆[]))
          (◆∷ [] (A +S B) ◆[])
          0
          refl
          refl
          refl
          (plus-R-head
            ([] ∷ A ∷ B)
            []
            A
            B
            (M-head
              ([] ∷ A)
              ([] ∷ B)
              ([] ∷ A)
              ([] ∷ B)
              refl
              refl
              (ax A)
              (ax B))))
    completeness2 (◆Monotony A B) =
      min-R-head
        ([] ∷ ◆ (A ⊓S B))
        []
        (◆ (A ⊓S B))
        (◆ A)
        (ax (◆ (A ⊓S B)))
        (◆-rule
          ([] ∷ ◆ (A ⊓S B))
          ([] ∷ ◆ A)
          (◆∷ [] (A ⊓S B) ◆[])
          (◆∷ [] A ◆[])
          0
          refl
          refl
          refl
          (min-L-head
            []
            ([] ∷ A)
            A
            B
            (W-head
              ([] ∷ A)
              ([] ∷ B)
              ([] ∷ A)
              ([] ∷ A)
              (ax A))))

  completeness :
    {A : Term} ->
    botAG ≤S A ->
    MGA (head ([] , [] ∷ A))
  completeness {A} 0≤A =
    cut-head
      []
      []
      ([] ∷ A)
      []
      (botAG ⊓S A)
      refl
      refl
      (min-L-head
        []
        ([] ∷ A)
        botAG
        A
        (hseq-exchange
          (head ([] ∷ A , [] ∷ A) ∣ ([] ∷ botAG , [] ∷ A))
          (head (([] ∷ botAG) , ([] ∷ A)) ∣ (([] ∷ A) , ([] ∷ A)))
          exHE-head
          (W-head
            ([] ∷ A)
            ([] ∷ botAG)
            ([] ∷ A)
            ([] ∷ A)
            (ax A))))
      (cut-head
        []
        []
        ([] ∷ (botAG ⊓S A))
        []
        botAG
        refl
        refl
        (completeness2 0≤A)
        (Z-R-head
          []
          []
          Δ-ax))
