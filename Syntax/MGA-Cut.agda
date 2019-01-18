module Syntax.MGA-Cut where
  {- STDLIB -}
  open import Equality
  open import Nat

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq
  open import Syntax.HSeq

  {- Semantic -}


  data MGA : HSeq -> Set where
    -- Axioms
    ax :
      (A : Term) ->
      MGA (head ([] ∷ A , [] ∷ A))
    Δ-ax :
      MGA (head ([] , []))
    1-ax :
      MGA (head ([] , [] ∷ one))
    -- Structural Rules
    W :
      (G : HSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      MGA (G ∣ (Γ1 , Δ1)) ->
      MGA (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      MGA (G ∣ (Γ , Δ) ∣ (Γ , Δ)) ->
      MGA (G ∣ (Γ , Δ))
    S :
      (G : HSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      {wΓ wΔ : ListTerm} ->
      (wΓ ≡ union Γ1 Γ2) ->
      (wΔ ≡ union Δ1 Δ2) ->
      MGA (G ∣ (wΓ , wΔ)) ->
      MGA (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    M :
      (G : HSeq) ->
      (T T' D D' : ListTerm) ->
      {wT wD : ListTerm} ->
      wT ≡ union T T' ->
      wD ≡ union D D' ->
      MGA (G ∣ (T , D)) ->
      MGA (G ∣ (T' , D')) ->
      MGA (G ∣ (wT , wD))
    W-head :
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      MGA (head (Γ1 , Δ1)) ->
      MGA (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C-head :
      (Γ Δ : ListTerm) ->
      MGA (head (Γ , Δ) ∣ (Γ , Δ)) ->
      MGA (head (Γ , Δ))
    S-head :
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      {wΓ wΔ : ListTerm} ->
      (wΓ ≡ union Γ1 Γ2) ->
      (wΔ ≡ union Δ1 Δ2) ->
      MGA (head (wΓ , wΔ)) ->
      MGA (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    M-head :
      (T T' D D' : ListTerm) ->
      {wT wD : ListTerm} ->
      wT ≡ union T T' ->
      wD ≡ union D D' ->
      MGA (head (T , D)) ->
      MGA (head (T' , D')) ->
      MGA (head (wT , wD))
    -- Logical Rules
    Z-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      MGA (G ∣ (Γ , Δ)) ->
      MGA (G ∣ (Γ ∷ botAG , Δ))
    Z-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      MGA (G ∣ (Γ , Δ)) ->
      MGA (G ∣ (Γ , Δ ∷ botAG))
    minus-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      MGA (G ∣ (Γ , Δ ∷ A)) ->
      MGA (G ∣ (Γ ∷ (-S A) , Δ))
    minus-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      MGA (G ∣ (Γ ∷ A , Δ)) ->
      MGA (G ∣ (Γ , Δ ∷ (-S A)))
    plus-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA (G ∣(Γ ∷ A ∷ B , Δ)) ->
      MGA (G ∣ (Γ ∷ (A +S B), Δ))
    plus-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA (G ∣ (Γ , Δ ∷ A ∷ B)) ->
      MGA (G ∣ (Γ , Δ ∷ (A +S B)))
    max-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA (G ∣(Γ ∷ A , Δ)) ->
      MGA (G ∣(Γ ∷ B , Δ)) ->
      MGA (G ∣(Γ ∷ (A ⊔S B), Δ))
    max-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA (G ∣(Γ , Δ ∷ A)∣(Γ , Δ ∷ B)) ->
      MGA (G ∣(Γ , Δ ∷ (A ⊔S B)))
    min-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA (G ∣ (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ)) ->
      MGA (G ∣ (Γ ∷ (A ⊓S B), Δ))
    min-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA (G ∣ (Γ , Δ ∷ A)) ->
      MGA (G ∣ (Γ , Δ ∷ B)) ->
      MGA (G ∣ (Γ , Δ ∷ (A ⊓S B)))
    Z-L-head :  
      (Γ Δ : ListTerm) ->
      MGA (head (Γ , Δ)) ->
      MGA (head (Γ ∷ botAG , Δ))
    Z-R-head :
      (Γ Δ : ListTerm) ->
      MGA (head (Γ , Δ)) ->
      MGA (head (Γ , Δ ∷ botAG))
    minus-L-head :
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      MGA (head (Γ , Δ ∷ A)) ->
      MGA (head (Γ ∷ (-S A), Δ))
    minus-R-head :
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      MGA (head (Γ ∷ A , Δ)) ->
      MGA (head (Γ , Δ ∷ (-S A)))
    plus-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA (head (Γ ∷ A ∷ B , Δ)) ->
      MGA (head (Γ ∷ (A +S B), Δ))
    plus-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA (head(Γ , Δ ∷ A ∷ B)) ->
      MGA (head(Γ , Δ ∷ (A +S B)))
    max-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA (head(Γ ∷ A , Δ)) ->
      MGA (head(Γ ∷ B , Δ)) ->
      MGA (head(Γ ∷ (A ⊔S B), Δ))
    max-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA (head(Γ , Δ ∷ A)∣(Γ , Δ ∷ B)) ->
      MGA (head(Γ , Δ ∷ (A ⊔S B)))
    min-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA (head (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ)) ->
      MGA (head (Γ ∷ (A ⊓S B), Δ))
    min-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA (head (Γ , Δ ∷ A)) ->
      MGA (head (Γ , Δ ∷ B)) ->
      MGA (head (Γ , Δ ∷ (A ⊓S B)))
    seq-exchange :
      (G : HSeq) ->
      (Γ Γ' Δ Δ' : ListTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      MGA (G ∣ (Γ , Δ)) ->
      MGA (G ∣ (Γ' , Δ'))
    -- Exchange Rules
    seq-exchange-head :
      (Γ Γ' Δ Δ' : ListTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      MGA (head (Γ , Δ)) ->
      MGA (head (Γ' , Δ'))
    hseq-exchange :
      (G G' : HSeq) ->
      HSeqExchange G G' ->
      MGA G ->
      MGA G'
    -- Modal rule
    ◆-rule :
      (Γ Δ : ListTerm) ->
      (◆Γ : ◆List Γ) ->
      (◆Δ : ◆List Δ) ->
      (k : ℕ) ->
      {wΓ wΔ wΔ' : ListTerm} ->
      (wΓ ≡ remove◆ ◆Γ) ->
      (wΔ ≡ union (remove◆ ◆Δ) (constantList one k)) ->
      wΔ' ≡ union Δ (constantList one k) ->
      MGA (head (wΓ , wΔ)) ->
      MGA (head (Γ , wΔ'))
    -- Cut rule
    cut-head :
      (Γ₁ Γ₂ Δ₁ Δ₂ : ListTerm) ->
      (A : Term) ->
      {wT wD : ListTerm} ->
      wT ≡ union Γ₁ Γ₂ ->
      wD ≡ union Δ₁ Δ₂ ->
      MGA (head (Γ₁ ∷ A , Δ₁)) ->
      MGA (head (Γ₂ , Δ₂ ∷ A)) ->
      MGA (head (wT , wD))
    cut :
      (G : HSeq) ->
      (Γ₁ Γ₂ Δ₁ Δ₂ : ListTerm) ->
      (A : Term) ->
      {wT wD : ListTerm} ->
      wT ≡ union Γ₁ Γ₂ ->
      wD ≡ union Δ₁ Δ₂ ->
      MGA (G ∣ (Γ₁ ∷ A , Δ₁)) ->
      MGA (G ∣ (Γ₂ , Δ₂ ∷ A)) ->
      MGA (G ∣ (wT , wD))

  MGACong :
    {G G' : HSeq} ->
    MGA G ->
    G ≡ G' ->
    MGA G'
  MGACong PG refl = PG
