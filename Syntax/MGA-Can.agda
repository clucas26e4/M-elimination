module Syntax.MGA-Can where
  {- STDLIB -}
  open import Equality
  open import Nat

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq
  open import Syntax.HSeq

  {- Semantic -}


  data MGA-Can : HSeq -> Set where
    -- Axioms
    ax :
      (A : Term) ->
      MGA-Can (head ([] ∷ A , [] ∷ A))
    Δ-ax :
      MGA-Can (head ([] , []))
    1-ax :
      MGA-Can (head ([] , [] ∷ one))
    -- Structural Rules
    W :
      (G : HSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      MGA-Can (G ∣ (Γ1 , Δ1)) ->
      MGA-Can (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      MGA-Can (G ∣ (Γ , Δ) ∣ (Γ , Δ)) ->
      MGA-Can (G ∣ (Γ , Δ))
    S :
      (G : HSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      {wΓ wΔ : ListTerm} ->
      (wΓ ≡ union Γ1 Γ2) ->
      (wΔ ≡ union Δ1 Δ2) ->
      MGA-Can (G ∣ (wΓ , wΔ)) ->
      MGA-Can (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    M :
      (G : HSeq) ->
      (T T' D D' : ListTerm) ->
      {wT wD : ListTerm} ->
      wT ≡ union T T' ->
      wD ≡ union D D' ->
      MGA-Can (G ∣ (T , D)) ->
      MGA-Can (G ∣ (T' , D')) ->
      MGA-Can (G ∣ (wT , wD))
    W-head :
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      MGA-Can (head (Γ1 , Δ1)) ->
      MGA-Can (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C-head :
      (Γ Δ : ListTerm) ->
      MGA-Can (head (Γ , Δ) ∣ (Γ , Δ)) ->
      MGA-Can (head (Γ , Δ))
    S-head :
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      {wΓ wΔ : ListTerm} ->
      (wΓ ≡ union Γ1 Γ2) ->
      (wΔ ≡ union Δ1 Δ2) ->
      MGA-Can (head (wΓ , wΔ)) ->
      MGA-Can (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    M-head :
      (T T' D D' : ListTerm) ->
      {wT wD : ListTerm} ->
      wT ≡ union T T' ->
      wD ≡ union D D' ->
      MGA-Can (head (T , D)) ->
      MGA-Can (head (T' , D')) ->
      MGA-Can (head (wT , wD))
    -- Logical Rules
    Z-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      MGA-Can (G ∣ (Γ , Δ)) ->
      MGA-Can (G ∣ (Γ ∷ botAG , Δ))
    Z-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      MGA-Can (G ∣ (Γ , Δ)) ->
      MGA-Can (G ∣ (Γ , Δ ∷ botAG))
    minus-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      MGA-Can (G ∣ (Γ , Δ ∷ A)) ->
      MGA-Can (G ∣ (Γ ∷ (-S A) , Δ))
    minus-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      MGA-Can (G ∣ (Γ ∷ A , Δ)) ->
      MGA-Can (G ∣ (Γ , Δ ∷ (-S A)))
    plus-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA-Can (G ∣(Γ ∷ A ∷ B , Δ)) ->
      MGA-Can (G ∣ (Γ ∷ (A +S B), Δ))
    plus-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA-Can (G ∣ (Γ , Δ ∷ A ∷ B)) ->
      MGA-Can (G ∣ (Γ , Δ ∷ (A +S B)))
    max-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA-Can (G ∣(Γ ∷ A , Δ)) ->
      MGA-Can (G ∣(Γ ∷ B , Δ)) ->
      MGA-Can (G ∣(Γ ∷ (A ⊔S B), Δ))
    max-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA-Can (G ∣(Γ , Δ ∷ A)∣(Γ , Δ ∷ B)) ->
      MGA-Can (G ∣(Γ , Δ ∷ (A ⊔S B)))
    min-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA-Can (G ∣ (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ)) ->
      MGA-Can (G ∣ (Γ ∷ (A ⊓S B), Δ))
    min-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA-Can (G ∣ (Γ , Δ ∷ A)) ->
      MGA-Can (G ∣ (Γ , Δ ∷ B)) ->
      MGA-Can (G ∣ (Γ , Δ ∷ (A ⊓S B)))
    Z-L-head :  
      (Γ Δ : ListTerm) ->
      MGA-Can (head (Γ , Δ)) ->
      MGA-Can (head (Γ ∷ botAG , Δ))
    Z-R-head :
      (Γ Δ : ListTerm) ->
      MGA-Can (head (Γ , Δ)) ->
      MGA-Can (head (Γ , Δ ∷ botAG))
    minus-L-head :
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      MGA-Can (head (Γ , Δ ∷ A)) ->
      MGA-Can (head (Γ ∷ (-S A), Δ))
    minus-R-head :
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      MGA-Can (head (Γ ∷ A , Δ)) ->
      MGA-Can (head (Γ , Δ ∷ (-S A)))
    plus-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA-Can (head (Γ ∷ A ∷ B , Δ)) ->
      MGA-Can (head (Γ ∷ (A +S B), Δ))
    plus-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA-Can (head(Γ , Δ ∷ A ∷ B)) ->
      MGA-Can (head(Γ , Δ ∷ (A +S B)))
    max-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA-Can (head(Γ ∷ A , Δ)) ->
      MGA-Can (head(Γ ∷ B , Δ)) ->
      MGA-Can (head(Γ ∷ (A ⊔S B), Δ))
    max-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA-Can (head(Γ , Δ ∷ A)∣(Γ , Δ ∷ B)) ->
      MGA-Can (head(Γ , Δ ∷ (A ⊔S B)))
    min-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA-Can (head (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ)) ->
      MGA-Can (head (Γ ∷ (A ⊓S B), Δ))
    min-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      MGA-Can (head (Γ , Δ ∷ A)) ->
      MGA-Can (head (Γ , Δ ∷ B)) ->
      MGA-Can (head (Γ , Δ ∷ (A ⊓S B)))
    seq-exchange :
      (G : HSeq) ->
      (Γ Γ' Δ Δ' : ListTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      MGA-Can (G ∣ (Γ , Δ)) ->
      MGA-Can (G ∣ (Γ' , Δ'))
    -- Exchange Rules
    seq-exchange-head :
      (Γ Γ' Δ Δ' : ListTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      MGA-Can (head (Γ , Δ)) ->
      MGA-Can (head (Γ' , Δ'))
    hseq-exchange :
      (G G' : HSeq) ->
      HSeqExchange G G' ->
      MGA-Can G ->
      MGA-Can G'
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
      MGA-Can (head (wΓ , wΔ)) ->
      MGA-Can (head (Γ , wΔ'))
    -- Cut rule
    can-rule-head :
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      MGA-Can (head (Γ ∷ A , Δ ∷ A)) ->
      MGA-Can (head (Γ , Δ))
    can-rule :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      MGA-Can (G ∣ (Γ ∷ A , Δ ∷ A)) ->
      MGA-Can (G ∣ (Γ , Δ))

  MGA-CanCong :
    {G G' : HSeq} ->
    MGA-Can G ->
    G ≡ G' ->
    MGA-Can G'
  MGA-CanCong PG refl = PG
