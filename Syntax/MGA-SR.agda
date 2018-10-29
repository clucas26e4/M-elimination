module Syntax.MGA-SR where
  {- STDLIB -}
  open import Equality
  open import Nat
  open import Data.Product

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.LTerm
  open import Syntax.ListLTerm
  open import Syntax.LSeq
  open import Syntax.LHSeq
  open import Syntax.ListLTerm.Properties
  open import Syntax.LHSeq.Properties

  {- Semantic -}

  data MGA-SR†* : LHSeq -> Set where
    -- Axiom
    ax :
      MGA-SR†* (head ([] , []))
    -- Structural Rules
    W :
      (G : LHSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListLTerm) ->
      MGA-SR†* (G ∣ (Γ1 , Δ1)) ->
      MGA-SR†* (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      MGA-SR†* (G ∣ (Γ , Δ) ∣ (Γ , Δ)) ->
      MGA-SR†* (G ∣ (Γ , Δ))
    S :
      (G : LHSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListLTerm) ->
      {wΓ wΔ : ListLTerm} ->
      (wΓ ≡ union Γ1 Γ2) ->
      (wΔ ≡ union Δ1 Δ2) ->
      MGA-SR†* (G ∣ (wΓ , wΔ)) ->
      MGA-SR†* (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    Id-rule :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : LTerm) ->
      MGA-SR†* (G ∣ (Γ , Δ)) ->
      MGA-SR†* (G ∣ (Γ ∷ A , Δ ∷ A))
    W-head :
      (Γ1 Γ2 Δ1 Δ2 : ListLTerm) ->
      MGA-SR†* (head (Γ1 , Δ1)) ->
      MGA-SR†* (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C-head :
      (Γ Δ : ListLTerm) ->
      MGA-SR†* (head (Γ , Δ) ∣ (Γ , Δ)) ->
      MGA-SR†* (head (Γ , Δ))
    S-head :
      (Γ1 Γ2 Δ1 Δ2 : ListLTerm) ->
      {wΓ wΔ : ListLTerm} ->
      (wΓ ≡ union Γ1 Γ2) ->
      (wΔ ≡ union Δ1 Δ2) ->
      MGA-SR†* (head (wΓ , wΔ)) ->
      MGA-SR†* (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    Id-rule-head :
      (Γ Δ : ListLTerm) ->
      (A : LTerm) ->
      MGA-SR†* (head (Γ , Δ)) ->
      MGA-SR†* (head (Γ ∷ A , Δ ∷ A))
    U-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR†* (G ∣ (Γ ∷ (A , w) , Δ)) ->
      MGA-SR†* (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
    U-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (A , w))) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
    F-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR†* (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , Δ)) ->
      MGA-SR†* (G ∣ (Γ ∷ (A , w) , Δ))
    F-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (A , n1) ∷ (A , n2))) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (A , w)))
    U-L-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR†* (head (Γ ∷ (A , w) , Δ)) ->
      MGA-SR†* (head (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
    U-R-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR†* (head (Γ , Δ ∷ (A , w))) ->
      MGA-SR†* (head (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
    F-L-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR†* (head (Γ ∷ (A , n1) ∷ (A , n2) , Δ)) ->
      MGA-SR†* (head (Γ ∷ (A , w) , Δ))
    F-R-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR†* (head (Γ , Δ ∷ (A , n1) ∷ (A , n2))) ->
      MGA-SR†* (head (Γ , Δ ∷ (A , w)))
    E-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      MGA-SR†* (G ∣ (Γ , Δ)) ->
      MGA-SR†* (G ∣ (Γ ∷ (A , 0) , Δ))
    E-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      MGA-SR†* (G ∣ (Γ , Δ)) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (A , 0)))
    E-L-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      MGA-SR†* (head (Γ , Δ)) ->
      MGA-SR†* (head (Γ ∷ (A , 0) , Δ))
    E-R-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      MGA-SR†* (head (Γ , Δ)) ->
      MGA-SR†* (head (Γ , Δ ∷ (A , 0)))
    -- Logical Rules
    plus-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR†* (G ∣(Γ ∷ (A , n) ∷ (B , n) , Δ)) ->
      MGA-SR†* (G ∣ (Γ ∷ ((A +S B) , n), Δ))
    plus-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (A , n) ∷ (B , n))) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ ((A +S B) , n)))
    max-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR†* (G ∣(Γ ∷ (A , n) , Δ)) ->
      MGA-SR†* (G ∣(Γ ∷ (B , n) , Δ)) ->
      MGA-SR†* (G ∣(Γ ∷ ((A ⊔S B) , n) , Δ))
    max-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR†* (G ∣(Γ , Δ ∷ (A , n))∣(Γ , Δ ∷ (B , n))) ->
      MGA-SR†* (G ∣(Γ , Δ ∷ ((A ⊔S B) , n)))
    plus-L-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR†* (head (Γ ∷ (A , n) ∷ (B , n) , Δ)) ->
      MGA-SR†* (head (Γ ∷ ((A +S B) , n), Δ))
    plus-R-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR†* (head(Γ , Δ ∷ (A , n) ∷ (B , n))) ->
      MGA-SR†* (head(Γ , Δ ∷ ((A +S B) , n)))
    max-L-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR†* (head(Γ ∷ (A , n) , Δ)) ->
      MGA-SR†* (head(Γ ∷ (B , n) , Δ)) ->
      MGA-SR†* (head(Γ ∷ ((A ⊔S B) , n) , Δ))
    max-R-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR†* (head(Γ , Δ ∷ (A , n))∣(Γ , Δ ∷ (B , n))) ->
      MGA-SR†* (head(Γ , Δ ∷ ((A ⊔S B) , n)))
    Z-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (n : ℕ) ->
      MGA-SR†* (G ∣ (Γ , Δ)) ->
      MGA-SR†* (G ∣ (Γ ∷ (botAG , n) , Δ))
    Z-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (n : ℕ) ->
      MGA-SR†* (G ∣ (Γ , Δ)) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (botAG , n)))
    minus-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (A , n))) ->
      MGA-SR†* (G ∣ (Γ ∷ (-S A , n) , Δ))
    minus-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      MGA-SR†* (G ∣ (Γ ∷ (A , n) , Δ)) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (-S A , n)))
    min-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR†* (G ∣ (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ)) ->
      MGA-SR†* (G ∣ (Γ ∷ (A ⊓S B , n) , Δ))
    min-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (A , n))) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (B , n))) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (A ⊓S B , n)))
    Z-L-head :
      (Γ Δ : ListLTerm) ->
      (n : ℕ) ->
      MGA-SR†* (head (Γ , Δ)) ->
      MGA-SR†* (head (Γ ∷ (botAG , n) , Δ))
    Z-R-head :
      (Γ Δ : ListLTerm) ->
      (n : ℕ) ->
      MGA-SR†* (head (Γ , Δ)) ->
      MGA-SR†* (head (Γ , Δ ∷ (botAG , n)))
    minus-L-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      MGA-SR†* (head (Γ , Δ ∷ (A , n))) ->
      MGA-SR†* (head (Γ ∷ (-S A , n) , Δ))
    minus-R-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      MGA-SR†* (head (Γ ∷ (A , n) , Δ)) ->
      MGA-SR†* (head (Γ , Δ ∷ (-S A , n)))
    min-L-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR†* (head (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ)) ->
      MGA-SR†* (head (Γ ∷ (A ⊓S B , n) , Δ))
    min-R-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR†* (head (Γ , Δ ∷ (A , n))) ->
      MGA-SR†* (head (Γ , Δ ∷ (B , n))) ->
      MGA-SR†* (head (Γ , Δ ∷ (A ⊓S B , n)))
    ◆1-rule :
      (Γ Δ : ListLTerm) ->
      (◆Γ : ◆List Γ) ->
      (◆Δ : ◆List Δ) ->
      {wΓ wΔ : ListLTerm} ->
      (wΓ ≡ remove◆ ◆Γ) ->
      (wΔ ≡ remove◆ ◆Δ) ->
      (k : ℕ) ->
      MGA-SR†* (head (wΓ , (wΔ ∷ (one , suc k)))) ->
      MGA-SR†* (head (Γ , Δ ∷ (one , suc k)))
    ◆-rule :
      (Γ Δ : ListLTerm) ->
      (◆Γ : ◆List Γ) ->
      (◆Δ : ◆List Δ) ->
      {wΓ wΔ : ListLTerm} ->
      (wΓ ≡ remove◆ ◆Γ) ->
      (wΔ ≡ remove◆ ◆Δ) ->
      MGA-SR†* (head (wΓ , wΔ)) ->
      MGA-SR†* (head (Γ , Δ))
    1-rule :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (k : ℕ) ->
      MGA-SR†* (G ∣ (Γ , Δ)) ->
      MGA-SR†* (G ∣ (Γ , Δ ∷ (one , k)))
    1-rule-head :
      (Γ Δ : ListLTerm) ->
      (k : ℕ) ->
      MGA-SR†* (head (Γ , Δ)) ->
      MGA-SR†* (head (Γ , Δ ∷ (one , k)))
    -- Exchange rules
    seq-exchange :
      (G : LHSeq) ->
      (Γ Γ' Δ Δ' : ListLTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      MGA-SR†* (G ∣ (Γ , Δ)) ->
      MGA-SR†* (G ∣ (Γ' , Δ'))
    seq-exchange-head :
      (Γ Γ' Δ Δ' : ListLTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      MGA-SR†* (head (Γ , Δ)) ->
      MGA-SR†* (head (Γ' , Δ'))
    hseq-exchange :
      (G G' : LHSeq) ->
      LHSeqExchange G G' ->
      MGA-SR†* G ->
      MGA-SR†* G'

  #◆* :
    {G : LHSeq} ->
    MGA-SR†* G ->
    ℕ
  #◆* ax =
    0
  #◆* (W G Γ1 Γ2 Δ1 Δ2 p) =
    #◆* p
  #◆* (C G Γ Δ p) = 
    #◆* p
  #◆* (S G Γ1 Γ2 Δ1 Δ2 refl refl p) = 
    #◆* p
  #◆* (Id-rule G Γ Δ A p) = 
    #◆* p
  #◆* (W-head Γ1 Γ2 Δ1 Δ2 p) = 
    #◆* p
  #◆* (C-head Γ Δ p) = 
    #◆* p
  #◆* (S-head Γ1 Γ2 Δ1 Δ2 refl refl p) = 
    #◆* p
  #◆* (Id-rule-head Γ Δ A p) = 
    #◆* p
  #◆* (U-L G Γ Δ A n1 n2 refl p) = 
    #◆* p
  #◆* (U-R G Γ Δ A n1 n2 refl p) = 
    #◆* p
  #◆* (F-L G Γ Δ A n1 n2 refl p) = 
    #◆* p
  #◆* (F-R G Γ Δ A n1 n2 refl p) = 
    #◆* p
  #◆* (U-L-head Γ Δ A n1 n2 refl p) = 
    #◆* p
  #◆* (U-R-head Γ Δ A n1 n2 refl p) = 
    #◆* p
  #◆* (F-L-head Γ Δ A n1 n2 refl p) = 
    #◆* p
  #◆* (F-R-head Γ Δ A n1 n2 refl p) = 
    #◆* p
  #◆* (E-L G Γ Δ A p) = 
    #◆* p
  #◆* (E-R G Γ Δ A p) = 
    #◆* p
  #◆* (E-L-head Γ Δ A p) = 
    #◆* p
  #◆* (E-R-head Γ Δ A p) = 
    #◆* p
  #◆* (plus-L G Γ Δ A B n p) = 
    #◆* p
  #◆* (plus-R G Γ Δ A B n p) = 
    #◆* p
  #◆* (max-L G Γ Δ A B n p p₁) = 
    #◆* p + #◆* p₁
  #◆* (max-R G Γ Δ A B n p) = 
    #◆* p
  #◆* (plus-L-head Γ Δ A B n p) = 
    #◆* p
  #◆* (plus-R-head Γ Δ A B n p) = 
    #◆* p
  #◆* (max-L-head Γ Δ A B n p p₁) = 
    #◆* p + #◆* p₁
  #◆* (max-R-head Γ Δ A B n p) = 
    #◆* p
  #◆* (◆1-rule Γ Δ ◆Γ ◆Δ refl refl n p) = 
    suc (#◆* p)
  #◆* (◆-rule Γ Δ ◆Γ ◆Δ refl refl p) = 
    suc (#◆* p)
  #◆* (seq-exchange G Γ Γ' Δ Δ' x x₁ p) = 
    #◆* p
  #◆* (seq-exchange-head Γ Γ' Δ Δ' x x₁ p) = 
    #◆* p
  #◆* (hseq-exchange G G' x p) = 
    #◆* p
  #◆* (Z-L G Γ Δ n p) = 
    #◆* p
  #◆* (Z-R G Γ Δ n p) = 
    #◆* p
  #◆* (minus-L-head Γ Δ A n p) = 
    #◆* p
  #◆* (minus-R-head Γ Δ A n p) = 
    #◆* p
  #◆* (minus-L G Γ Δ A n p) = 
    #◆* p
  #◆* (minus-R G Γ Δ A n p) = 
    #◆* p
  #◆* (Z-L-head Γ Δ n p) = 
    #◆* p
  #◆* (Z-R-head Γ Δ n p) = 
    #◆* p
  #◆* (min-R-head Γ Δ A B n p p₁) = 
    #◆* p + #◆* p₁
  #◆* (min-L-head Γ Δ A B n p) = 
    #◆* p
  #◆* (min-R G Γ Δ A B n p p₁) = 
    #◆* p + #◆* p₁
  #◆* (min-L G Γ Δ A B n p) = 
    #◆* p
  #◆* (1-rule G Γ Δ k p) =
    #◆* p
  #◆* (1-rule-head Γ Δ k p) =
    #◆* p

--
--
-- With the can rule
--
--
  data MGA-SR† : LHSeq -> Set where
    -- Axiom
    ax :
      MGA-SR† (head ([] , []))
    -- Structural Rules
    W :
      (G : LHSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListLTerm) ->
      MGA-SR† (G ∣ (Γ1 , Δ1)) ->
      MGA-SR† (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      MGA-SR† (G ∣ (Γ , Δ) ∣ (Γ , Δ)) ->
      MGA-SR† (G ∣ (Γ , Δ))
    S :
      (G : LHSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListLTerm) ->
      {wΓ wΔ : ListLTerm} ->
      (wΓ ≡ union Γ1 Γ2) ->
      (wΔ ≡ union Δ1 Δ2) ->
      MGA-SR† (G ∣ (wΓ , wΔ)) ->
      MGA-SR† (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    Id-rule :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : LTerm) ->
      MGA-SR† (G ∣ (Γ , Δ)) ->
      MGA-SR† (G ∣ (Γ ∷ A , Δ ∷ A))
    W-head :
      (Γ1 Γ2 Δ1 Δ2 : ListLTerm) ->
      MGA-SR† (head (Γ1 , Δ1)) ->
      MGA-SR† (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C-head :
      (Γ Δ : ListLTerm) ->
      MGA-SR† (head (Γ , Δ) ∣ (Γ , Δ)) ->
      MGA-SR† (head (Γ , Δ))
    S-head :
      (Γ1 Γ2 Δ1 Δ2 : ListLTerm) ->
      {wΓ wΔ : ListLTerm} ->
      (wΓ ≡ union Γ1 Γ2) ->
      (wΔ ≡ union Δ1 Δ2) ->
      MGA-SR† (head (wΓ , wΔ)) ->
      MGA-SR† (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    Id-rule-head :
      (Γ Δ : ListLTerm) ->
      (A : LTerm) ->
      MGA-SR† (head (Γ , Δ)) ->
      MGA-SR† (head (Γ ∷ A , Δ ∷ A))
    U-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR† (G ∣ (Γ ∷ (A , w) , Δ)) ->
      MGA-SR† (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
    U-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (A , w))) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
    F-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR† (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , Δ)) ->
      MGA-SR† (G ∣ (Γ ∷ (A , w) , Δ))
    F-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (A , n1) ∷ (A , n2))) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (A , w)))
    U-L-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR† (head (Γ ∷ (A , w) , Δ)) ->
      MGA-SR† (head (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
    U-R-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR† (head (Γ , Δ ∷ (A , w))) ->
      MGA-SR† (head (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
    F-L-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR† (head (Γ ∷ (A , n1) ∷ (A , n2) , Δ)) ->
      MGA-SR† (head (Γ ∷ (A , w) , Δ))
    F-R-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      MGA-SR† (head (Γ , Δ ∷ (A , n1) ∷ (A , n2))) ->
      MGA-SR† (head (Γ , Δ ∷ (A , w)))
    E-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      MGA-SR† (G ∣ (Γ , Δ)) ->
      MGA-SR† (G ∣ (Γ ∷ (A , 0) , Δ))
    E-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      MGA-SR† (G ∣ (Γ , Δ)) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (A , 0)))
    E-L-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      MGA-SR† (head (Γ , Δ)) ->
      MGA-SR† (head (Γ ∷ (A , 0) , Δ))
    E-R-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      MGA-SR† (head (Γ , Δ)) ->
      MGA-SR† (head (Γ , Δ ∷ (A , 0)))
    -- Logical Rules
    plus-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR† (G ∣(Γ ∷ (A , n) ∷ (B , n) , Δ)) ->
      MGA-SR† (G ∣ (Γ ∷ ((A +S B) , n), Δ))
    plus-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (A , n) ∷ (B , n))) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ ((A +S B) , n)))
    max-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR† (G ∣(Γ ∷ (A , n) , Δ)) ->
      MGA-SR† (G ∣(Γ ∷ (B , n) , Δ)) ->
      MGA-SR† (G ∣(Γ ∷ ((A ⊔S B) , n) , Δ))
    max-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR† (G ∣(Γ , Δ ∷ (A , n))∣(Γ , Δ ∷ (B , n))) ->
      MGA-SR† (G ∣(Γ , Δ ∷ ((A ⊔S B) , n)))
    plus-L-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR† (head (Γ ∷ (A , n) ∷ (B , n) , Δ)) ->
      MGA-SR† (head (Γ ∷ ((A +S B) , n), Δ))
    plus-R-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR† (head(Γ , Δ ∷ (A , n) ∷ (B , n))) ->
      MGA-SR† (head(Γ , Δ ∷ ((A +S B) , n)))
    max-L-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR† (head(Γ ∷ (A , n) , Δ)) ->
      MGA-SR† (head(Γ ∷ (B , n) , Δ)) ->
      MGA-SR† (head(Γ ∷ ((A ⊔S B) , n) , Δ))
    max-R-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR† (head(Γ , Δ ∷ (A , n))∣(Γ , Δ ∷ (B , n))) ->
      MGA-SR† (head(Γ , Δ ∷ ((A ⊔S B) , n)))
    Z-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (n : ℕ) ->
      MGA-SR† (G ∣ (Γ , Δ)) ->
      MGA-SR† (G ∣ (Γ ∷ (botAG , n) , Δ))
    Z-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (n : ℕ) ->
      MGA-SR† (G ∣ (Γ , Δ)) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (botAG , n)))
    minus-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (A , n))) ->
      MGA-SR† (G ∣ (Γ ∷ (-S A , n) , Δ))
    minus-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      MGA-SR† (G ∣ (Γ ∷ (A , n) , Δ)) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (-S A , n)))
    min-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR† (G ∣ (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ)) ->
      MGA-SR† (G ∣ (Γ ∷ (A ⊓S B , n) , Δ))
    min-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (A , n))) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (B , n))) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (A ⊓S B , n)))
    Z-L-head :
      (Γ Δ : ListLTerm) ->
      (n : ℕ) ->
      MGA-SR† (head (Γ , Δ)) ->
      MGA-SR† (head (Γ ∷ (botAG , n) , Δ))
    Z-R-head :
      (Γ Δ : ListLTerm) ->
      (n : ℕ) ->
      MGA-SR† (head (Γ , Δ)) ->
      MGA-SR† (head (Γ , Δ ∷ (botAG , n)))
    minus-L-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      MGA-SR† (head (Γ , Δ ∷ (A , n))) ->
      MGA-SR† (head (Γ ∷ (-S A , n) , Δ))
    minus-R-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      MGA-SR† (head (Γ ∷ (A , n) , Δ)) ->
      MGA-SR† (head (Γ , Δ ∷ (-S A , n)))
    min-L-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR† (head (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ)) ->
      MGA-SR† (head (Γ ∷ (A ⊓S B , n) , Δ))
    min-R-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      MGA-SR† (head (Γ , Δ ∷ (A , n))) ->
      MGA-SR† (head (Γ , Δ ∷ (B , n))) ->
      MGA-SR† (head (Γ , Δ ∷ (A ⊓S B , n)))
    ◆1-rule :
      (Γ Δ : ListLTerm) ->
      (◆Γ : ◆List Γ) ->
      (◆Δ : ◆List Δ) ->
      {wΓ wΔ : ListLTerm} ->
      (wΓ ≡ remove◆ ◆Γ) ->
      (wΔ ≡ remove◆ ◆Δ) ->
      (k : ℕ) ->
      MGA-SR† (head (wΓ , (wΔ ∷ (one , suc k)))) ->
      MGA-SR† (head (Γ , Δ ∷ (one , suc k)))
    ◆-rule :
      (Γ Δ : ListLTerm) ->
      (◆Γ : ◆List Γ) ->
      (◆Δ : ◆List Δ) ->
      {wΓ wΔ : ListLTerm} ->
      (wΓ ≡ remove◆ ◆Γ) ->
      (wΔ ≡ remove◆ ◆Δ) ->
      MGA-SR† (head (wΓ , wΔ)) ->
      MGA-SR† (head (Γ , Δ))
    1-rule :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (k : ℕ) ->
      MGA-SR† (G ∣ (Γ , Δ)) ->
      MGA-SR† (G ∣ (Γ , Δ ∷ (one , k)))
    1-rule-head :
      (Γ Δ : ListLTerm) ->
      (k : ℕ) ->
      MGA-SR† (head (Γ , Δ)) ->
      MGA-SR† (head (Γ , Δ ∷ (one , k)))
    -- Exchange rules
    seq-exchange :
      (G : LHSeq) ->
      (Γ Γ' Δ Δ' : ListLTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      MGA-SR† (G ∣ (Γ , Δ)) ->
      MGA-SR† (G ∣ (Γ' , Δ'))
    seq-exchange-head :
      (Γ Γ' Δ Δ' : ListLTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      MGA-SR† (head (Γ , Δ)) ->
      MGA-SR† (head (Γ' , Δ'))
    hseq-exchange :
      (G G' : LHSeq) ->
      LHSeqExchange G G' ->
      MGA-SR† G ->
      MGA-SR† G'
    -- Can rule
    can-rule :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : LTerm) ->
      MGA-SR† (G ∣ (Γ ∷ A , Δ ∷ A)) ->
      MGA-SR† (G ∣ (Γ , Δ))
    can-rule-head :
      (Γ Δ : ListLTerm) ->
      (A : LTerm) ->
      MGA-SR† (head (Γ ∷ A , Δ ∷ A)) ->
      MGA-SR† (head (Γ , Δ))

  #◆ :
    {G : LHSeq} ->
    MGA-SR† G ->
    ℕ
  #◆ ax =
    0
  #◆ (W G Γ1 Γ2 Δ1 Δ2 p) =
    #◆ p
  #◆ (C G Γ Δ p) = 
    #◆ p
  #◆ (S G Γ1 Γ2 Δ1 Δ2 refl refl p) = 
    #◆ p
  #◆ (Id-rule G Γ Δ A p) = 
    #◆ p
  #◆ (W-head Γ1 Γ2 Δ1 Δ2 p) = 
    #◆ p
  #◆ (C-head Γ Δ p) = 
    #◆ p
  #◆ (S-head Γ1 Γ2 Δ1 Δ2 refl refl p) = 
    #◆ p
  #◆ (Id-rule-head Γ Δ A p) = 
    #◆ p
  #◆ (U-L G Γ Δ A n1 n2 refl p) = 
    #◆ p
  #◆ (U-R G Γ Δ A n1 n2 refl p) = 
    #◆ p
  #◆ (F-L G Γ Δ A n1 n2 refl p) = 
    #◆ p
  #◆ (F-R G Γ Δ A n1 n2 refl p) = 
    #◆ p
  #◆ (U-L-head Γ Δ A n1 n2 refl p) = 
    #◆ p
  #◆ (U-R-head Γ Δ A n1 n2 refl p) = 
    #◆ p
  #◆ (F-L-head Γ Δ A n1 n2 refl p) = 
    #◆ p
  #◆ (F-R-head Γ Δ A n1 n2 refl p) = 
    #◆ p
  #◆ (E-L G Γ Δ A p) = 
    #◆ p
  #◆ (E-R G Γ Δ A p) = 
    #◆ p
  #◆ (E-L-head Γ Δ A p) = 
    #◆ p
  #◆ (E-R-head Γ Δ A p) = 
    #◆ p
  #◆ (plus-L G Γ Δ A B n p) = 
    #◆ p
  #◆ (plus-R G Γ Δ A B n p) = 
    #◆ p
  #◆ (max-L G Γ Δ A B n p p₁) = 
    #◆ p + #◆ p₁
  #◆ (max-R G Γ Δ A B n p) = 
    #◆ p
  #◆ (plus-L-head Γ Δ A B n p) = 
    #◆ p
  #◆ (plus-R-head Γ Δ A B n p) = 
    #◆ p
  #◆ (max-L-head Γ Δ A B n p p₁) = 
    #◆ p + #◆ p₁
  #◆ (max-R-head Γ Δ A B n p) = 
    #◆ p
  #◆ (◆1-rule Γ Δ ◆Γ ◆Δ refl refl n p) = 
    suc (#◆ p)
  #◆ (◆-rule Γ Δ ◆Γ ◆Δ refl refl p) = 
    suc (#◆ p)
  #◆ (seq-exchange G Γ Γ' Δ Δ' x x₁ p) = 
    #◆ p
  #◆ (seq-exchange-head Γ Γ' Δ Δ' x x₁ p) = 
    #◆ p
  #◆ (hseq-exchange G G' x p) = 
    #◆ p
  #◆ (Z-L G Γ Δ n p) = 
    #◆ p
  #◆ (Z-R G Γ Δ n p) = 
    #◆ p
  #◆ (minus-L-head Γ Δ A n p) = 
    #◆ p
  #◆ (minus-R-head Γ Δ A n p) = 
    #◆ p
  #◆ (minus-L G Γ Δ A n p) = 
    #◆ p
  #◆ (minus-R G Γ Δ A n p) = 
    #◆ p
  #◆ (Z-L-head Γ Δ n p) = 
    #◆ p
  #◆ (Z-R-head Γ Δ n p) = 
    #◆ p
  #◆ (min-R-head Γ Δ A B n p p₁) = 
    #◆ p + #◆ p₁
  #◆ (min-L-head Γ Δ A B n p) = 
    #◆ p
  #◆ (min-R G Γ Δ A B n p p₁) = 
    #◆ p + #◆ p₁
  #◆ (min-L G Γ Δ A B n p) = 
    #◆ p
  #◆ (1-rule G Γ Δ k p) =
    #◆ p
  #◆ (1-rule-head Γ Δ k p) =
    #◆ p
  #◆ (can-rule G Γ Δ A p) =
    #◆ p
  #◆ (can-rule-head Γ Δ A p) =
    #◆ p
