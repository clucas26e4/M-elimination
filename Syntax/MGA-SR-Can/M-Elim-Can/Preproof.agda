module Syntax.MGA-SR-Can.M-Elim-Can.Preproof where
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
  open import Syntax.LHSeqList
  open import Syntax.ListLTerm.Properties
  open import Syntax.LHSeq.Properties

  {- Semantic -}

  data Preproof : LHSeq -> Set where
    -- Leaf
    leaf :
      (G : LHSeq) ->
      Preproof G
    -- Axiom
    ax :
      Preproof (head ([] , []))
    -- Structural Rules
    W :
      (G : LHSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListLTerm) ->
      Preproof (G ∣ (Γ1 , Δ1)) ->
      Preproof (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      Preproof (G ∣ (Γ , Δ) ∣ (Γ , Δ)) ->
      Preproof (G ∣ (Γ , Δ))
    S :
      (G : LHSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListLTerm) ->
      {wΓ wΔ : ListLTerm} ->
      (wΓ ≡ union Γ1 Γ2) ->
      (wΔ ≡ union Δ1 Δ2) ->
      Preproof (G ∣ (wΓ , wΔ)) ->
      Preproof (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    Id-rule :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : LTerm) ->
      Preproof (G ∣ (Γ , Δ)) ->
      Preproof (G ∣ (Γ ∷ A , Δ ∷ A))
    W-head :
      (Γ1 Γ2 Δ1 Δ2 : ListLTerm) ->
      Preproof (head (Γ1 , Δ1)) ->
      Preproof (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C-head :
      (Γ Δ : ListLTerm) ->
      Preproof (head (Γ , Δ) ∣ (Γ , Δ)) ->
      Preproof (head (Γ , Δ))
    S-head :
      (Γ1 Γ2 Δ1 Δ2 : ListLTerm) ->
      {wΓ wΔ : ListLTerm} ->
      (wΓ ≡ union Γ1 Γ2) ->
      (wΔ ≡ union Δ1 Δ2) ->
      Preproof (head (wΓ , wΔ)) ->
      Preproof (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    Id-rule-head :
      (Γ Δ : ListLTerm) ->
      (A : LTerm) ->
      Preproof (head (Γ , Δ)) ->
      Preproof (head (Γ ∷ A , Δ ∷ A))
    U-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      Preproof (G ∣ (Γ ∷ (A , w) , Δ)) ->
      Preproof (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
    U-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      Preproof (G ∣ (Γ , Δ ∷ (A , w))) ->
      Preproof (G ∣ (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
    F-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      Preproof (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , Δ)) ->
      Preproof (G ∣ (Γ ∷ (A , w) , Δ))
    F-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      Preproof (G ∣ (Γ , Δ ∷ (A , n1) ∷ (A , n2))) ->
      Preproof (G ∣ (Γ , Δ ∷ (A , w)))
    U-L-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      Preproof (head (Γ ∷ (A , w) , Δ)) ->
      Preproof (head (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
    U-R-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      Preproof (head (Γ , Δ ∷ (A , w))) ->
      Preproof (head (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
    F-L-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      Preproof (head (Γ ∷ (A , n1) ∷ (A , n2) , Δ)) ->
      Preproof (head (Γ ∷ (A , w) , Δ))
    F-R-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n1 n2 : ℕ) ->
      {w : ℕ} ->
      (w ≡ n1 + n2) ->
      Preproof (head (Γ , Δ ∷ (A , n1) ∷ (A , n2))) ->
      Preproof (head (Γ , Δ ∷ (A , w)))
    E-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      Preproof (G ∣ (Γ , Δ)) ->
      Preproof (G ∣ (Γ ∷ (A , 0) , Δ))
    E-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      Preproof (G ∣ (Γ , Δ)) ->
      Preproof (G ∣ (Γ , Δ ∷ (A , 0)))
    E-L-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      Preproof (head (Γ , Δ)) ->
      Preproof (head (Γ ∷ (A , 0) , Δ))
    E-R-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      Preproof (head (Γ , Δ)) ->
      Preproof (head (Γ , Δ ∷ (A , 0)))
    -- Logical Rules
    plus-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      Preproof (G ∣(Γ ∷ (A , n) ∷ (B , n) , Δ)) ->
      Preproof (G ∣ (Γ ∷ ((A +S B) , n), Δ))
    plus-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      Preproof (G ∣ (Γ , Δ ∷ (A , n) ∷ (B , n))) ->
      Preproof (G ∣ (Γ , Δ ∷ ((A +S B) , n)))
    max-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      Preproof (G ∣(Γ ∷ (A , n) , Δ)) ->
      Preproof (G ∣(Γ ∷ (B , n) , Δ)) ->
      Preproof (G ∣(Γ ∷ ((A ⊔S B) , n) , Δ))
    max-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      Preproof (G ∣(Γ , Δ ∷ (A , n))∣(Γ , Δ ∷ (B , n))) ->
      Preproof (G ∣(Γ , Δ ∷ ((A ⊔S B) , n)))
    plus-L-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      Preproof (head (Γ ∷ (A , n) ∷ (B , n) , Δ)) ->
      Preproof (head (Γ ∷ ((A +S B) , n), Δ))
    plus-R-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      Preproof (head(Γ , Δ ∷ (A , n) ∷ (B , n))) ->
      Preproof (head(Γ , Δ ∷ ((A +S B) , n)))
    max-L-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      Preproof (head(Γ ∷ (A , n) , Δ)) ->
      Preproof (head(Γ ∷ (B , n) , Δ)) ->
      Preproof (head(Γ ∷ ((A ⊔S B) , n) , Δ))
    max-R-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      Preproof (head(Γ , Δ ∷ (A , n))∣(Γ , Δ ∷ (B , n))) ->
      Preproof (head(Γ , Δ ∷ ((A ⊔S B) , n)))
    Z-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (n : ℕ) ->
      Preproof (G ∣ (Γ , Δ)) ->
      Preproof (G ∣ (Γ ∷ (botAG , n) , Δ))
    Z-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (n : ℕ) ->
      Preproof (G ∣ (Γ , Δ)) ->
      Preproof (G ∣ (Γ , Δ ∷ (botAG , n)))
    minus-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      Preproof (G ∣ (Γ , Δ ∷ (A , n))) ->
      Preproof (G ∣ (Γ ∷ (-S A , n) , Δ))
    minus-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      Preproof (G ∣ (Γ ∷ (A , n) , Δ)) ->
      Preproof (G ∣ (Γ , Δ ∷ (-S A , n)))
    min-L :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      Preproof (G ∣ (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ)) ->
      Preproof (G ∣ (Γ ∷ (A ⊓S B , n) , Δ))
    min-R :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      Preproof (G ∣ (Γ , Δ ∷ (A , n))) ->
      Preproof (G ∣ (Γ , Δ ∷ (B , n))) ->
      Preproof (G ∣ (Γ , Δ ∷ (A ⊓S B , n)))
    Z-L-head :
      (Γ Δ : ListLTerm) ->
      (n : ℕ) ->
      Preproof (head (Γ , Δ)) ->
      Preproof (head (Γ ∷ (botAG , n) , Δ))
    Z-R-head :
      (Γ Δ : ListLTerm) ->
      (n : ℕ) ->
      Preproof (head (Γ , Δ)) ->
      Preproof (head (Γ , Δ ∷ (botAG , n)))
    minus-L-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      Preproof (head (Γ , Δ ∷ (A , n))) ->
      Preproof (head (Γ ∷ (-S A , n) , Δ))
    minus-R-head :
      (Γ Δ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      Preproof (head (Γ ∷ (A , n) , Δ)) ->
      Preproof (head (Γ , Δ ∷ (-S A , n)))
    min-L-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      Preproof (head (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ)) ->
      Preproof (head (Γ ∷ (A ⊓S B , n) , Δ))
    min-R-head :
      (Γ Δ : ListLTerm) ->
      (A B : Term) ->
      (n : ℕ) ->
      Preproof (head (Γ , Δ ∷ (A , n))) ->
      Preproof (head (Γ , Δ ∷ (B , n))) ->
      Preproof (head (Γ , Δ ∷ (A ⊓S B , n)))
    ◆-rule :
      (Γ Δ : ListLTerm) ->
      (◆Γ : ◆List Γ) ->
      (◆Δ : ◆List Δ) ->
      {wΓ wΔ : ListLTerm} ->
      wΓ ≡ remove◆ ◆Γ ->
      wΔ ≡ remove◆ ◆Δ ->
      Preproof (head (wΓ , wΔ)) ->
      Preproof (head (Γ , Δ))
    ◆1-rule :
      (Γ Δ : ListLTerm) ->
      (◆Γ : ◆List Γ) ->
      (◆Δ : ◆List Δ) ->
      {wΓ wΔ : ListLTerm} ->
      wΓ ≡ remove◆ ◆Γ ->
      wΔ ≡ remove◆ ◆Δ ->
      (n : ℕ) ->
      Preproof (head (wΓ , wΔ ∷ (one , (suc n)))) ->
      Preproof (head (Γ , Δ ∷ (one , (suc n))))
    1-rule :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (k : ℕ) ->
      Preproof (G ∣ (Γ , Δ)) ->
      Preproof (G ∣ (Γ , Δ ∷ (one , k)))
    1-rule-head :
      (Γ Δ : ListLTerm) ->
      (k : ℕ) ->
      Preproof (head (Γ , Δ)) ->
      Preproof (head (Γ , Δ ∷ (one , k)))
    -- Exchange rules
    seq-exchange :
      (G : LHSeq) ->
      (Γ Γ' Δ Δ' : ListLTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      Preproof (G ∣ (Γ , Δ)) ->
      Preproof (G ∣ (Γ' , Δ'))
    seq-exchange-head :
      (Γ Γ' Δ Δ' : ListLTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      Preproof (head (Γ , Δ)) ->
      Preproof (head (Γ' , Δ'))
    hseq-exchange :
      (G G' : LHSeq) ->
      LHSeqExchange G G' ->
      Preproof G ->
      Preproof G'
    -- can rule
    can-rule :
      (G : LHSeq) ->
      (Γ Δ : ListLTerm) ->
      (A : LTerm) ->
      Preproof (G ∣ (Γ ∷ A , Δ ∷ A)) ->
      Preproof (G ∣ (Γ , Δ))
    can-rule-head :
      (Γ Δ : ListLTerm) ->
      (A : LTerm) ->
      Preproof (head (Γ ∷ A , Δ ∷ A)) ->
      Preproof (head (Γ , Δ))

  PreproofCong :
    {G G' : LHSeq} ->
    Preproof G ->
    G ≡ G' ->
    Preproof G'
  PreproofCong PG refl = PG    
    
  ΔGen :
    (G : LHSeq) ->
    Preproof (G ∣ ([] , []))
  ΔGen (head (T , D)) =
    hseq-exchange
      (head ([] , []) ∣ (T , D))
      (head (T , D) ∣ ([] , []))
      exHE-head
      (W-head
        []
        T
        []
        D
        ax)
  ΔGen (G ∣ (T , D)) =
    hseq-exchange
      (G ∣ ([] , []) ∣ (T , D))
      (G ∣ (T , D) ∣ ([] , []))
      (exHE
        idHE)
      (W
        G
        []
        T
        []
        D
        (ΔGen G))

  UnfoldPreproofCopy-LGen :
    (G : LHSeq) ->
    (T T' D : ListLTerm) ->
    (n : ℕ) ->
    Preproof (G ∣ (union (copy T (suc n)) T' , D)) ->
    Preproof (G ∣ (union (union (copy T n) T) T' , D))
  UnfoldPreproofCopy-LGen G [] T' D zero p =
    p
  UnfoldPreproofCopy-LGen G [] T' D (suc n) p =
    p
  UnfoldPreproofCopy-LGen G (T ∷ (A , n1)) T' D zero p =
    PreproofCong
      p
      (cong₂
        (λ x y -> G ∣ (union (x ∷ (A , y)) T' , D))
        (begin
          copy T 1
            ≡⟨ idCopy T ⟩
          T
            ≡⟨ sym (union[]T=T T) ⟩
          union [] T ∎)
        (sym a=a+0))
  UnfoldPreproofCopy-LGen G (T ∷ (A , n1)) T' D (suc n) p =
    seq-exchange
      G
      (union T' (union (copy T (suc n) ∷ (A , n1 + n * n1)) T) ∷ (A , n1))
      (union (union (copy T (suc n) ∷ (A , n1 + n * n1)) T ∷ (A , n1)) T')
      D
      D
      (ListExchangeUnion
        T'
        (union (copy T (suc n) ∷ (A , n1 + n * n1)) T ∷ (A , n1)))
      idLE
      (seq-exchange
        G
        (union T' (union (copy T (suc n)) T) ∷ (A , n1 + n * n1) ∷ (A , n1))
        (union T' (union (copy T (suc n) ∷ (A , n1 + n * n1)) T ∷ (A , n1)))
        D
        D
        (unionKeepExchangeRight T'
          (indLE
            (ListExchangeSym
              (exchangeUnionLast (copy T (suc n)) T (A , n1 + n * n1)))))
        idLE
        (U-L
          G
          (union T' (union (copy T (suc n)) T))
          D
          A
          (n1 + n * n1)
          n1
          refl
          (seq-exchange
            G
            (union (union (copy T (suc n)) T) (T' ∷ (A , n1 + n * n1 + n1)))
            (union T' (union (copy T (suc n)) T) ∷ (A , n1 + n * n1 + n1))
            D
            D
            (indLE
              (ListExchangeUnion
                (union (copy T (suc n)) T)
                T'))
            idLE
            (UnfoldPreproofCopy-LGen
              G
              T
              (T' ∷ (A , n1 + n * n1 + n1))
              D
              (suc n)
              (seq-exchange
                G
                (union (copy T (suc (suc n)) ∷ (A , n1 + n * n1 + n1)) T')
                (union (copy T (suc (suc n))) T' ∷ (A , n1 + n * n1 + n1))
                D
                D
                (exchangeUnionLast
                  (copy T (suc (suc n)))
                  T'
                  (A , n1 + n * n1 + n1))
                idLE
                (PreproofCong
                  p
                  (cong
                    (λ x -> G ∣ (union (copy T (suc (suc n)) ∷ (A , x)) T' , D))
                    (begin
                      n1 + (n1 + n * n1)
                        ≡⟨ cong
                             (λ x -> n1 + x)
                             (+-comm n1 (n * n1)) ⟩
                      n1 + (n * n1 + n1)
                        ≡⟨ sym (+-assoc n1 (n * n1) n1) ⟩
                      n1 + n * n1 + n1 ∎))))))))

  UnfoldPreproofCopy-L :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    (n : ℕ) ->
    Preproof (G ∣ (copy T (suc n) , D)) ->
    Preproof (G ∣ (union (copy T n) T , D))
  UnfoldPreproofCopy-L G T D n = UnfoldPreproofCopy-LGen G T [] D n



  UnfoldPreproofCopy-RGen :
    (G : LHSeq) ->
    (T D D' : ListLTerm) ->
    (n : ℕ) ->
    Preproof (G ∣ (T , union (copy D (suc n)) D')) ->
    Preproof (G ∣ (T , union (union (copy D n) D) D'))
  UnfoldPreproofCopy-RGen G T [] D' zero p =
    p
  UnfoldPreproofCopy-RGen G T [] D' (suc n) p =
    p
  UnfoldPreproofCopy-RGen G T (D ∷ (A , n1)) D' zero p =
    PreproofCong
      p
      (cong₂
        (λ x y -> G ∣ (T , (union (x ∷ (A , y)) D')))
        (begin
          copy D 1
            ≡⟨ idCopy D ⟩
          D
            ≡⟨ sym (union[]T=T D) ⟩
          union [] D ∎)
        (sym a=a+0))
  UnfoldPreproofCopy-RGen G T (D ∷ (A , n1)) D' (suc n) p =
    seq-exchange
      G
      T
      T
      (union D' (union (copy D (suc n) ∷ (A , n1 + n * n1)) D) ∷ (A , n1))
      (union (union (copy D (suc n) ∷ (A , n1 + n * n1)) D ∷ (A , n1)) D')
      idLE
      (ListExchangeUnion
        D'
        (union (copy D (suc n) ∷ (A , n1 + n * n1)) D ∷ (A , n1)))
      (seq-exchange
        G
        T
        T
        (union D' (union (copy D (suc n)) D) ∷ (A , n1 + n * n1) ∷ (A , n1))
        (union D' (union (copy D (suc n) ∷ (A , n1 + n * n1)) D ∷ (A , n1)))
        idLE
        (unionKeepExchangeRight D'
          (indLE
            (ListExchangeSym
              (exchangeUnionLast (copy D (suc n)) D (A , n1 + n * n1)))))
        (U-R
          G
          T
          (union D' (union (copy D (suc n)) D))
          A
          (n1 + n * n1)
          n1
          refl
          (seq-exchange
            G
            T
            T
            (union (union (copy D (suc n)) D) (D' ∷ (A , n1 + n * n1 + n1)))
            (union D' (union (copy D (suc n)) D) ∷ (A , n1 + n * n1 + n1))
            idLE
            (indLE
              (ListExchangeUnion
                (union (copy D (suc n)) D)
                D'))
            (UnfoldPreproofCopy-RGen
              G
              T
              D
              (D' ∷ (A , n1 + n * n1 + n1))
              (suc n)
              (seq-exchange
                G
                T
                T
                (union (copy D (suc (suc n)) ∷ (A , n1 + n * n1 + n1)) D')
                (union (copy D (suc (suc n))) D' ∷ (A , n1 + n * n1 + n1))
                idLE
                (exchangeUnionLast
                  (copy D (suc (suc n)))
                  D'
                  (A , n1 + n * n1 + n1))
                (PreproofCong
                  p
                  (cong
                    (λ x -> G ∣ (T , union (copy D (suc (suc n)) ∷ (A , x)) D'))
                    (begin
                      n1 + (n1 + n * n1)
                        ≡⟨ cong
                             (λ x -> n1 + x)
                             (+-comm n1 (n * n1)) ⟩
                      n1 + (n * n1 + n1)
                        ≡⟨ sym (+-assoc n1 (n * n1) n1) ⟩
                      n1 + n * n1 + n1 ∎))))))))



  UnfoldPreproofCopy-R :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    (n : ℕ) ->
    Preproof (G ∣ (T , copy D (suc n))) ->
    Preproof (G ∣ (T , union (copy D n) D))
  UnfoldPreproofCopy-R G T D n = UnfoldPreproofCopy-RGen G T D [] n

  UnfoldPreproofCopy-L-head-Gen :
    (T T' D : ListLTerm) ->
    (n : ℕ) ->
    Preproof (head (union (copy T (suc n)) T' , D)) ->
    Preproof (head (union (union (copy T n) T) T' , D))
  UnfoldPreproofCopy-L-head-Gen [] T' D zero p =
    p
  UnfoldPreproofCopy-L-head-Gen [] T' D (suc n) p =
    p
  UnfoldPreproofCopy-L-head-Gen (T ∷ (A , n1)) T' D zero p =
    PreproofCong
      p
      (cong₂
        (λ x y -> head (union (x ∷ (A , y)) T' , D))
        (begin
          copy T 1
            ≡⟨ idCopy T ⟩
          T
            ≡⟨ sym (union[]T=T T) ⟩
          union [] T ∎)
        (sym a=a+0))
  UnfoldPreproofCopy-L-head-Gen (T ∷ (A , n1)) T' D (suc n) p =
    seq-exchange-head
      (union T' (union (copy T (suc n) ∷ (A , n1 + n * n1)) T) ∷ (A , n1))
      (union (union (copy T (suc n) ∷ (A , n1 + n * n1)) T ∷ (A , n1)) T')
      D
      D
      (ListExchangeUnion
        T'
        (union (copy T (suc n) ∷ (A , n1 + n * n1)) T ∷ (A , n1)))
      idLE
      (seq-exchange-head
        (union T' (union (copy T (suc n)) T) ∷ (A , n1 + n * n1) ∷ (A , n1))
        (union T' (union (copy T (suc n) ∷ (A , n1 + n * n1)) T ∷ (A , n1)))
        D
        D
        (unionKeepExchangeRight T'
          (indLE
            (ListExchangeSym
              (exchangeUnionLast (copy T (suc n)) T (A , n1 + n * n1)))))
        idLE
        (U-L-head
          (union T' (union (copy T (suc n)) T))
          D
          A
          (n1 + n * n1)
          n1
          refl
          (seq-exchange-head
            (union (union (copy T (suc n)) T) (T' ∷ (A , n1 + n * n1 + n1)))
            (union T' (union (copy T (suc n)) T) ∷ (A , n1 + n * n1 + n1))
            D
            D
            (indLE
              (ListExchangeUnion
                (union (copy T (suc n)) T)
                T'))
            idLE
            (UnfoldPreproofCopy-L-head-Gen
              T
              (T' ∷ (A , n1 + n * n1 + n1))
              D
              (suc n)
              (seq-exchange-head
                (union (copy T (suc (suc n)) ∷ (A , n1 + n * n1 + n1)) T')
                (union (copy T (suc (suc n))) T' ∷ (A , n1 + n * n1 + n1))
                D
                D
                (exchangeUnionLast
                  (copy T (suc (suc n)))
                  T'
                  (A , n1 + n * n1 + n1))
                idLE
                (PreproofCong
                  p
                  (cong
                    (λ x -> head (union (copy T (suc (suc n)) ∷ (A , x)) T' , D))
                    (begin
                      n1 + (n1 + n * n1)
                        ≡⟨ cong
                             (λ x -> n1 + x)
                             (+-comm n1 (n * n1)) ⟩
                      n1 + (n * n1 + n1)
                        ≡⟨ sym (+-assoc n1 (n * n1) n1) ⟩
                      n1 + n * n1 + n1 ∎))))))))

  UnfoldPreproofCopy-L-head :
    (T D : ListLTerm) ->
    (n : ℕ) ->
    Preproof (head (copy T (suc n) , D)) ->
    Preproof (head (union (copy T n) T , D))
  UnfoldPreproofCopy-L-head T D n = UnfoldPreproofCopy-L-head-Gen T [] D n



  UnfoldPreproofCopy-R-head-Gen :
    (T D D' : ListLTerm) ->
    (n : ℕ) ->
    Preproof (head (T , union (copy D (suc n)) D')) ->
    Preproof (head (T , union (union (copy D n) D) D'))
  UnfoldPreproofCopy-R-head-Gen T [] D' zero p =
    p
  UnfoldPreproofCopy-R-head-Gen T [] D' (suc n) p =
    p
  UnfoldPreproofCopy-R-head-Gen T (D ∷ (A , n1)) D' zero p =
    PreproofCong
      p
      (cong₂
        (λ x y -> head (T , (union (x ∷ (A , y)) D')))
        (begin
          copy D 1
            ≡⟨ idCopy D ⟩
          D
            ≡⟨ sym (union[]T=T D) ⟩
          union [] D ∎)
        (sym a=a+0))
  UnfoldPreproofCopy-R-head-Gen T (D ∷ (A , n1)) D' (suc n) p =
    seq-exchange-head
      T
      T
      (union D' (union (copy D (suc n) ∷ (A , n1 + n * n1)) D) ∷ (A , n1))
      (union (union (copy D (suc n) ∷ (A , n1 + n * n1)) D ∷ (A , n1)) D')
      idLE
      (ListExchangeUnion
        D'
        (union (copy D (suc n) ∷ (A , n1 + n * n1)) D ∷ (A , n1)))
      (seq-exchange-head
        T
        T
        (union D' (union (copy D (suc n)) D) ∷ (A , n1 + n * n1) ∷ (A , n1))
        (union D' (union (copy D (suc n) ∷ (A , n1 + n * n1)) D ∷ (A , n1)))
        idLE
        (unionKeepExchangeRight D'
          (indLE
            (ListExchangeSym
              (exchangeUnionLast (copy D (suc n)) D (A , n1 + n * n1)))))
        (U-R-head
          T
          (union D' (union (copy D (suc n)) D))
          A
          (n1 + n * n1)
          n1
          refl
          (seq-exchange-head
            T
            T
            (union (union (copy D (suc n)) D) (D' ∷ (A , n1 + n * n1 + n1)))
            (union D' (union (copy D (suc n)) D) ∷ (A , n1 + n * n1 + n1))
            idLE
            (indLE
              (ListExchangeUnion
                (union (copy D (suc n)) D)
                D'))
            (UnfoldPreproofCopy-R-head-Gen
              T
              D
              (D' ∷ (A , n1 + n * n1 + n1))
              (suc n)
              (seq-exchange-head
                T
                T
                (union (copy D (suc (suc n)) ∷ (A , n1 + n * n1 + n1)) D')
                (union (copy D (suc (suc n))) D' ∷ (A , n1 + n * n1 + n1))
                idLE
                (exchangeUnionLast
                  (copy D (suc (suc n)))
                  D'
                  (A , n1 + n * n1 + n1))
                (PreproofCong
                  p
                  (cong
                    (λ x -> head (T , union (copy D (suc (suc n)) ∷ (A , x)) D'))
                    (begin
                      n1 + (n1 + n * n1)
                        ≡⟨ cong
                             (λ x -> n1 + x)
                             (+-comm n1 (n * n1)) ⟩
                      n1 + (n * n1 + n1)
                        ≡⟨ sym (+-assoc n1 (n * n1) n1) ⟩
                      n1 + n * n1 + n1 ∎))))))))



  UnfoldPreproofCopy-R-head :
    (T D : ListLTerm) ->
    (n : ℕ) ->
    Preproof (head (T , copy D (suc n))) ->
    Preproof (head (T , union (copy D n) D))
  UnfoldPreproofCopy-R-head T D n = UnfoldPreproofCopy-R-head-Gen T D [] n

  leaves :
    {G : LHSeq} ->
    Preproof G ->
    LHSeqList
  leaves (leaf G) =
    G ∷H []H
  leaves ax = 
    []H
  leaves (W G Γ1 Γ2 Δ1 Δ2 p) =
    leaves p
  leaves (C G Γ Δ p) =
    leaves p
  leaves (S G Γ1 Γ2 Δ1 Δ2 refl refl p) =
    leaves p
  leaves (Id-rule G Γ Δ A p) =
    leaves p
  leaves (W-head Γ1 Γ2 Δ1 Δ2 p) = 
    leaves p
  leaves (C-head Γ Δ p) = 
    leaves p
  leaves (S-head Γ1 Γ2 Δ1 Δ2 refl refl p) =
    leaves p
  leaves (Id-rule-head Γ Δ A p) =
    leaves p
  leaves (U-L G Γ Δ A n1 n2 refl p) =
    leaves p
  leaves (U-R G Γ Δ A n1 n2 refl p) =
    leaves p
  leaves (F-L G Γ Δ A n1 n2 refl p) =
    leaves p
  leaves (F-R G Γ Δ A n1 n2 refl p) =
    leaves p
  leaves (U-L-head Γ Δ A n1 n2 refl p) =
    leaves p
  leaves (U-R-head Γ Δ A n1 n2 refl p) =
    leaves p
  leaves (F-L-head Γ Δ A n1 n2 refl p) =
    leaves p
  leaves (F-R-head Γ Δ A n1 n2 refl p) =
    leaves p
  leaves (E-L G Γ Δ A p) =
    leaves p
  leaves (E-R G Γ Δ A p) =
    leaves p
  leaves (E-L-head Γ Δ A p) =
    leaves p
  leaves (E-R-head Γ Δ A p) =
    leaves p
  leaves (plus-L G Γ Δ A B n p) =
    leaves p
  leaves (plus-R G Γ Δ A B n p) =
    leaves p
  leaves (max-L G Γ Δ A B n p p₁) =
    unionHL (leaves p) (leaves p₁)
  leaves (max-R G Γ Δ A B n p) =
    leaves p
  leaves (plus-L-head Γ Δ A B n p) =
    leaves p
  leaves (plus-R-head Γ Δ A B n p) =
    leaves p
  leaves (max-L-head Γ Δ A B n p p₁) =
    unionHL (leaves p) (leaves p₁)
  leaves (max-R-head Γ Δ A B n p) =
    leaves p
  leaves (Z-L G Γ Δ n p) =
    leaves p
  leaves (Z-R G Γ Δ n p) =
    leaves p
  leaves (Z-L-head Γ Δ n p) =
    leaves p
  leaves (Z-R-head Γ Δ n p) =
    leaves p
  leaves (minus-L G Γ Δ A n p) =
    leaves p
  leaves (minus-R G Γ Δ A n p) =
    leaves p
  leaves (minus-L-head Γ Δ A n p) =
    leaves p
  leaves (minus-R-head Γ Δ A n p) =
    leaves p
  leaves (min-R-head Γ Δ A B n p p₁) =
    unionHL (leaves p) (leaves p₁)
  leaves (min-L-head Γ Δ A B n p) =
    leaves p
  leaves (min-R G Γ Δ A B n p p₁) =
    unionHL (leaves p) (leaves p₁)
  leaves (min-L G Γ Δ A B n p) =
    leaves p
  leaves (◆1-rule Γ Δ ◆Γ ◆Δ refl refl n p) =
    leaves p
  leaves (◆-rule Γ Δ ◆Γ ◆Δ refl refl p) =
    leaves p
  leaves (1-rule G Γ Δ n p) =
    leaves p
  leaves (1-rule-head Γ Δ n p) =
    leaves p
  leaves (seq-exchange G Γ Γ' Δ Δ' x x₁ p) =
    leaves p
  leaves (seq-exchange-head Γ Γ' Δ Δ' x x₁ p) =
    leaves p
  leaves (hseq-exchange G G' x p) =
    leaves p
  leaves (can-rule G Γ Δ A p) =
    leaves p
  leaves (can-rule-head Γ Δ A p) =
    leaves p

  unionCopy-L :
    (G : LHSeq) ->
    (T T' D : ListLTerm) ->
    (n n' : ℕ) ->
    Preproof (G ∣ (union T (copy T' (n + n')) , D)) ->
    Preproof (G ∣ (union T (union (copy T' n) (copy T' n')) , D))
  unionCopy-L G T T' D zero zero p = 
    p
  unionCopy-L G T T' D (suc n) zero p =
    PreproofCong
      p
      (cong
        (λ x -> G ∣ (union T (copy T' (suc x)) , D))
        (sym a=a+0))
  unionCopy-L G T T' D zero (suc n') p =
    PreproofCong
      p
      (cong
        (λ x -> G ∣ (union T x , D))
        (sym
          (union[]T=T (copy T' (suc n')))))
  unionCopy-L G T [] D (suc n) (suc n') p =
    p
  unionCopy-L G T (T' ∷ (A , nA)) D (suc n) (suc n') p =
    seq-exchange
      G
      ((union T (union (copy T' (suc n)) (copy T' (suc n')))) ∷ (A , nA + n * nA) ∷ (A , nA + n' * nA))
      (union T (union (copy T' (suc n) ∷ (A , nA + n * nA)) (copy T' (suc n'))) ∷ (A , nA + n' * nA))
      D
      D
      (unionKeepExchangeRight
        T
        (indLE
          (ListExchangeSym
            (exchangeUnionLast
              (copy T' (suc n))
              (copy T' (suc n'))
              (A , nA + n * nA)))))
      idLE
      (U-L
        G
        (union T (union (copy T' (suc n)) (copy T' (suc n'))))
        D
        A
        ((suc n) * nA)
        ((suc n') * nA)
        refl
        (seq-exchange
          G
          (union (T ∷ (A , nA + n * nA + (nA + n' * nA))) (union (copy T' (suc n)) (copy T' (suc n'))))
          (union T (union (copy T' (suc n)) (copy T' (suc n'))) ∷ (A , nA + n * nA + (nA + n' * nA)))
          D
          D
          (exchangeUnionLast
            T
            (union (copy T' (suc n)) (copy T' (suc n')))
            (A , nA + n * nA + (nA + n' * nA)))
          idLE
          (unionCopy-L
            G
            (T ∷ (A , nA + n * nA + (nA + n' * nA)))
            T'
            D
            (suc n)
            (suc n')
            (seq-exchange
              G
              (union T (copy T' (suc (n + (suc n')))) ∷ (A , nA + n * nA + (nA + n' * nA)))
              (union (T ∷ (A , nA + n * nA + (nA + n' * nA))) (copy T' (suc n + (suc n'))))
              D
              D
              (ListExchangeSym
                (exchangeUnionLast
                  T
                  (copy T' (suc n + (suc n')))
                  (A , nA + n * nA + (nA + n' * nA))))
              idLE
              (PreproofCong
                p
                (cong
                  (λ x -> G ∣ ((union T (copy T' (suc (n + suc n')))) ∷ (A , x) , D))
                  (a+b*c=a*c+b*c (suc n) (suc n') nA)))))))

  unionCopy-R :
    (G : LHSeq) ->
    (T D D' : ListLTerm) ->
    (n n' : ℕ) ->
    Preproof (G ∣ (T , union D (copy D' (n + n')))) ->
    Preproof (G ∣ (T , union D (union (copy D' n) (copy D' n'))))
  unionCopy-R G T D D' zero zero p = 
    p
  unionCopy-R G T D D' (suc n) zero p =
    PreproofCong
      p
      (cong
        (λ x -> G ∣ (T , union D (copy D' (suc x))))
        (sym a=a+0))
  unionCopy-R G T D D' zero (suc n') p =
    PreproofCong
      p
      (cong
        (λ x -> G ∣ (T , union D x))
        (sym
          (union[]T=T (copy D' (suc n')))))
  unionCopy-R G T D [] (suc n) (suc n') p =
    p
  unionCopy-R G T D (D' ∷ (A , nA)) (suc n) (suc n') p =
    seq-exchange
      G
      T
      T
      ((union D (union (copy D' (suc n)) (copy D' (suc n')))) ∷ (A , nA + n * nA) ∷ (A , nA + n' * nA))
      (union D (union (copy D' (suc n) ∷ (A , nA + n * nA)) (copy D' (suc n'))) ∷ (A , nA + n' * nA))
      idLE
      (unionKeepExchangeRight
        D
        (indLE
          (ListExchangeSym
            (exchangeUnionLast
              (copy D' (suc n))
              (copy D' (suc n'))
              (A , nA + n * nA)))))
      (U-R
        G
        T
        (union D (union (copy D' (suc n)) (copy D' (suc n'))))
        A
        ((suc n) * nA)
        ((suc n') * nA)
        refl
        (seq-exchange
          G
          T
          T
          (union (D ∷ (A , nA + n * nA + (nA + n' * nA))) (union (copy D' (suc n)) (copy D' (suc n'))))
          (union D (union (copy D' (suc n)) (copy D' (suc n'))) ∷ (A , nA + n * nA + (nA + n' * nA)))
          idLE
          (exchangeUnionLast
            D
            (union (copy D' (suc n)) (copy D' (suc n')))
            (A , nA + n * nA + (nA + n' * nA)))
          (unionCopy-R
            G
            T
            (D ∷ (A , nA + n * nA + (nA + n' * nA)))
            D'
            (suc n)
            (suc n')
            (seq-exchange
              G
              T
              T
              (union D (copy D' (suc (n + (suc n')))) ∷ (A , nA + n * nA + (nA + n' * nA)))
              (union (D ∷ (A , nA + n * nA + (nA + n' * nA))) (copy D' (suc n + (suc n'))))
              idLE
              (ListExchangeSym
                (exchangeUnionLast
                  D
                  (copy D' (suc n + (suc n')))
                  (A , nA + n * nA + (nA + n' * nA))))
              (PreproofCong
                p
                (cong
                  (λ x -> G ∣ (T , (union D (copy D' (suc (n + suc n')))) ∷ (A , x)))
                  (a+b*c=a*c+b*c (suc n) (suc n') nA)))))))

  unionCopy-L-head :
    (T T' D : ListLTerm) ->
    (n n' : ℕ) ->
    Preproof (head (union T (copy T' (n + n')) , D)) ->
    Preproof (head (union T (union (copy T' n) (copy T' n')) , D))
  unionCopy-L-head T T' D zero zero p = 
    p
  unionCopy-L-head T T' D (suc n) zero p =
    PreproofCong
      p
      (cong
        (λ x -> head (union T (copy T' (suc x)) , D))
        (sym a=a+0))
  unionCopy-L-head T T' D zero (suc n') p =
    PreproofCong
      p
      (cong
        (λ x -> head (union T x , D))
        (sym
          (union[]T=T (copy T' (suc n')))))
  unionCopy-L-head T [] D (suc n) (suc n') p =
    p
  unionCopy-L-head T (T' ∷ (A , nA)) D (suc n) (suc n') p =
    seq-exchange-head
      ((union T (union (copy T' (suc n)) (copy T' (suc n')))) ∷ (A , nA + n * nA) ∷ (A , nA + n' * nA))
      (union T (union (copy T' (suc n) ∷ (A , nA + n * nA)) (copy T' (suc n'))) ∷ (A , nA + n' * nA))
      D
      D
      (unionKeepExchangeRight
        T
        (indLE
          (ListExchangeSym
            (exchangeUnionLast
              (copy T' (suc n))
              (copy T' (suc n'))
              (A , nA + n * nA)))))
      idLE
      (U-L-head
        (union T (union (copy T' (suc n)) (copy T' (suc n'))))
        D
        A
        ((suc n) * nA)
        ((suc n') * nA)
        refl
        (seq-exchange-head
          (union (T ∷ (A , nA + n * nA + (nA + n' * nA))) (union (copy T' (suc n)) (copy T' (suc n'))))
          (union T (union (copy T' (suc n)) (copy T' (suc n'))) ∷ (A , nA + n * nA + (nA + n' * nA)))
          D
          D
          (exchangeUnionLast
            T
            (union (copy T' (suc n)) (copy T' (suc n')))
            (A , nA + n * nA + (nA + n' * nA)))
          idLE
          (unionCopy-L-head
            (T ∷ (A , nA + n * nA + (nA + n' * nA)))
            T'
            D
            (suc n)
            (suc n')
            (seq-exchange-head
              (union T (copy T' (suc (n + (suc n')))) ∷ (A , nA + n * nA + (nA + n' * nA)))
              (union (T ∷ (A , nA + n * nA + (nA + n' * nA))) (copy T' (suc n + (suc n'))))
              D
              D
              (ListExchangeSym
                (exchangeUnionLast
                  T
                  (copy T' (suc n + (suc n')))
                  (A , nA + n * nA + (nA + n' * nA))))
              idLE
              (PreproofCong
                p
                (cong
                  (λ x -> head ((union T (copy T' (suc (n + suc n')))) ∷ (A , x) , D))
                  (a+b*c=a*c+b*c (suc n) (suc n') nA)))))))

  unionCopy-R-head :
    (T D D' : ListLTerm) ->
    (n n' : ℕ) ->
    Preproof (head (T , union D (copy D' (n + n')))) ->
    Preproof (head (T , union D (union (copy D' n) (copy D' n'))))
  unionCopy-R-head T D D' zero zero p = 
    p
  unionCopy-R-head T D D' (suc n) zero p =
    PreproofCong
      p
      (cong
        (λ x -> head (T , union D (copy D' (suc x))))
        (sym a=a+0))
  unionCopy-R-head T D D' zero (suc n') p =
    PreproofCong
      p
      (cong
        (λ x -> head (T , union D x))
        (sym
          (union[]T=T (copy D' (suc n')))))
  unionCopy-R-head T D [] (suc n) (suc n') p =
    p
  unionCopy-R-head T D (D' ∷ (A , nA)) (suc n) (suc n') p =
    seq-exchange-head
      T
      T
      ((union D (union (copy D' (suc n)) (copy D' (suc n')))) ∷ (A , nA + n * nA) ∷ (A , nA + n' * nA))
      (union D (union (copy D' (suc n) ∷ (A , nA + n * nA)) (copy D' (suc n'))) ∷ (A , nA + n' * nA))
      idLE
      (unionKeepExchangeRight
        D
        (indLE
          (ListExchangeSym
            (exchangeUnionLast
              (copy D' (suc n))
              (copy D' (suc n'))
              (A , nA + n * nA)))))
      (U-R-head
        T
        (union D (union (copy D' (suc n)) (copy D' (suc n'))))
        A
        ((suc n) * nA)
        ((suc n') * nA)
        refl
        (seq-exchange-head
          T
          T
          (union (D ∷ (A , nA + n * nA + (nA + n' * nA))) (union (copy D' (suc n)) (copy D' (suc n'))))
          (union D (union (copy D' (suc n)) (copy D' (suc n'))) ∷ (A , nA + n * nA + (nA + n' * nA)))
          idLE
          (exchangeUnionLast
            D
            (union (copy D' (suc n)) (copy D' (suc n')))
            (A , nA + n * nA + (nA + n' * nA)))
          (unionCopy-R-head
            T
            (D ∷ (A , nA + n * nA + (nA + n' * nA)))
            D'
            (suc n)
            (suc n')
            (seq-exchange-head
              T
              T
              (union D (copy D' (suc (n + (suc n')))) ∷ (A , nA + n * nA + (nA + n' * nA)))
              (union (D ∷ (A , nA + n * nA + (nA + n' * nA))) (copy D' (suc n + (suc n'))))
              idLE
              (ListExchangeSym
                (exchangeUnionLast
                  D
                  (copy D' (suc n + (suc n')))
                  (A , nA + n * nA + (nA + n' * nA))))
              (PreproofCong
                p
                (cong
                  (λ x -> head (T , (union D (copy D' (suc (n + suc n')))) ∷ (A , x)))
                  (a+b*c=a*c+b*c (suc n) (suc n') nA)))))))
                  
  PreproofCongKeepLeaves :
    {G G' : LHSeq} ->
    (pG : Preproof G) ->
    (G=G' : G ≡ G') ->
    (leaves (PreproofCong pG G=G')) ≡ leaves pG
  PreproofCongKeepLeaves pG refl = refl

  unionCopy-LKeepLeaves :
    {G : LHSeq} ->
    {T T' D : ListLTerm} ->
    {n n' : ℕ} ->
    (ppG : Preproof (G ∣ (union T (copy T' (n + n')) , D))) ->
    leaves (unionCopy-L G T T' D n n' ppG) ≡ leaves ppG
  unionCopy-LKeepLeaves {n = zero} {zero} ppG =
    refl
  unionCopy-LKeepLeaves {G} {T} {T'} {D} {n = zero} {suc n'} ppG =
    PreproofCongKeepLeaves
      ppG
      (cong
        (λ x -> G ∣ (union T x , D))
        (sym (union[]T=T (copy T' (suc n')))))
  unionCopy-LKeepLeaves {G} {T} {T'} {D} {n = suc n} {zero} ppG =
    PreproofCongKeepLeaves
      ppG
      (cong
        (λ x -> G ∣ (union T (copy T' (suc x)) , D))
        (sym a=a+0))
  unionCopy-LKeepLeaves {G} {T} {[]} {D} {suc n} {suc n'} ppG =
    refl
  unionCopy-LKeepLeaves {G} {T} {T' ∷ (A , nA)} {D} {suc n} {suc n'} ppG =
    trans
      (unionCopy-LKeepLeaves {G} {T ∷ (A , nA + n * nA + (nA + n' * nA))} {T'} {D} {suc n} {suc n'}
        (seq-exchange
          G
          (union T (copy T' (suc (n + (suc n')))) ∷ (A , nA + n * nA + (nA + n' * nA)))
          (union (T ∷ (A , nA + n * nA + (nA + n' * nA))) (copy T' (suc n + (suc n'))))
          D
          D
          (ListExchangeSym
            (exchangeUnionLast
              T
              (copy T' (suc n + (suc n')))
              (A , nA + n * nA + (nA + n' * nA))))
          idLE
          (PreproofCong
            ppG
            (cong
              (λ x -> G ∣ ((union T (copy T' (suc (n + suc n')))) ∷ (A , x) , D))
              (a+b*c=a*c+b*c (suc n) (suc n') nA)))))
      (PreproofCongKeepLeaves
        ppG
        (cong
          (λ x -> G ∣ ((union T (copy T' (suc (n + suc n'))) ∷ (A , x)) , D))
          (a+b*c=a*c+b*c (suc n) (suc n') nA)))

  unionCopy-RKeepLeaves :
    {G : LHSeq} ->
    {T D D' : ListLTerm} ->
    {n n' : ℕ} ->
    (ppG : Preproof (G ∣ (T , union D (copy D' (n + n'))))) ->
    leaves (unionCopy-R G T D D' n n' ppG) ≡ leaves ppG
  unionCopy-RKeepLeaves {n = zero} {zero} ppG =
    refl
  unionCopy-RKeepLeaves {G} {T} {D} {D'} {n = zero} {suc n'} ppG =
    PreproofCongKeepLeaves
      ppG
      (cong
        (λ x -> G ∣ (T , union D x))
        (sym (union[]T=T (copy D' (suc n')))))
  unionCopy-RKeepLeaves {G} {T} {D} {D'} {n = suc n} {zero} ppG =
    PreproofCongKeepLeaves
      ppG
      (cong
        (λ x -> G ∣ (T , union D (copy D' (suc x))))
        (sym a=a+0))
  unionCopy-RKeepLeaves {G} {T} {D} {[]} {suc n} {suc n'} ppG =
    refl
  unionCopy-RKeepLeaves {G} {T} {D} {D' ∷ (A , nA)} {suc n} {suc n'} ppG =
    trans
      (unionCopy-RKeepLeaves
        {G}
        {T}
        {D ∷ (A , nA + n * nA + (nA + n' * nA))}
        {D'}
        {suc n}
        {suc n'}
        (seq-exchange
          G
          T
          T
          (union D (copy D' (suc (n + (suc n')))) ∷ (A , nA + n * nA + (nA + n' * nA)))
          (union (D ∷ (A , nA + n * nA + (nA + n' * nA))) (copy D' (suc n + (suc n'))))
          idLE
          (ListExchangeSym
            (exchangeUnionLast
              D
              (copy D' (suc n + (suc n')))
              (A , nA + n * nA + (nA + n' * nA))))
          (PreproofCong
            ppG
            (cong
              (λ x -> G ∣ (T , (union D (copy D' (suc (n + suc n')))) ∷ (A , x)))
              (a+b*c=a*c+b*c (suc n) (suc n') nA)))))
      (PreproofCongKeepLeaves
        ppG
        (cong
          (λ x -> G ∣ (T , (union D (copy D' (suc (n + suc n'))) ∷ (A , x))))
          (a+b*c=a*c+b*c (suc n) (suc n') nA)))

  unionCopy-L-headKeepLeaves :
    {T T' D : ListLTerm} ->
    {n n' : ℕ} ->
    (ppG : Preproof (head (union T (copy T' (n + n')) , D))) ->
    leaves (unionCopy-L-head T T' D n n' ppG) ≡ leaves ppG
  unionCopy-L-headKeepLeaves {n = zero} {zero} ppG =
    refl
  unionCopy-L-headKeepLeaves {T} {T'} {D} {n = zero} {suc n'} ppG =
    PreproofCongKeepLeaves
      ppG
      (cong
        (λ x -> head (union T x , D))
        (sym (union[]T=T (copy T' (suc n')))))
  unionCopy-L-headKeepLeaves {T} {T'} {D} {n = suc n} {zero} ppG =
    PreproofCongKeepLeaves
      ppG
      (cong
        (λ x -> head (union T (copy T' (suc x)) , D))
        (sym a=a+0))
  unionCopy-L-headKeepLeaves {T} {[]} {D} {suc n} {suc n'} ppG =
    refl
  unionCopy-L-headKeepLeaves {T} {T' ∷ (A , nA)} {D} {suc n} {suc n'} ppG =
    trans
      (unionCopy-L-headKeepLeaves {T ∷ (A , nA + n * nA + (nA + n' * nA))} {T'} {D} {suc n} {suc n'}
        (seq-exchange-head
          (union T (copy T' (suc (n + (suc n')))) ∷ (A , nA + n * nA + (nA + n' * nA)))
          (union (T ∷ (A , nA + n * nA + (nA + n' * nA))) (copy T' (suc n + (suc n'))))
          D
          D
          (ListExchangeSym
            (exchangeUnionLast
              T
              (copy T' (suc n + (suc n')))
              (A , nA + n * nA + (nA + n' * nA))))
          idLE
          (PreproofCong
            ppG
            (cong
              (λ x -> head ((union T (copy T' (suc (n + suc n')))) ∷ (A , x) , D))
              (a+b*c=a*c+b*c (suc n) (suc n') nA)))))
      (PreproofCongKeepLeaves
        ppG
        (cong
          (λ x -> head ((union T (copy T' (suc (n + suc n'))) ∷ (A , x)) , D))
          (a+b*c=a*c+b*c (suc n) (suc n') nA)))

  unionCopy-R-headKeepLeaves :
    {T D D' : ListLTerm} ->
    {n n' : ℕ} ->
    (ppG : Preproof (head (T , union D (copy D' (n + n'))))) ->
    leaves (unionCopy-R-head T D D' n n' ppG) ≡ leaves ppG
  unionCopy-R-headKeepLeaves {n = zero} {zero} ppG =
    refl
  unionCopy-R-headKeepLeaves {T} {D} {D'} {n = zero} {suc n'} ppG =
    PreproofCongKeepLeaves
      ppG
      (cong
        (λ x -> head (T , union D x))
        (sym (union[]T=T (copy D' (suc n')))))
  unionCopy-R-headKeepLeaves {T} {D} {D'} {n = suc n} {zero} ppG =
    PreproofCongKeepLeaves
      ppG
      (cong
        (λ x -> head (T , union D (copy D' (suc x))))
        (sym a=a+0))
  unionCopy-R-headKeepLeaves {T} {D} {[]} {suc n} {suc n'} ppG =
    refl
  unionCopy-R-headKeepLeaves {T} {D} {D' ∷ (A , nA)} {suc n} {suc n'} ppG =
    trans
      (unionCopy-R-headKeepLeaves
        {T}
        {D ∷ (A , nA + n * nA + (nA + n' * nA))}
        {D'}
        {suc n}
        {suc n'}
        (seq-exchange-head
          T
          T
          (union D (copy D' (suc (n + (suc n')))) ∷ (A , nA + n * nA + (nA + n' * nA)))
          (union (D ∷ (A , nA + n * nA + (nA + n' * nA))) (copy D' (suc n + (suc n'))))
          idLE
          (ListExchangeSym
            (exchangeUnionLast
              D
              (copy D' (suc n + (suc n')))
              (A , nA + n * nA + (nA + n' * nA))))
          (PreproofCong
            ppG
            (cong
              (λ x -> head (T , (union D (copy D' (suc (n + suc n')))) ∷ (A , x)))
              (a+b*c=a*c+b*c (suc n) (suc n') nA)))))
      (PreproofCongKeepLeaves
        ppG
        (cong
          (λ x -> head (T , (union D (copy D' (suc (n + suc n'))) ∷ (A , x))))
          (a+b*c=a*c+b*c (suc n) (suc n') nA)))

