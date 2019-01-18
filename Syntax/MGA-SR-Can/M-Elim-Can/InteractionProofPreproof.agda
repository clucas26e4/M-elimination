module Syntax.MGA-SR-Can.M-Elim-Can.InteractionProofPreproof where
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
  open import Syntax.MGA-SR-Can.M-Elim-Can.Preproof
  open import Syntax.MGA-SR-Can

  proofToPreproof :
    {G : LHSeq} ->
    MGA-SR† G ->
    Preproof G
  proofToPreproof ax =
    ax
  proofToPreproof (W G Γ1 Γ2 Δ1 Δ2 p) =
    W G Γ1 Γ2 Δ1 Δ2 (proofToPreproof p)
  proofToPreproof (C G Γ Δ p) =
    C G Γ Δ (proofToPreproof p)
  proofToPreproof (S G Γ1 Γ2 Δ1 Δ2 refl refl p) =
    S G Γ1 Γ2 Δ1 Δ2 refl refl (proofToPreproof p)
  proofToPreproof (Id-rule G Γ Δ A p) =
    Id-rule G Γ Δ A (proofToPreproof p)
  proofToPreproof (W-head Γ1 Γ2 Δ1 Δ2 p) =
    W-head Γ1 Γ2 Δ1 Δ2 (proofToPreproof p)
  proofToPreproof (C-head Γ Δ p) =
    C-head Γ Δ (proofToPreproof p)
  proofToPreproof (S-head Γ1 Γ2 Δ1 Δ2 refl refl p) =
    S-head Γ1 Γ2 Δ1 Δ2 refl refl (proofToPreproof p)
  proofToPreproof (Id-rule-head Γ Δ A p) =
    Id-rule-head Γ Δ A (proofToPreproof p)
  proofToPreproof (U-L G Γ Δ A n1 n2 refl p) =
    U-L G Γ Δ A n1 n2 refl (proofToPreproof p)
  proofToPreproof (U-R G Γ Δ A n1 n2 refl p) =
    U-R G Γ Δ A n1 n2 refl (proofToPreproof p)
  proofToPreproof (F-L G Γ Δ A n1 n2 refl p) =
    F-L G Γ Δ A n1 n2 refl (proofToPreproof p)
  proofToPreproof (F-R G Γ Δ A n1 n2 refl p) =
    F-R G Γ Δ A n1 n2 refl (proofToPreproof p)
  proofToPreproof (U-L-head Γ Δ A n1 n2 refl p) =
    U-L-head Γ Δ A n1 n2 refl (proofToPreproof p)
  proofToPreproof (U-R-head Γ Δ A n1 n2 refl p) =
    U-R-head Γ Δ A n1 n2 refl (proofToPreproof p)
  proofToPreproof (F-L-head Γ Δ A n1 n2 refl p) =
    F-L-head Γ Δ A n1 n2 refl (proofToPreproof p)
  proofToPreproof (F-R-head Γ Δ A n1 n2 refl p) =
    F-R-head Γ Δ A n1 n2 refl (proofToPreproof p)
  proofToPreproof (E-L G Γ Δ A p) =
    E-L G Γ Δ A (proofToPreproof p)
  proofToPreproof (E-R G Γ Δ A p) =
    E-R G Γ Δ A (proofToPreproof p)
  proofToPreproof (E-L-head Γ Δ A p) =
    E-L-head Γ Δ A (proofToPreproof p)
  proofToPreproof (E-R-head Γ Δ A p) =
    E-R-head Γ Δ A (proofToPreproof p)
  proofToPreproof (plus-L G Γ Δ A B n p) =
    plus-L G Γ Δ A B n (proofToPreproof p)
  proofToPreproof (plus-R G Γ Δ A B n p) =
    plus-R G Γ Δ A B n (proofToPreproof p)
  proofToPreproof (max-L G Γ Δ A B n p p₁) =
    max-L G Γ Δ A B n (proofToPreproof p) (proofToPreproof p₁)
  proofToPreproof (max-R G Γ Δ A B n p) =
    max-R G Γ Δ A B n (proofToPreproof p)
  proofToPreproof (plus-L-head Γ Δ A B n p) =
    plus-L-head Γ Δ A B n (proofToPreproof p)
  proofToPreproof (plus-R-head Γ Δ A B n p) =
    plus-R-head Γ Δ A B n (proofToPreproof p)
  proofToPreproof (max-L-head Γ Δ A B n p p₁) =
    max-L-head Γ Δ A B n (proofToPreproof p) (proofToPreproof p₁)
  proofToPreproof (max-R-head Γ Δ A B n p) =
    max-R-head Γ Δ A B n (proofToPreproof p)
  proofToPreproof (Z-L G Γ Δ n p) =
    Z-L G Γ Δ n (proofToPreproof p)
  proofToPreproof (Z-R G Γ Δ n p) =
    Z-R G Γ Δ n (proofToPreproof p)
  proofToPreproof (Z-L-head Γ Δ n p) =
    Z-L-head Γ Δ n (proofToPreproof p)
  proofToPreproof (Z-R-head Γ Δ n p) =
    Z-R-head Γ Δ n (proofToPreproof p)
  proofToPreproof (minus-L G Γ Δ A n p) =
    minus-L G Γ Δ A n (proofToPreproof p)
  proofToPreproof (minus-R G Γ Δ A n p) =
    minus-R G Γ Δ A n (proofToPreproof p)
  proofToPreproof (minus-L-head Γ Δ A n p) =
    minus-L-head Γ Δ A n (proofToPreproof p)
  proofToPreproof (minus-R-head Γ Δ A n p) =
    minus-R-head Γ Δ A n (proofToPreproof p)
  proofToPreproof (min-L G Γ Δ A B n p) =
    min-L G Γ Δ A B n (proofToPreproof p)
  proofToPreproof (min-R G Γ Δ A B n p p') =
    min-R G Γ Δ A B n (proofToPreproof p) (proofToPreproof p')
  proofToPreproof (min-L-head Γ Δ A B n p) =
    min-L-head Γ Δ A B n (proofToPreproof p)
  proofToPreproof (min-R-head Γ Δ A B n p p') =
    min-R-head Γ Δ A B n (proofToPreproof p) (proofToPreproof p')
  proofToPreproof (◆1-rule Γ Δ ◆Γ ◆Δ refl refl n p) =
    ◆1-rule Γ Δ ◆Γ ◆Δ refl refl n (proofToPreproof p)
  proofToPreproof (◆-rule Γ Δ ◆Γ ◆Δ refl refl p) =
    ◆-rule Γ Δ ◆Γ ◆Δ refl refl (proofToPreproof p)
  proofToPreproof (1-rule G Γ Δ n p) =
    1-rule G Γ Δ n (proofToPreproof p)
  proofToPreproof (1-rule-head Γ Δ n p) =
    1-rule-head Γ Δ n (proofToPreproof p)
  proofToPreproof (seq-exchange G Γ Γ' Δ Δ' x x₁ p) =
    seq-exchange G Γ Γ' Δ Δ' x x₁ (proofToPreproof p)
  proofToPreproof (seq-exchange-head Γ Γ' Δ Δ' x x₁ p) =
    seq-exchange-head Γ Γ' Δ Δ' x x₁ (proofToPreproof p)
  proofToPreproof (hseq-exchange G G' x p) =
    hseq-exchange G G' x (proofToPreproof p)
  proofToPreproof (can-rule G Γ Δ A p) =
    can-rule G Γ Δ A (proofToPreproof p)
  proofToPreproof (can-rule-head Γ Δ A p) =
    can-rule-head Γ Δ A (proofToPreproof p)

  finishPreproof :
    {G : LHSeq} ->
    (ppG : Preproof G) ->
    Prooflist (leaves ppG) ->
    MGA-SR† G
  finishPreproof (leaf G) (consP pL pG) =
    pG
  finishPreproof ax pL =
    ax
  finishPreproof (W G Γ1 Γ2 Δ1 Δ2 ppG) pL =
    W G Γ1 Γ2 Δ1 Δ2 (finishPreproof ppG pL)
  finishPreproof (C G Γ Δ ppG) pL =
    C G Γ Δ (finishPreproof ppG pL)
  finishPreproof (S G Γ1 Γ2 Δ1 Δ2 refl refl ppG) pL =
    S G Γ1 Γ2 Δ1 Δ2 refl refl (finishPreproof ppG pL)
  finishPreproof (Id-rule G Γ Δ A ppG) pL =
    Id-rule G Γ Δ A (finishPreproof ppG pL)
  finishPreproof (W-head Γ1 Γ2 Δ1 Δ2 ppG) pL =
    W-head Γ1 Γ2 Δ1 Δ2 (finishPreproof ppG pL)
  finishPreproof (C-head Γ Δ ppG) pL =
    C-head Γ Δ (finishPreproof ppG pL)
  finishPreproof (S-head Γ1 Γ2 Δ1 Δ2 refl refl ppG) pL =
    S-head Γ1 Γ2 Δ1 Δ2 refl refl (finishPreproof ppG pL)
  finishPreproof (Id-rule-head Γ Δ A ppG) pL =
    Id-rule-head Γ Δ A (finishPreproof ppG pL)
  finishPreproof (U-L G Γ Δ A n1 n2 refl ppG) pL =
    U-L G Γ Δ A n1 n2 refl (finishPreproof ppG pL)
  finishPreproof (U-R G Γ Δ A n1 n2 refl ppG) pL =
    U-R G Γ Δ A n1 n2 refl (finishPreproof ppG pL)
  finishPreproof (F-L G Γ Δ A n1 n2 refl ppG) pL =
    F-L G Γ Δ A n1 n2 refl (finishPreproof ppG pL)
  finishPreproof (F-R G Γ Δ A n1 n2 refl ppG) pL =
    F-R G Γ Δ A n1 n2 refl (finishPreproof ppG pL)
  finishPreproof (U-L-head Γ Δ A n1 n2 refl ppG) pL =
    U-L-head Γ Δ A n1 n2 refl (finishPreproof ppG pL)
  finishPreproof (U-R-head Γ Δ A n1 n2 refl ppG) pL =
    U-R-head Γ Δ A n1 n2 refl (finishPreproof ppG pL)
  finishPreproof (F-L-head Γ Δ A n1 n2 refl ppG) pL =
    F-L-head Γ Δ A n1 n2 refl  (finishPreproof ppG pL)
  finishPreproof (F-R-head Γ Δ A n1 n2 refl ppG) pL =
    F-R-head Γ Δ A n1 n2 refl (finishPreproof ppG pL)
  finishPreproof (E-L G Γ Δ A ppG) pL =
    E-L G Γ Δ A (finishPreproof ppG pL)
  finishPreproof (E-R G Γ Δ A ppG) pL =
    E-R G Γ Δ A (finishPreproof ppG pL)
  finishPreproof (E-L-head Γ Δ A ppG) pL =
    E-L-head Γ Δ A (finishPreproof ppG pL)
  finishPreproof (E-R-head Γ Δ A ppG) pL =
    E-R-head Γ Δ A (finishPreproof ppG pL)
  finishPreproof (plus-L G Γ Δ A B n ppG) pL =
    plus-L G Γ Δ A B n (finishPreproof ppG pL)
  finishPreproof (plus-R G Γ Δ A B n ppG) pL = 
    plus-R G Γ Δ A B n (finishPreproof ppG pL)
  finishPreproof (max-L G Γ Δ A B n ppG ppG₁) pL =
    max-L G Γ Δ A B n (finishPreproof ppG (Prooflist-L (leaves ppG) (leaves ppG₁) pL)) (finishPreproof ppG₁ (Prooflist-R (leaves ppG) (leaves ppG₁) pL))
  finishPreproof (max-R G Γ Δ A B n ppG) pL =
    max-R G Γ Δ A B n (finishPreproof ppG pL)
  finishPreproof (plus-L-head Γ Δ A B n ppG) pL =
    plus-L-head Γ Δ A B n (finishPreproof ppG pL)
  finishPreproof (plus-R-head Γ Δ A B n ppG) pL =
    plus-R-head Γ Δ A B n (finishPreproof ppG pL)
  finishPreproof (max-L-head Γ Δ A B n ppG ppG₁) pL = 
    max-L-head Γ Δ A B n (finishPreproof ppG (Prooflist-L (leaves ppG) (leaves ppG₁) pL)) (finishPreproof ppG₁ (Prooflist-R (leaves ppG) (leaves ppG₁) pL))
  finishPreproof (max-R-head Γ Δ A B n ppG) pL = 
    max-R-head Γ Δ A B n (finishPreproof ppG pL)
  finishPreproof (Z-L G Γ Δ n p) pL =
    Z-L G Γ Δ n (finishPreproof p pL)
  finishPreproof (Z-R G Γ Δ n p) pL =
    Z-R G Γ Δ n (finishPreproof p pL)
  finishPreproof (Z-L-head Γ Δ n p) pL =
    Z-L-head Γ Δ n (finishPreproof p pL)
  finishPreproof (Z-R-head Γ Δ n p) pL =
    Z-R-head Γ Δ n (finishPreproof p pL)
  finishPreproof (minus-L G Γ Δ A n p) pL =
    minus-L G Γ Δ A n (finishPreproof p pL)
  finishPreproof (minus-R G Γ Δ A n p) pL =
    minus-R G Γ Δ A n (finishPreproof p pL)
  finishPreproof (minus-L-head Γ Δ A n p) pL =
    minus-L-head Γ Δ A n (finishPreproof p pL)
  finishPreproof (minus-R-head Γ Δ A n p) pL =
    minus-R-head Γ Δ A n (finishPreproof p pL)
  finishPreproof (min-L G Γ Δ A B n p) pL =
    min-L G Γ Δ A B n (finishPreproof p pL)
  finishPreproof (min-R G Γ Δ A B n p p') pL =
    min-R G Γ Δ A B n (finishPreproof p (Prooflist-L (leaves p) (leaves p') pL)) (finishPreproof p' (Prooflist-R (leaves p) (leaves p') pL))
  finishPreproof (min-L-head Γ Δ A B n p) pL =
    min-L-head Γ Δ A B n (finishPreproof p pL)
  finishPreproof (min-R-head Γ Δ A B n p p') pL =
    min-R-head Γ Δ A B n (finishPreproof p (Prooflist-L (leaves p) (leaves p') pL)) (finishPreproof p' (Prooflist-R (leaves p) (leaves p') pL))
  finishPreproof (◆1-rule Γ Δ ◆Γ ◆Δ refl refl n p) pL =
    ◆1-rule Γ Δ ◆Γ ◆Δ refl refl n (finishPreproof p pL)
  finishPreproof (◆-rule Γ Δ ◆Γ ◆Δ refl refl p) pL =
    ◆-rule Γ Δ ◆Γ ◆Δ refl refl (finishPreproof p pL)
  finishPreproof (1-rule G Γ Δ n p) pL =
    1-rule G Γ Δ n (finishPreproof p pL)
  finishPreproof (1-rule-head Γ Δ n p) pL =
    1-rule-head Γ Δ n (finishPreproof p pL)
  finishPreproof (seq-exchange G Γ Γ' Δ Δ' x x₁ ppG) pL =
    seq-exchange G Γ Γ' Δ Δ' x x₁ (finishPreproof ppG pL)
  finishPreproof (seq-exchange-head Γ Γ' Δ Δ' x x₁ ppG) pL =
    seq-exchange-head Γ Γ' Δ Δ' x x₁ (finishPreproof ppG pL)
  finishPreproof (hseq-exchange G G' x ppG) pL =
    hseq-exchange G G' x (finishPreproof ppG pL)
  finishPreproof (can-rule G Γ Δ A p) pL =
    can-rule G Γ Δ A (finishPreproof p pL)
  finishPreproof (can-rule-head Γ Δ A p) pL =
    can-rule-head Γ Δ A (finishPreproof p pL)


  leavesMGA-SR† :
    {G : LHSeq} ->
    (pG : MGA-SR† G) ->
    leaves (proofToPreproof pG) ≡ []H
  leavesMGA-SR† ax =
    refl
  leavesMGA-SR† (W G Γ1 Γ2 Δ1 Δ2 pG) =
    leavesMGA-SR† pG
  leavesMGA-SR† (C G Γ Δ pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (S G Γ1 Γ2 Δ1 Δ2 refl refl pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (Id-rule G Γ Δ A pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (W-head Γ1 Γ2 Δ1 Δ2 pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (C-head Γ Δ pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (S-head Γ1 Γ2 Δ1 Δ2 refl refl pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (Id-rule-head Γ Δ A pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (U-L G Γ Δ A n1 n2 refl pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (U-R G Γ Δ A n1 n2 refl pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (F-L G Γ Δ A n1 n2 refl pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (F-R G Γ Δ A n1 n2 refl pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (U-L-head Γ Δ A n1 n2 refl pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (U-R-head Γ Δ A n1 n2 refl pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (F-L-head Γ Δ A n1 n2 refl pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (F-R-head Γ Δ A n1 n2 refl pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (E-L G Γ Δ A pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (E-R G Γ Δ A pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (E-L-head Γ Δ A pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (E-R-head Γ Δ A pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (plus-L G Γ Δ A B n pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (plus-R G Γ Δ A B n pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (max-L G Γ Δ A B n pG pG₁) =
    begin
      unionHL (leaves (proofToPreproof pG)) (leaves (proofToPreproof pG₁))
        ≡⟨ cong
             (λ x -> unionHL x (leaves (proofToPreproof pG₁)))
             (leavesMGA-SR† pG) ⟩
      leaves (proofToPreproof pG₁)
        ≡⟨ leavesMGA-SR† pG₁ ⟩
      []H ∎
  leavesMGA-SR† (max-R G Γ Δ A B n pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (plus-L-head Γ Δ A B n pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (plus-R-head Γ Δ A B n pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (max-L-head Γ Δ A B n pG pG₁) = 
    begin
      unionHL (leaves (proofToPreproof pG)) (leaves (proofToPreproof pG₁))
        ≡⟨ cong
             (λ x -> unionHL x (leaves (proofToPreproof pG₁)))
             (leavesMGA-SR† pG) ⟩
      leaves (proofToPreproof pG₁)
        ≡⟨ leavesMGA-SR† pG₁ ⟩
      []H ∎
  leavesMGA-SR† (max-R-head Γ Δ A B n pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (Z-L G Γ Δ n p) =
   leavesMGA-SR† p
  leavesMGA-SR† (Z-R G Γ Δ n p) =
    leavesMGA-SR† p
  leavesMGA-SR† (Z-L-head Γ Δ n p) =
    leavesMGA-SR† p
  leavesMGA-SR† (Z-R-head Γ Δ n p) =
    leavesMGA-SR† p
  leavesMGA-SR† (minus-L G Γ Δ A n p) =
    leavesMGA-SR† p
  leavesMGA-SR† (minus-R G Γ Δ A n p) =
    leavesMGA-SR† p
  leavesMGA-SR† (minus-L-head Γ Δ A n p) =
    leavesMGA-SR† p
  leavesMGA-SR† (minus-R-head Γ Δ A n p) =
    leavesMGA-SR† p
  leavesMGA-SR† (min-L G Γ Δ A B n p) =
    leavesMGA-SR† p
  leavesMGA-SR† (min-R G Γ Δ A B n p p') =
    begin
      unionHL (leaves (proofToPreproof p)) (leaves (proofToPreproof p'))
        ≡⟨ cong
             (λ x -> unionHL x (leaves (proofToPreproof p')))
             (leavesMGA-SR† p) ⟩
      leaves (proofToPreproof p')
        ≡⟨ leavesMGA-SR† p' ⟩
      []H ∎
  leavesMGA-SR† (min-L-head Γ Δ A B n p) =
    leavesMGA-SR† p
  leavesMGA-SR† (min-R-head Γ Δ A B n p p') = 
    begin
      unionHL (leaves (proofToPreproof p)) (leaves (proofToPreproof p'))
        ≡⟨ cong
             (λ x -> unionHL x (leaves (proofToPreproof p')))
             (leavesMGA-SR† p) ⟩
      leaves (proofToPreproof p')
        ≡⟨ leavesMGA-SR† p' ⟩
      []H ∎
  leavesMGA-SR† (◆1-rule Γ Δ ◆Γ ◆Δ refl refl n p) =
    leavesMGA-SR† p
  leavesMGA-SR† (◆-rule Γ Δ ◆Γ ◆Δ refl refl p) =
    leavesMGA-SR† p
  leavesMGA-SR† (1-rule G Γ Δ n p) =
    leavesMGA-SR† p
  leavesMGA-SR† (1-rule-head Γ Δ n p) =
    leavesMGA-SR† p
  leavesMGA-SR† (seq-exchange G Γ Γ' Δ Δ' x x₁ pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (seq-exchange-head Γ Γ' Δ Δ' x x₁ pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (hseq-exchange G G' x pG) = 
    leavesMGA-SR† pG
  leavesMGA-SR† (can-rule G Γ Δ A p) =
    leavesMGA-SR† p
  leavesMGA-SR† (can-rule-head Γ Δ A p) =
    leavesMGA-SR† p

  congKeepLeaves :
    {G G' : LHSeq} ->
    (pG : Preproof G) ->
    (G=G' : G ≡ G') ->
    leaves (PreproofCong pG G=G') ≡ leaves pG
  congKeepLeaves pG refl =
    refl
