module Syntax.MGA-SR.M-ElimCan.PumpingLemma where
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
  open import Syntax.MGA-SR
  open import Syntax.MGA-SR.Properties
  open import Syntax.ListLTerm.Properties
  open import Syntax.LHSeq.Properties

  {- Semantic -}

  data Pumping : LHSeq -> Set where
    headPumping :
      (H : LSeq) ->
      (n : ℕ) ->
      Pumping (head H)
    consPumping :
      (G : LHSeq) ->
      (pump : Pumping G) ->
      (H : LSeq) ->
      (n : ℕ) ->
      Pumping (G ∣ H)

  idPumping :
    (G : LHSeq) ->
    Pumping G
--{{{
  idPumping (head H) =
    headPumping H 1
  idPumping (G ∣ H) =
    consPumping G (idPumping G) H 1
--}}}

  pumpExchange :
    (G G' : LHSeq) ->
    Pumping G ->
    LHSeqExchange G G' ->
    Pumping G'
--{{{
  pumpExchange G .G pump idHE =
    pump
  pumpExchange .(G ∣ H₁ ∣ H) (G' ∣ .H ∣ .H₁) (consPumping .(G ∣ H₁) (consPumping G pump H₁ n₁) H n) (exHE G=G') =
    consPumping
      (G' ∣ H)
      (consPumping
        G'
        (pumpExchange G G' pump G=G')
        H
        n)
      H₁
      n₁
  pumpExchange .(head H₁ ∣ H) .(head H ∣ H₁) (consPumping .(head H₁) (headPumping H₁ n₁) H n) exHE-head =
    consPumping
      (head H)
      (headPumping
        H
        n)
      H₁
      n₁
  pumpExchange G G' pump (transHE {G₂ = G₂} G=G' G=G'') =
    pumpExchange G₂ G' (pumpExchange G G₂ pump G=G') G=G''
  pumpExchange .(G ∣ H) .(G' ∣ H) (consPumping .G pump H n) (indHE G G' G=G') =
    consPumping
      G'
      (pumpExchange G G' pump G=G')
      H
      n
--}}}

  doPumping :
    (G : LHSeq) ->
    Pumping G ->
    LHSeq
--{{{
  doPumping .(head H) (headPumping H n) =
    head (copyLSeq H n) 
  doPumping .(G ∣ H) (consPumping G pump H n) = 
    (doPumping G pump) ∣ (copyLSeq H n)
--}}}

  doPumpingExchange :
    (G G' : LHSeq) ->
    (pump : Pumping G) ->
    (G=G' : LHSeqExchange G G') ->
    LHSeqExchange (doPumping G pump) (doPumping G' (pumpExchange G G' pump G=G'))
--{{{    
  doPumpingExchange G .G pump idHE =
    idHE
  doPumpingExchange .(G ∣ H₁ ∣ H) (G' ∣ H ∣ H₁) (consPumping .(G ∣ H₁) (consPumping G pump H₁ n₁) H n) (exHE G=G') =
    exHE
      (doPumpingExchange G G' pump G=G')
  doPumpingExchange .(head H₁ ∣ H) .(head H ∣ H₁) (consPumping .(head H₁) (headPumping H₁ n₁) H n) exHE-head =
    exHE-head
  doPumpingExchange G G' pump (transHE {G₂ = G₂} G=G' G=G'') =
    transHE
      (doPumpingExchange G G₂ pump G=G')
      (doPumpingExchange G₂ G' (pumpExchange G G₂ pump G=G') G=G'')
  doPumpingExchange .(G ∣ _) .(G' ∣ _) (consPumping G pump H n) (indHE G G' G=G') =
    indHE
      (doPumping G pump)
      (doPumping G' (pumpExchange G G' pump G=G'))
      (doPumpingExchange G G' pump G=G')
--}}}

  idDoPumping :
    (G : LHSeq) ->
    doPumping G (idPumping G) ≡ G
--{{{
  idDoPumping (head H) =
    cong head
      (idCopyLSeq H)
  idDoPumping (G ∣ H) =
    begin
      doPumping G (idPumping G) ∣ copyLSeq H 1
        ≡⟨ cong (λ x -> x ∣ copyLSeq H 1)
             (idDoPumping G) ⟩
      G ∣ copyLSeq H 1
        ≡⟨ cong (λ x -> G ∣ x)
             (idCopyLSeq H) ⟩
      G ∣ H ∎
--}}}

  PumpingLemmaGen-S-Lemma1 :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    (n : ℕ) ->
    MGA-SR† (G ∣ (copy T (suc n) , copy D (suc n))) ->
    MGA-SR† (G ∣ (T , D))
--{{{    
  PumpingLemmaGen-S-Lemma1 G T D zero p = 
    MGA-SR†Cong
      {G ∣ ( (copy T 1) , (copy D 1))}
      p
      (cong₂
        (λ x y -> G ∣ (x , y))
        (idCopy T)
        (idCopy D))
  PumpingLemmaGen-S-Lemma1 G T D (suc n) p =
    C
      G
      T
      D
      (PumpingLemmaGen-S-Lemma1
        (G ∣ (T , D))
        T
        D
        n
        (hseq-exchange
          (G ∣ (copy T (suc n) , copy D (suc n)) ∣ (T , D))
          (G ∣ (T , D) ∣ (copy T (suc n) , copy D (suc n)))
          (exHE
            idHE)
          (S
            G
            (copy T (suc n))
            T
            (copy D (suc n))
            D
            refl
            refl
            (UnfoldMGA-SR†Copy-L
              G
              T
              (union (copy D (suc n)) D)
              (suc n)
              (UnfoldMGA-SR†Copy-R
                G
                (copy T (suc (suc n)))
                D
                (suc n)
                p)))))
--}}}

  PropPumpingLemmaGen-S-Lemma1 :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    (n : ℕ) ->
    (p : MGA-SR† (G ∣ (copy T (suc n) , copy D (suc n)))) ->
    #◆ (PumpingLemmaGen-S-Lemma1 G T D n p) ≤ #◆ p
--{{{
  PropPumpingLemmaGen-S-Lemma1 G T D zero p =
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          p
          (cong₂
            (λ x y -> G ∣ (x , y))
            (idCopy T)
            (idCopy D))))
      (k≤k (#◆ p))
  PropPumpingLemmaGen-S-Lemma1 G T D (suc n) p =
    ≤-trans
      (PropPumpingLemmaGen-S-Lemma1
        (G ∣ (T , D))
        T
        D
        n
        (hseq-exchange
          (G ∣ (copy T (suc n) , copy D (suc n)) ∣ (T , D))
          (G ∣ (T , D) ∣ (copy T (suc n) , copy D (suc n)))
          (exHE
            idHE)
          (S
            G
            (copy T (suc n))
            T
            (copy D (suc n))
            D
            refl
            refl
            (UnfoldMGA-SR†Copy-L
              G
              T
              (union (copy D (suc n)) D)
              (suc n)
              (UnfoldMGA-SR†Copy-R
                G
                (copy T (suc (suc n)))
                D
                (suc n)
                p)))))
      (cong-≤-l
        (sym
          (UnfoldMGA-SR†Copy-LKeep#◆
            G
            T
            (union (copy D (suc n)) D)
            (suc n)
            (UnfoldMGA-SR†Copy-R G (copy T (suc (suc n))) D (suc n) p)))
        (cong-≤-l
          (sym
            (UnfoldMGA-SR†Copy-RKeep#◆
              G
              (copy T (suc (suc n)))
              D
              (suc n)
              p))
          (k≤k (#◆ p))))
--}}}
  
  PumpingLemmaGen-S-Lemma2 :
    (G : LHSeq) ->
    (T T' D D' : ListLTerm) ->
    (n1 n2 : ℕ) ->
    MGA-SR† (G ∣ ((union (copy T (n1 * n2)) (copy T' (n1 * n2))) , (union (copy D (n1 * n2)) (copy D' (n1 * n2))))) ->
    MGA-SR† (G ∣ (copy T n1 , copy D n1) ∣ (copy T' n2 , copy D' n2))
--{{{
  PumpingLemmaGen-S-Lemma2 G T T' D D' n1 zero p =
    ΔGen
      (G ∣ (copy T n1 , copy D n1))
  PumpingLemmaGen-S-Lemma2 G T T' D D' zero (suc n2) p =
    hseq-exchange
      (G ∣ (copy T' (suc n2) , copy D' (suc n2)) ∣ ([] , []))
      (G ∣ ([] , []) ∣ (copy T' (suc n2) , copy D' (suc n2)))
      (exHE
        idHE)
      (ΔGen
        (G ∣ (copy T' (suc n2) , copy D' (suc n2))))
  PumpingLemmaGen-S-Lemma2 G T T' D D' (suc n1) (suc n2) p = 
    hseq-exchange
      (G ∣ (copy T' (suc n2) , copy D' (suc n2)) ∣ (copy T (suc n1) , copy D (suc n1)))
      (G ∣ (copy T (suc n1) , copy D (suc n1)) ∣ (copy T' (suc n2) , copy D' (suc n2)))
      (exHE
        idHE)
      (PumpingLemmaGen-S-Lemma1
        (G ∣ (copy T' (suc n2) , copy D' (suc n2)))
        (copy T (suc n1))
        (copy D (suc n1))
        n2
        (MGA-SR†Cong
          {G ∣ (copy T' (suc n2) , copy D' (suc n2)) ∣ (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2)))}
          (hseq-exchange
            (G ∣ (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))) ∣ (copy T' (suc n2) , copy D' (suc n2)))
            (G ∣ (copy T' (suc n2) , copy D' (suc n2)) ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))))
            (exHE
              idHE)
            (PumpingLemmaGen-S-Lemma1
              (G ∣ (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))))
              (copy T' (suc n2))
              (copy D' (suc n2))
              n1
              (MGA-SR†Cong
                {G ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (copy T' ((suc n1) * (suc n2)) , copy D' ((suc n1) * (suc n2)))}
                (S
                  G
                  (copy T ((suc n1) * (suc n2)))
                  (copy T' ((suc n1) * (suc n2)))
                  (copy D ((suc n1) * (suc n2)))
                  (copy D' ((suc n1) * (suc n2)))
                  refl
                  refl
                  p)
                (cong₂
                  (λ x y -> G ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (x , y))
                  (sym
                    (begin
                      copy (copy T' (suc n2)) (suc n1)
                        ≡⟨ doubleCopy T' (suc n2) (suc n1) ⟩
                      copy T' ((suc n2) * (suc n1))
                        ≡⟨ cong
                             (λ x -> copy T' x)
                             (*-comm (suc n2) (suc n1)) ⟩
                      copy T' ((suc n1) * (suc n2)) ∎))
                  (sym
                    (begin
                      copy (copy D' (suc n2)) (suc n1)
                        ≡⟨ doubleCopy D' (suc n2) (suc n1) ⟩
                      copy D' ((suc n2) * (suc n1))
                        ≡⟨ cong
                             (λ x -> copy D' x)
                             (*-comm (suc n2) (suc n1)) ⟩
                      copy D' ((suc n1) * (suc n2)) ∎))))))
          (cong₂
            (λ x y -> G ∣ (copy T' (suc n2) , copy D' (suc n2)) ∣ (x , y))
            (sym
              (doubleCopy
                T
                (suc n1)
                (suc n2)))
            (sym
              (doubleCopy
                D
                (suc n1)
                (suc n2))))))
--}}}

  PropPumpingLemmaGen-S-Lemma2 :
    (G : LHSeq) ->
    (T T' D D' : ListLTerm) ->
    (n1 n2 : ℕ) ->
    (p : MGA-SR† (G ∣ ((union (copy T (n1 * n2)) (copy T' (n1 * n2))) , (union (copy D (n1 * n2)) (copy D' (n1 * n2)))))) ->
    #◆ (PumpingLemmaGen-S-Lemma2 G T T' D D' n1 n2 p) ≤ #◆ p
--{{{
  PropPumpingLemmaGen-S-Lemma2 G T T' D D' n1 zero p =
    cong-≤-l
      (sym
        (ΔGenNo◆ G))
      z≤n
  PropPumpingLemmaGen-S-Lemma2 G T T' D D' zero (suc n2) p = 
    cong-≤-l
      (sym
        (ΔGenNo◆ G))
      z≤n
  PropPumpingLemmaGen-S-Lemma2 G T T' D D' (suc n1) (suc n2) p =
    ≤-trans
      (PropPumpingLemmaGen-S-Lemma1
        (G ∣ (copy T' (suc n2) , copy D' (suc n2)))
        (copy T (suc n1))
        (copy D (suc n1))
        n2
        (MGA-SR†Cong
          {G ∣ (copy T' (suc n2) , copy D' (suc n2)) ∣ (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2)))}
          (hseq-exchange
            (G ∣ (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))) ∣ (copy T' (suc n2) , copy D' (suc n2)))
            (G ∣ (copy T' (suc n2) , copy D' (suc n2)) ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))))
            (exHE
              idHE)
            (PumpingLemmaGen-S-Lemma1
              (G ∣ (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))))
              (copy T' (suc n2))
              (copy D' (suc n2))
              n1
              (MGA-SR†Cong
                {G ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (copy T' ((suc n1) * (suc n2)) , copy D' ((suc n1) * (suc n2)))}
                (S
                  G
                  (copy T ((suc n1) * (suc n2)))
                  (copy T' ((suc n1) * (suc n2)))
                  (copy D ((suc n1) * (suc n2)))
                  (copy D' ((suc n1) * (suc n2)))
                  refl
                  refl
                  p)
                (cong₂
                  (λ x y -> G ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (x , y))
                  (sym
                    (begin
                      copy (copy T' (suc n2)) (suc n1)
                        ≡⟨ doubleCopy T' (suc n2) (suc n1) ⟩
                      copy T' ((suc n2) * (suc n1))
                        ≡⟨ cong
                             (λ x -> copy T' x)
                             (*-comm (suc n2) (suc n1)) ⟩
                      copy T' ((suc n1) * (suc n2)) ∎))
                  (sym
                    (begin
                      copy (copy D' (suc n2)) (suc n1)
                        ≡⟨ doubleCopy D' (suc n2) (suc n1) ⟩
                      copy D' ((suc n2) * (suc n1))
                        ≡⟨ cong
                             (λ x -> copy D' x)
                             (*-comm (suc n2) (suc n1)) ⟩
                      copy D' ((suc n1) * (suc n2)) ∎))))))
          (cong₂
            (λ x y -> G ∣ (copy T' (suc n2) , copy D' (suc n2)) ∣ (x , y))
            (sym
              (doubleCopy
                T
                (suc n1)
                (suc n2)))
            (sym
              (doubleCopy
                D
                (suc n1)
                (suc n2))))))
      (cong-≤-l
        (sym
          (MGA-SR†CongKeep#◆
            (hseq-exchange
              (G ∣ (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))) ∣ (copy T' (suc n2) , copy D' (suc n2)))
              (G ∣ (copy T' (suc n2) , copy D' (suc n2)) ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))))
              (exHE
                idHE)
              (PumpingLemmaGen-S-Lemma1
                (G ∣ (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))))
                (copy T' (suc n2))
                (copy D' (suc n2))
                n1
                (MGA-SR†Cong
                  (S
                    G
                    (copy T ((suc n1) * (suc n2)))
                    (copy T' ((suc n1) * (suc n2)))
                    (copy D ((suc n1) * (suc n2)))
                    (copy D' ((suc n1) * (suc n2)))
                    refl
                    refl
                    p)
                  (cong₂
                    (λ x y -> G ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (x , y))
                    (sym
                      (begin
                        copy (copy T' (suc n2)) (suc n1)
                          ≡⟨ doubleCopy T' (suc n2) (suc n1) ⟩
                        copy T' ((suc n2) * (suc n1))
                          ≡⟨ cong
                            (λ x -> copy T' x)
                              (*-comm (suc n2) (suc n1)) ⟩
                        copy T' ((suc n1) * (suc n2)) ∎))
                    (sym
                      (begin
                        copy (copy D' (suc n2)) (suc n1)
                          ≡⟨ doubleCopy D' (suc n2) (suc n1) ⟩
                        copy D' ((suc n2) * (suc n1))
                          ≡⟨ cong
                            (λ x -> copy D' x)
                              (*-comm (suc n2) (suc n1)) ⟩
                        copy D' ((suc n1) * (suc n2)) ∎))))))
              (cong₂
                (λ x y -> G ∣ (copy T' (suc n2) , copy D' (suc n2)) ∣ (x , y))
                (sym
                  (doubleCopy
                    T
                    (suc n1)
                    (suc n2)))
                (sym
                  (doubleCopy
                    D
                    (suc n1)
                    (suc n2))))))
        (≤-trans
          (PropPumpingLemmaGen-S-Lemma1
            (G ∣ (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))))
            (copy T' (suc n2))
            (copy D' (suc n2))
            n1
            (MGA-SR†Cong
              (S
                G
                (copy T ((suc n1) * (suc n2)))
                (copy T' ((suc n1) * (suc n2)))
                (copy D ((suc n1) * (suc n2)))
                (copy D' ((suc n1) * (suc n2)))
                refl
                refl
                p)
              (cong₂
                (λ x y -> G ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (x , y))
                (sym
                  (begin
                    copy (copy T' (suc n2)) (suc n1)
                      ≡⟨ doubleCopy T' (suc n2) (suc n1) ⟩
                    copy T' ((suc n2) * (suc n1))
                      ≡⟨ cong
                         (λ x -> copy T' x)
                          (*-comm (suc n2) (suc n1)) ⟩
                    copy T' ((suc n1) * (suc n2)) ∎))
                (sym
                  (begin
                    copy (copy D' (suc n2)) (suc n1)
                      ≡⟨ doubleCopy D' (suc n2) (suc n1) ⟩
                    copy D' ((suc n2) * (suc n1))
                      ≡⟨ cong
                         (λ x -> copy D' x)
                           (*-comm (suc n2) (suc n1)) ⟩
                    copy D' ((suc n1) * (suc n2)) ∎)))))
          (cong-≤-l
            (sym
              (MGA-SR†CongKeep#◆
                (S
                  G
                  (copy T ((suc n1) * (suc n2)))
                  (copy T' ((suc n1) * (suc n2)))
                  (copy D ((suc n1) * (suc n2)))
                  (copy D' ((suc n1) * (suc n2)))
                  refl
                  refl
                  p)
                (cong₂
                  (λ x y -> G ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (x , y))
                  (sym
                    (begin
                      copy (copy T' (suc n2)) (suc n1)
                        ≡⟨ doubleCopy T' (suc n2) (suc n1) ⟩
                      copy T' ((suc n2) * (suc n1))
                        ≡⟨ cong
                          (λ x -> copy T' x)
                            (*-comm (suc n2) (suc n1)) ⟩
                      copy T' ((suc n1) * (suc n2)) ∎))
                  (sym
                    (begin
                      copy (copy D' (suc n2)) (suc n1)
                        ≡⟨ doubleCopy D' (suc n2) (suc n1) ⟩
                      copy D' ((suc n2) * (suc n1))
                        ≡⟨ cong
                          (λ x -> copy D' x)
                            (*-comm (suc n2) (suc n1)) ⟩
                      copy D' ((suc n1) * (suc n2)) ∎)))))
            (k≤k (#◆ p)))))
--}}}

  PumpingLemmaGen-S-head-Lemma1 :
    (T D : ListLTerm) ->
    (n : ℕ) ->
    MGA-SR† (head (copy T (suc n) , copy D (suc n))) ->
    MGA-SR† (head (T , D))
--{{{
  PumpingLemmaGen-S-head-Lemma1 T D zero p = 
    MGA-SR†Cong
      {head ( (copy T 1) , (copy D 1))}
      p
      (cong₂
        (λ x y -> head (x , y))
        (idCopy T)
        (idCopy D))
  PumpingLemmaGen-S-head-Lemma1 T D (suc n) p =
    C-head
      T
      D
      (PumpingLemmaGen-S-Lemma1
        (head (T , D))
        T
        D
        n
        (hseq-exchange
          (head (copy T (suc n) , copy D (suc n)) ∣ (T , D))
          (head (T , D) ∣ (copy T (suc n) , copy D (suc n)))
          (exHE-head)
          (S-head
            (copy T (suc n))
            T
            (copy D (suc n))
            D
            refl
            refl
            (UnfoldMGA-SR†Copy-L-head
              T
              (union (copy D (suc n)) D)
              (suc n)
              (UnfoldMGA-SR†Copy-R-head
                (copy T (suc (suc n)))
                D
                (suc n)
                p)))))
--}}}

  PropPumpingLemmaGen-S-head-Lemma1 :
    (T D : ListLTerm) ->
    (n : ℕ) ->
    (p : MGA-SR† (head (copy T (suc n) , copy D (suc n)))) ->
    #◆ (PumpingLemmaGen-S-head-Lemma1 T D n p) ≤ #◆ p
--{{{
  PropPumpingLemmaGen-S-head-Lemma1 T D zero p =
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          p
          (cong₂
            (λ x y -> head (x , y))
            (idCopy T)
            (idCopy D))))
      (k≤k (#◆ p))
  PropPumpingLemmaGen-S-head-Lemma1 T D (suc n) p =
    ≤-trans
      (PropPumpingLemmaGen-S-Lemma1
        (head (T , D))
        T
        D
        n
        (hseq-exchange
          (head (copy T (suc n) , copy D (suc n)) ∣ (T , D))
          (head (T , D) ∣ (copy T (suc n) , copy D (suc n)))
          (exHE-head)
          (S-head
            (copy T (suc n))
            T
            (copy D (suc n))
            D
            refl
            refl
            (UnfoldMGA-SR†Copy-L-head
              T
              (union (copy D (suc n)) D)
              (suc n)
              (UnfoldMGA-SR†Copy-R-head
                (copy T (suc (suc n)))
                D
                (suc n)
                p)))))
      (cong-≤-l
        (sym
          (UnfoldMGA-SR†Copy-L-head-Keep#◆
            T
            (union (copy D (suc n)) D)
            (suc n)
            (UnfoldMGA-SR†Copy-R-head (copy T (suc (suc n))) D (suc n) p)))
        (cong-≤-l
          (sym
            (UnfoldMGA-SR†Copy-R-head-Keep#◆
              (copy T (suc (suc n)))
              D
              (suc n)
              p))
          (k≤k (#◆ p))))
--}}}

  PumpingLemmaGen-S-head-Lemma2 :
    (T T' D D' : ListLTerm) ->
    (n1 n2 : ℕ) ->
    MGA-SR† (head ((union (copy T (n1 * n2)) (copy T' (n1 * n2))) , (union (copy D (n1 * n2)) (copy D' (n1 * n2))))) ->
    MGA-SR† (head (copy T n1 , copy D n1) ∣ (copy T' n2 , copy D' n2))
--{{{
  PumpingLemmaGen-S-head-Lemma2 T T' D D' n1 zero p =
    ΔGen
      (head (copy T n1 , copy D n1))
  PumpingLemmaGen-S-head-Lemma2 T T' D D' zero (suc n2) p =
    hseq-exchange
      (head (copy T' (suc n2) , copy D' (suc n2)) ∣ ([] , []))
      (head ([] , []) ∣ (copy T' (suc n2) , copy D' (suc n2)))
      (exHE-head)
      (ΔGen
        (head (copy T' (suc n2) , copy D' (suc n2))))
  PumpingLemmaGen-S-head-Lemma2 T T' D D' (suc n1) (suc n2) p = 
    hseq-exchange
      (head (copy T' (suc n2) , copy D' (suc n2)) ∣ (copy T (suc n1) , copy D (suc n1)))
      (head (copy T (suc n1) , copy D (suc n1)) ∣ (copy T' (suc n2) , copy D' (suc n2)))
      (exHE-head)
      (PumpingLemmaGen-S-Lemma1
        (head (copy T' (suc n2) , copy D' (suc n2)))
        (copy T (suc n1))
        (copy D (suc n1))
        n2
        (MGA-SR†Cong
          {head (copy T' (suc n2) , copy D' (suc n2)) ∣ (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2)))}
          (hseq-exchange
            (head (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))) ∣ (copy T' (suc n2) , copy D' (suc n2)))
            (head (copy T' (suc n2) , copy D' (suc n2)) ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))))
            (exHE-head)
            (PumpingLemmaGen-S-Lemma1
              (head ((copy T ((suc n1) * (suc n2)), copy D ((suc n1) * (suc n2)))))
              (copy T' (suc n2))
              (copy D' (suc n2))
              n1
              (MGA-SR†Cong
                {head (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (copy T' ((suc n1) * (suc n2)) , copy D' ((suc n1) * (suc n2)))}
                (S-head
                  (copy T ((suc n1) * (suc n2)))
                  (copy T' ((suc n1) * (suc n2)))
                  (copy D ((suc n1) * (suc n2)))
                  (copy D' ((suc n1) * (suc n2)))
                  refl
                  refl
                  p)
                (cong₂
                  (λ x y -> head (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (x , y))
                  (sym
                    (begin
                      copy (copy T' (suc n2)) (suc n1)
                        ≡⟨ doubleCopy T' (suc n2) (suc n1) ⟩
                      copy T' ((suc n2) * (suc n1))
                        ≡⟨ cong
                             (λ x -> copy T' x)
                             (*-comm (suc n2) (suc n1)) ⟩
                      copy T' ((suc n1) * (suc n2)) ∎))
                  (sym
                    (begin
                      copy (copy D' (suc n2)) (suc n1)
                        ≡⟨ doubleCopy D' (suc n2) (suc n1) ⟩
                      copy D' ((suc n2) * (suc n1))
                        ≡⟨ cong
                             (λ x -> copy D' x)
                             (*-comm (suc n2) (suc n1)) ⟩
                      copy D' ((suc n1) * (suc n2)) ∎))))))
          (cong₂
            (λ x y -> head (copy T' (suc n2) , copy D' (suc n2)) ∣ (x , y))
            (sym
              (doubleCopy
                T
                (suc n1)
                (suc n2)))
            (sym
              (doubleCopy
                D
                (suc n1)
                (suc n2))))))
--}}}

  PropPumpingLemmaGen-S-head-Lemma2 :
    (T T' D D' : ListLTerm) ->
    (n1 n2 : ℕ) ->
    (p : MGA-SR† (head ((union (copy T (n1 * n2)) (copy T' (n1 * n2))) , (union (copy D (n1 * n2)) (copy D' (n1 * n2)))))) ->
    #◆ (PumpingLemmaGen-S-head-Lemma2 T T' D D' n1 n2 p) ≤ #◆ p
--{{{
  PropPumpingLemmaGen-S-head-Lemma2 T T' D D' n1 zero p =
    z≤n
  PropPumpingLemmaGen-S-head-Lemma2 T T' D D' zero (suc n2) p =
    z≤n
  PropPumpingLemmaGen-S-head-Lemma2 T T' D D' (suc n1) (suc n2) p =
    ≤-trans
      (PropPumpingLemmaGen-S-Lemma1
        (head (copy T' (suc n2) , copy D' (suc n2)))
        (copy T (suc n1))
        (copy D (suc n1))
        n2
        (MGA-SR†Cong
          (hseq-exchange
            (head (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))) ∣ (copy T' (suc n2) , copy D' (suc n2)))
            (head (copy T' (suc n2) , copy D' (suc n2)) ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))))
            exHE-head
            (PumpingLemmaGen-S-Lemma1
              (head (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))))
              (copy T' (suc n2))
              (copy D' (suc n2))
              n1
              (MGA-SR†Cong
                (S-head
                  (copy T ((suc n1) * (suc n2)))
                  (copy T' ((suc n1) * (suc n2)))
                  (copy D ((suc n1) * (suc n2)))
                  (copy D' ((suc n1) * (suc n2)))
                  refl
                  refl
                  p)
                (cong₂
                  (λ x y -> head (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (x , y))
                  (sym
                    (begin
                      copy (copy T' (suc n2)) (suc n1)
                        ≡⟨ doubleCopy T' (suc n2) (suc n1) ⟩
                      copy T' ((suc n2) * (suc n1))
                        ≡⟨ cong
                             (λ x -> copy T' x)
                             (*-comm (suc n2) (suc n1)) ⟩
                      copy T' ((suc n1) * (suc n2)) ∎))
                  (sym
                    (begin
                      copy (copy D' (suc n2)) (suc n1)
                        ≡⟨ doubleCopy D' (suc n2) (suc n1) ⟩
                      copy D' ((suc n2) * (suc n1))
                        ≡⟨ cong
                             (λ x -> copy D' x)
                             (*-comm (suc n2) (suc n1)) ⟩
                      copy D' ((suc n1) * (suc n2)) ∎))))))
          (cong₂
            (λ x y -> head (copy T' (suc n2) , copy D' (suc n2)) ∣ (x , y))
            (sym
              (doubleCopy
                T
                (suc n1)
                (suc n2)))
            (sym
              (doubleCopy
                D
                (suc n1)
                (suc n2))))))
      (cong-≤-l
        (sym
          (MGA-SR†CongKeep#◆
            (hseq-exchange
              (head (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))) ∣ (copy T' (suc n2) , copy D' (suc n2)))
              (head (copy T' (suc n2) , copy D' (suc n2)) ∣ (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))))
              exHE-head
              (PumpingLemmaGen-S-Lemma1
                (head (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))))
                (copy T' (suc n2))
                (copy D' (suc n2))
                n1
                (MGA-SR†Cong
                  (S-head
                    (copy T ((suc n1) * (suc n2)))
                    (copy T' ((suc n1) * (suc n2)))
                    (copy D ((suc n1) * (suc n2)))
                    (copy D' ((suc n1) * (suc n2)))
                    refl
                    refl
                    p)
                  (cong₂
                    (λ x y -> head (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (x , y))
                    (sym
                      (begin
                        copy (copy T' (suc n2)) (suc n1)
                          ≡⟨ doubleCopy T' (suc n2) (suc n1) ⟩
                        copy T' ((suc n2) * (suc n1))
                          ≡⟨ cong
                            (λ x -> copy T' x)
                              (*-comm (suc n2) (suc n1)) ⟩
                        copy T' ((suc n1) * (suc n2)) ∎))
                    (sym
                      (begin
                        copy (copy D' (suc n2)) (suc n1)
                          ≡⟨ doubleCopy D' (suc n2) (suc n1) ⟩
                        copy D' ((suc n2) * (suc n1))
                          ≡⟨ cong
                            (λ x -> copy D' x)
                              (*-comm (suc n2) (suc n1)) ⟩
                        copy D' ((suc n1) * (suc n2)) ∎))))))
              (cong₂
                (λ x y -> head (copy T' (suc n2) , copy D' (suc n2)) ∣ (x , y))
                (sym
                  (doubleCopy
                    T
                    (suc n1)
                    (suc n2)))
                (sym
                  (doubleCopy
                    D
                    (suc n1)
                    (suc n2))))))
        (≤-trans
          (PropPumpingLemmaGen-S-Lemma1
            (head (copy T ((suc n1) * (suc n2)) , copy D ((suc n1) * (suc n2))))
            (copy T' (suc n2))
            (copy D' (suc n2))
            n1
            (MGA-SR†Cong
              (S-head
                (copy T ((suc n1) * (suc n2)))
                (copy T' ((suc n1) * (suc n2)))
                (copy D ((suc n1) * (suc n2)))
                (copy D' ((suc n1) * (suc n2)))
                refl
                refl
                p)
              (cong₂
                (λ x y -> head (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (x , y))
                (sym
                  (begin
                    copy (copy T' (suc n2)) (suc n1)
                      ≡⟨ doubleCopy T' (suc n2) (suc n1) ⟩
                    copy T' ((suc n2) * (suc n1))
                      ≡⟨ cong
                         (λ x -> copy T' x)
                          (*-comm (suc n2) (suc n1)) ⟩
                    copy T' ((suc n1) * (suc n2)) ∎))
                (sym
                  (begin
                    copy (copy D' (suc n2)) (suc n1)
                      ≡⟨ doubleCopy D' (suc n2) (suc n1) ⟩
                    copy D' ((suc n2) * (suc n1))
                      ≡⟨ cong
                         (λ x -> copy D' x)
                           (*-comm (suc n2) (suc n1)) ⟩
                    copy D' ((suc n1) * (suc n2)) ∎)))))
          (cong-≤-l
            (sym
              (MGA-SR†CongKeep#◆
                (S-head
                  (copy T ((suc n1) * (suc n2)))
                  (copy T' ((suc n1) * (suc n2)))
                  (copy D ((suc n1) * (suc n2)))
                  (copy D' ((suc n1) * (suc n2)))
                  refl
                  refl
                  p)
                (cong₂
                  (λ x y -> head (copy T (suc (n2 + n1 * suc n2)) , copy D (suc (n2 + n1 * suc n2))) ∣ (x , y))
                  (sym
                    (begin
                      copy (copy T' (suc n2)) (suc n1)
                        ≡⟨ doubleCopy T' (suc n2) (suc n1) ⟩
                      copy T' ((suc n2) * (suc n1))
                        ≡⟨ cong
                          (λ x -> copy T' x)
                            (*-comm (suc n2) (suc n1)) ⟩
                      copy T' ((suc n1) * (suc n2)) ∎))
                  (sym
                    (begin
                      copy (copy D' (suc n2)) (suc n1)
                        ≡⟨ doubleCopy D' (suc n2) (suc n1) ⟩
                      copy D' ((suc n2) * (suc n1))
                        ≡⟨ cong
                          (λ x -> copy D' x)
                            (*-comm (suc n2) (suc n1)) ⟩
                      copy D' ((suc n1) * (suc n2)) ∎)))))
            (k≤k (#◆ p)))))
--}}}

  PumpingLemmaGen :
    (G : LHSeq) ->
    (p : MGA-SR† G) ->
    (pump : Pumping G) ->
    MGA-SR† (doPumping G pump)
--{{{
  PumpingLemmaGen .(head (T , D)) p (headPumping (T , D) zero) =
    ax
  PumpingLemmaGen .(head ([] , [])) ax (headPumping (.[] , .[]) (suc n)) =
    ax
  PumpingLemmaGen .(head (T , D)) (C-head .T .D p) (headPumping (T , D) (suc n)) =
    C-head
      (copy T (suc n))
      (copy D (suc n))
      (PumpingLemmaGen
        (head (T , D) ∣ (T , D))
        p
        (consPumping
          (head (T , D))
          (headPumping (T , D) (suc n))
          (T , D)
          (suc n)))
  PumpingLemmaGen .(head ((Γ ∷ (A , n')) , (Δ ∷ (A , n')))) (Id-rule-head Γ Δ (A , n') p) (headPumping (.(Γ ∷ (A , n')) , .(Δ ∷ (A , n'))) (suc n)) =
    Id-rule-head
      (copy Γ (suc n))
      (copy Δ (suc n))
      (A , (suc n) * n')
      (PumpingLemmaGen
        (head (Γ , Δ))
        p
        (headPumping
          (Γ , Δ)
          (suc n)))
  PumpingLemmaGen .(head ((Γ ∷ (A , n1) ∷ (A , n2)) , D)) (U-L-head Γ .D A n1 n2 refl p) (headPumping (.(Γ ∷ (A , n1) ∷ (A , n2)) , D) (suc n)) =
    U-L-head
      (copy Γ (suc n))
      (copy D (suc n))
      A
      ((suc n) * n1)
      ((suc n) * n2)
      refl
      (MGA-SR†Cong
        {head ((copy Γ (suc n)) ∷ (A , (suc n) * (n1 + n2)) , (copy D (suc n)))}
        (PumpingLemmaGen
          (head (Γ ∷ (A , n1 + n2) , D))
          p
          (headPumping
            (Γ ∷ (A , n1 + n2) , D)
            (suc n)))
        (cong
          (λ x -> head ((copy Γ (suc n)) ∷ (A , x) , copy D (suc n)))
          (c*a+b=c*a+c*b n1 n2 (suc n))))
  PumpingLemmaGen .(head (T , (Δ ∷ (A , n1) ∷ (A , n2)))) (U-R-head .T Δ A n1 n2 refl p) (headPumping (T , .(Δ ∷ (A , n1) ∷ (A , n2))) (suc n)) =
    U-R-head
      (copy T (suc n))
      (copy Δ (suc n))
      A
      ((suc n) * n1)
      ((suc n) * n2)
      refl
      ((MGA-SR†Cong
        {head ((copy T (suc n)) , (copy Δ (suc n)) ∷ (A , (suc n) * (n1 + n2)))}
        (PumpingLemmaGen
          (head (T , Δ  ∷ (A , n1 + n2)))
          p
          (headPumping
            (T , Δ  ∷ (A , n1 + n2))
            (suc n)))
        (cong
          (λ x -> head ((copy T (suc n)) , copy Δ (suc n) ∷ (A , x)))
          (c*a+b=c*a+c*b n1 n2 (suc n)))))
  PumpingLemmaGen .(head ((Γ ∷ (A , n1 + n2)) , D)) (F-L-head Γ .D A n1 n2 refl p) (headPumping (.(Γ ∷ (A , n1 + n2)) , D) (suc n)) =
    MGA-SR†Cong
      {head ((copy Γ (suc n)) ∷ (A , (suc n) * n1 + (suc n) * n2) , copy D (suc n))}
      (F-L-head
        (copy Γ (suc n))
        (copy D (suc n))
        A
        ((suc n) * n1)
        ((suc n) * n2)
        refl
        (PumpingLemmaGen
          (head (Γ ∷ (A , n1) ∷ (A , n2) , D))
          p
          (headPumping
            (Γ ∷ (A , n1) ∷ (A , n2) , D)
            (suc n))))
      (cong
        (λ x -> head ((copy Γ (suc n) ∷ (A , x)) , copy D (suc n)))
        (sym
          (c*a+b=c*a+c*b n1 n2 (suc n))))
  PumpingLemmaGen .(head (T , (Δ ∷ (A , n1 + n2)))) (F-R-head .T Δ A n1 n2 refl p) (headPumping (T , .(Δ ∷ (A , n1 + n2))) (suc n)) = 
    MGA-SR†Cong
      {head ((copy T (suc n)) , copy Δ (suc n) ∷ (A , (suc n) * n1 + (suc n) * n2))}
      (F-R-head
        (copy T (suc n))
        (copy Δ (suc n))
        A
        ((suc n) * n1)
        ((suc n) * n2)
        refl
        (PumpingLemmaGen
          (head (T , Δ ∷ (A , n1) ∷ (A , n2)))
          p
          (headPumping
            (T , Δ ∷ (A , n1) ∷ (A , n2))
            (suc n))))
      (cong
        (λ x -> head ((copy T (suc n) , copy Δ (suc n) ∷ (A , x))))
        (sym
          (c*a+b=c*a+c*b n1 n2 (suc n))))
  PumpingLemmaGen .(head ((Γ ∷ (A , 0)) , D)) (E-L-head Γ .D A p) (headPumping (.(Γ ∷ (A , 0)) , D) (suc n)) =
    MGA-SR†Cong
      {head (copy Γ (suc n) ∷ (A , 0) , copy D (suc n))}
      (E-L-head
        (copy Γ (suc n))
        (copy D (suc n))
        A
        (PumpingLemmaGen
          (head (Γ , D))
          p
          (headPumping
            (Γ , D)
            (suc n))))
      (cong
        (λ x -> head ((copy Γ (suc n) ∷ (A , x)) , copy D (suc n)))
        (sym
          (a*0=0 n)))
  PumpingLemmaGen .(head (T , (Δ ∷ (A , 0)))) (E-R-head .T Δ A p) (headPumping (T , .(Δ ∷ (A , 0))) (suc n)) = 
    MGA-SR†Cong
      {head (copy T (suc n) , copy Δ (suc n) ∷ (A , 0))}
      (E-R-head
        (copy T (suc n))
        (copy Δ (suc n))
        A
        (PumpingLemmaGen
          (head (T , Δ))
          p
          (headPumping
            (T , Δ)
            (suc n))))
      (cong
        (λ x -> head (copy T (suc n) , copy Δ (suc n) ∷ (A , x)))
        (sym
          (a*0=0 n)))
  PumpingLemmaGen .(head ((Γ ∷ (A +S B , n₁)) , D)) (plus-L-head Γ .D A B n₁ p) (headPumping (.(Γ ∷ (A +S B , n₁)) , D) (suc n)) =
    plus-L-head
      (copy Γ (suc n))
      (copy D (suc n))
      A
      B
      ((suc n) * n₁)
      (PumpingLemmaGen
        (head (Γ ∷ (A , n₁) ∷ (B , n₁) , D))
        p
        (headPumping
          (Γ ∷ (A , n₁) ∷ (B , n₁) , D)
          (suc n)))
  PumpingLemmaGen .(head ((Γ ∷ (-S A , n₁)) , D)) (minus-L-head Γ .D A n₁ p) (headPumping (.(Γ ∷ (-S A , n₁)) , D) (suc n)) =
    minus-L-head
      (copy Γ (suc n))
      (copy D (suc n))
      A
      ((suc n) * n₁)
      (PumpingLemmaGen
        (head (Γ , D ∷ (A , n₁)))
        p
        (headPumping
          (Γ , D ∷ (A , n₁))
          (suc n)))
  PumpingLemmaGen .(head ((Γ ∷ (botAG , n₁)) , D)) (Z-L-head Γ .D n₁ p) (headPumping (.(Γ ∷ (botAG , n₁)) , D) (suc n)) =
    Z-L-head
      (copy Γ (suc n))
      (copy D (suc n))
      ((suc n) * n₁)
      (PumpingLemmaGen
        (head (Γ , D))
        p
        (headPumping
          (Γ , D)
          (suc n)))
  PumpingLemmaGen .(head (T , (Δ ∷ (A +S B , n₁)))) (plus-R-head .T Δ A B n₁ p) (headPumping (T , .(Δ ∷ (A +S B , n₁))) (suc n)) = 
    plus-R-head
      (copy T (suc n))
      (copy Δ (suc n))
      A
      B
      ((suc n) * n₁)
      (PumpingLemmaGen
        (head (T , Δ ∷ (A , n₁) ∷ (B , n₁)))
        p
        (headPumping
          (T , Δ ∷ (A , n₁) ∷ (B , n₁))
          (suc n)))
  PumpingLemmaGen .(head (T , (Δ ∷ (-S A , n₁)))) (minus-R-head .T Δ A n₁ p) (headPumping (T , .(Δ ∷ (-S A , n₁))) (suc n)) = 
    minus-R-head
      (copy T (suc n))
      (copy Δ (suc n))
      A
      ((suc n) * n₁)
      (PumpingLemmaGen
        (head (T ∷ (A , n₁) , Δ))
        p
        (headPumping
          (T ∷ (A , n₁) , Δ)
          (suc n)))
  PumpingLemmaGen .(head (T , (Δ ∷ (botAG , n₁)))) (Z-R-head .T Δ n₁ p) (headPumping (T , .(Δ ∷ (botAG , n₁))) (suc n)) = 
    Z-R-head
      (copy T (suc n))
      (copy Δ (suc n))
      ((suc n) * n₁)
      (PumpingLemmaGen
        (head (T , Δ))
        p
        (headPumping
          (T , Δ)
          (suc n)))
  PumpingLemmaGen .(head ((Γ ∷ (A ⊔S B , n₁)) , D)) (max-L-head Γ .D A B n₁ p p₁) (headPumping (.(Γ ∷ (A ⊔S B , n₁)) , D) (suc n)) =
    max-L-head
      (copy Γ (suc n))
      (copy D (suc n))
      A
      B
      ((suc n) * n₁)
      (PumpingLemmaGen
        (head (Γ ∷ (A , n₁) , D))
        p
        (headPumping
          (Γ ∷ (A , n₁) , D)
          (suc n)))
      (PumpingLemmaGen
        (head (Γ ∷ (B , n₁) , D))
        p₁
        (headPumping
          (Γ ∷ (B , n₁) , D)
          (suc n)))
  PumpingLemmaGen .(head (Γ , (D ∷ (A ⊓S B , n₁)))) (min-R-head .Γ D A B n₁ p p₁) (headPumping (Γ , .(D ∷ (A ⊓S B , n₁))) (suc n)) =
    min-R-head
      (copy Γ (suc n))
      (copy D (suc n))
      A
      B
      ((suc n) * n₁)
      (PumpingLemmaGen
        (head (Γ , D ∷ (A , n₁)))
        p
        (headPumping
          (Γ , D ∷ (A , n₁))
          (suc n)))
      (PumpingLemmaGen
        (head (Γ , D ∷ (B , n₁)))
        p₁
        (headPumping
          (Γ , D ∷ (B , n₁))
          (suc n)))
  PumpingLemmaGen .(head (T , (Δ ∷ (A ⊔S B , n₁)))) (max-R-head .T Δ A B n₁ p) (headPumping (T , .(Δ ∷ (A ⊔S B , n₁))) (suc n)) =
    max-R-head
      (copy T (suc n))
      (copy Δ (suc n))
      A
      B
      (suc n * n₁)
      (PumpingLemmaGen
        (head (T , Δ ∷ (A , n₁)) ∣ (T , Δ ∷ (B , n₁)))
        p
        (consPumping
          (head (T , Δ ∷ (A , n₁)))
          (headPumping
            (T , Δ ∷ (A , n₁))
            (suc n))
          (T , Δ ∷ (B , n₁))
          (suc n)))
  PumpingLemmaGen .(head ((T ∷ (A ⊓S B , n₁)) , Δ)) (min-L-head T .Δ A B n₁ p) (headPumping (.(T ∷ (A ⊓S B , n₁)) , Δ) (suc n)) =
    min-L-head
      (copy T (suc n))
      (copy Δ (suc n))
      A
      B
      (suc n * n₁)
      (PumpingLemmaGen
        (head (T ∷ (A , n₁) , Δ) ∣ (T ∷ (B , n₁) , Δ))
        p
        (consPumping
          (head (T ∷ (A , n₁) , Δ))
          (headPumping
            (T ∷ (A , n₁) , Δ)
            (suc n))
          (T ∷ (B , n₁) , Δ)
          (suc n)))
  PumpingLemmaGen (head (T , D ∷ (one , .(suc k)))) (◆1-rule .T .D ◆T ◆D refl refl k p) (headPumping (.T , .D ∷ (one , .(suc k))) (suc n)) =
    ◆1-rule
      (copy T (suc n))
      (copy D (suc n))
      (copyKeep◆ ◆T (suc n))
      (copyKeep◆ ◆D (suc n))
      refl
      refl
      (k + n * (suc k))
      (MGA-SR†Cong
        {head (copy (remove◆ ◆T) (suc n) , copy (remove◆ ◆D) (suc n) ∷ (one , (suc n) * (suc k)))}
        (PumpingLemmaGen (head (remove◆ ◆T , remove◆ ◆D ∷ (one , (suc k)))) p (headPumping (remove◆ ◆T , remove◆ ◆D ∷ (one , (suc k))) (suc n)))
        (cong₂
          (λ x y -> head (x , y ∷ (one , (suc n) * (suc k))))
          (copyRemove ◆T (suc n))
          ((copyRemove ◆D (suc n)))))
  PumpingLemmaGen (head (T , D)) (◆-rule .T .D ◆T ◆D refl refl p) (headPumping (.T , .D) (suc n)) =
    ◆-rule
      (copy T (suc n))
      (copy D (suc n))
      (copyKeep◆ ◆T (suc n))
      (copyKeep◆ ◆D (suc n))
      refl
      refl
      (MGA-SR†Cong
        {head (copy (remove◆ ◆T) (suc n) , copy (remove◆ ◆D) (suc n))}
        (PumpingLemmaGen (head (remove◆ ◆T , remove◆ ◆D)) p (headPumping (remove◆ ◆T , remove◆ ◆D) (suc n)))
        (cong₂
          (λ x y -> head (x , y))
          (copyRemove ◆T (suc n))
          ((copyRemove ◆D (suc n)))))
  PumpingLemmaGen .(head (T , D)) (seq-exchange-head Γ .T Δ .D x x₁ p) (headPumping (T , D) (suc n)) =
    seq-exchange-head
      (copy Γ (suc n))
      (copy T (suc n))
      (copy Δ (suc n))
      (copy D (suc n))
      (copyKeepExchange Γ T x (suc n))
      (copyKeepExchange Δ D x₁ (suc n))
      (PumpingLemmaGen (head (Γ , Δ)) p (headPumping (Γ , Δ) (suc n)))
  PumpingLemmaGen .(head (T , D)) (hseq-exchange G .(head (T , D)) x p) (headPumping (T , D) (suc n)) =
    hseq-exchange
      (doPumping G (pumpExchange (head (T , D)) G (headPumping (T , D) (suc n)) (LHSeqExchangeSym x)))
      (head (copy T (suc n) , copy D (suc n)))
      (LHSeqExchangeSym
        (doPumpingExchange
          (head (T , D))
          G
          (headPumping (T , D) (suc n))
          (LHSeqExchangeSym x)))
      (PumpingLemmaGen
        G
        p
        (pumpExchange (head (T , D)) G (headPumping (T , D) (suc n)) (LHSeqExchangeSym x)))
  PumpingLemmaGen .(G ∣ (T , D)) p (consPumping G pump (T , D) zero) =
    ΔGen
      (doPumping G pump)
  PumpingLemmaGen .(G ∣ (Γ1 , Δ1) ∣ (_ , _)) (W G Γ1 _ Δ1 _ p) (consPumping .(G ∣ (Γ1 , Δ1)) (consPumping .G pump .(Γ1 , Δ1) n₁) (Γ2 , Δ2) (suc n)) =
    W
      (doPumping G pump)
      (copy Γ1 n₁)
      (copy Γ2 (suc n))
      (copy Δ1 n₁)
      (copy Δ2 (suc n))
      (PumpingLemmaGen
        (G ∣ (Γ1 , Δ1))
        p
        (consPumping
          G
          pump
          (Γ1 , Δ1)
          n₁))
  PumpingLemmaGen .(G ∣ (T , D)) (C .G .T .D p) (consPumping G pump (T , D) (suc n)) = 
    C
      (doPumping G pump)
      (copy T (suc n))
      (copy D (suc n))
      (PumpingLemmaGen
        (G ∣ (T , D) ∣ (T , D))
        p
        (consPumping
          (G ∣ (T , D))
          (consPumping
            G
            pump
            (T , D)
            (suc n))
          (T , D)
          (suc n)))
  PumpingLemmaGen .(G ∣ (Γ1 , Δ1) ∣ (_ , _)) (S G Γ1 _ Δ1 _ refl refl p) (consPumping .(G ∣ (Γ1 , Δ1)) (consPumping .G pump .(Γ1 , Δ1) n₁) (T , D) (suc n)) =
    PumpingLemmaGen-S-Lemma2
      (doPumping G pump)
      Γ1
      T
      Δ1
      D
      n₁
      (suc n)
      (MGA-SR†Cong
        {doPumping G pump ∣ (copy (union Γ1 T) (n₁ * suc n) , copy (union Δ1 D) (n₁ * (suc n)))}
        (PumpingLemmaGen
          (G ∣ (union Γ1 T , union Δ1 D))
          p
          (consPumping
            G
            pump
            (union Γ1 T , union Δ1 D)
            (n₁ * (suc n))))
        (cong₂
          (λ x y -> (doPumping G pump ∣ (x , y)))
          (copyUnion Γ1 T (n₁ * suc n))
          (copyUnion Δ1 D (n₁ * suc n))))
  PumpingLemmaGen .(G ∣ ((Γ ∷ (A , n')) , (Δ ∷ (A , n')))) (Id-rule .G Γ Δ (A , n') p) (consPumping G pump (.(Γ ∷ (A , n')) , .(Δ ∷ (A , n'))) (suc n)) = 
    Id-rule
      (doPumping G pump)
      (copy Γ (suc n))
      (copy Δ (suc n))
      (A , (suc n) * n')
      (PumpingLemmaGen
        (G ∣ (Γ , Δ))
        p
        (consPumping
          G
          pump
          (Γ , Δ)
          (suc n)))
  PumpingLemmaGen .(head (Γ1 , Δ1) ∣ (_ , _)) (W-head Γ1 _ Δ1 _ p) (consPumping .(head (Γ1 , Δ1)) (headPumping .(Γ1 , Δ1) n₁) (T , D) (suc n)) =
    W-head
      (copy Γ1 n₁)
      (copy T (suc n))
      (copy Δ1 n₁)
      (copy D (suc n))
      (PumpingLemmaGen
        (head (Γ1 , Δ1))
        p
        (headPumping (Γ1 , Δ1) n₁))
  PumpingLemmaGen .(head (Γ1 , Δ1) ∣ (T , D)) (S-head Γ1 .T Δ1 .D refl refl p) (consPumping .(head (Γ1 , Δ1)) (headPumping (Γ1 , Δ1) n₁) (T , D) (suc n)) =
    PumpingLemmaGen-S-head-Lemma2
      Γ1
      T
      Δ1
      D
      n₁
      (suc n)
      (MGA-SR†Cong
        {head (copy (union Γ1 T) (n₁ * suc n) , copy (union Δ1 D) (n₁ * (suc n)))}
        (PumpingLemmaGen
          (head (union Γ1 T , union Δ1 D))
          p
          (headPumping
            (union Γ1 T , union Δ1 D)
            (n₁ * (suc n))))
        (cong₂
          (λ x y -> (head (x , y)))
          (copyUnion Γ1 T (n₁ * suc n))
          (copyUnion Δ1 D (n₁ * suc n))))
  PumpingLemmaGen .(G ∣ ((Γ ∷ (A , n1) ∷ (A , n2)) , D)) (U-L .G Γ .D A n1 n2 refl p) (consPumping G pump (.(Γ ∷ (A , n1) ∷ (A , n2)) , D) (suc n)) = 
    U-L
      (doPumping G pump)
      (copy Γ (suc n))
      (copy D (suc n))
      A
      ((suc n) * n1)
      ((suc n) * n2)
      refl
      (MGA-SR†Cong
        {(doPumping G pump) ∣ ((copy Γ (suc n)) ∷ (A , (suc n) * (n1 + n2)) , (copy D (suc n)))}
        (PumpingLemmaGen
          (G ∣ (Γ ∷ (A , n1 + n2) , D))
          p
          (consPumping
            G
            pump
            (Γ ∷ (A , n1 + n2) , D)
            (suc n)))
        (cong
          (λ x -> (doPumping G pump) ∣ ((copy Γ (suc n)) ∷ (A , x) , copy D (suc n)))
          (c*a+b=c*a+c*b n1 n2 (suc n))))
  PumpingLemmaGen .(G ∣ (T , (Δ ∷ (A , n1) ∷ (A , n2)))) (U-R .G .T Δ A n1 n2 refl p) (consPumping G pump (T , .(Δ ∷ (A , n1) ∷ (A , n2))) (suc n)) = 
    U-R
      (doPumping G pump)
      (copy T (suc n))
      (copy Δ (suc n))
      A
      ((suc n) * n1)
      ((suc n) * n2)
      refl
      ((MGA-SR†Cong
        {(doPumping G pump) ∣ ((copy T (suc n)) , (copy Δ (suc n)) ∷ (A , (suc n) * (n1 + n2)))}
        (PumpingLemmaGen
          (G ∣ (T , Δ  ∷ (A , n1 + n2)))
          p
          (consPumping
            G
            pump
            (T , Δ  ∷ (A , n1 + n2))
            (suc n)))
        (cong
          (λ x -> (doPumping G pump) ∣ ((copy T (suc n)) , copy Δ (suc n) ∷ (A , x)))
          (c*a+b=c*a+c*b n1 n2 (suc n)))))
  PumpingLemmaGen .(G ∣ ((Γ ∷ (A , n1 + n2)) , D)) (F-L .G Γ .D A n1 n2 refl p) (consPumping G pump (.(Γ ∷ (A , n1 + n2)) , D) (suc n)) = 
    MGA-SR†Cong
      {(doPumping G pump) ∣ ((copy Γ (suc n)) ∷ (A , (suc n) * n1 + (suc n) * n2) , copy D (suc n))}
      (F-L
        (doPumping G pump)
        (copy Γ (suc n))
        (copy D (suc n))
        A
        ((suc n) * n1)
        ((suc n) * n2)
        refl
        (PumpingLemmaGen
          (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , D))
          p
          (consPumping
            G
            pump
            (Γ ∷ (A , n1) ∷ (A , n2) , D)
            (suc n))))
      (cong
        (λ x -> (doPumping G pump) ∣ ((copy Γ (suc n) ∷ (A , x)) , copy D (suc n)))
        (sym
          (c*a+b=c*a+c*b n1 n2 (suc n))))
  PumpingLemmaGen .(G ∣ (T , (Δ ∷ (A , n1 + n2)))) (F-R .G .T Δ A n1 n2 refl p) (consPumping G pump (T , .(Δ ∷ (A , n1 + n2))) (suc n)) =  
    MGA-SR†Cong
      {(doPumping G pump) ∣ ((copy T (suc n)) , copy Δ (suc n) ∷ (A , (suc n) * n1 + (suc n) * n2))}
      (F-R
        (doPumping G pump)
        (copy T (suc n))
        (copy Δ (suc n))
        A
        ((suc n) * n1)
        ((suc n) * n2)
        refl
        (PumpingLemmaGen
          (G ∣ (T , Δ ∷ (A , n1) ∷ (A , n2)))
          p
          (consPumping
            G
            pump
            (T , Δ ∷ (A , n1) ∷ (A , n2))
            (suc n))))
      (cong
        (λ x -> (doPumping G pump) ∣ ((copy T (suc n) , copy Δ (suc n) ∷ (A , x))))
        (sym
          (c*a+b=c*a+c*b n1 n2 (suc n))))
  PumpingLemmaGen .(G ∣ ((Γ ∷ (A , 0)) , D)) (E-L .G Γ .D A p) (consPumping G pump (.(Γ ∷ (A , 0)) , D) (suc n)) = 
    MGA-SR†Cong
      {(doPumping G pump) ∣ (copy Γ (suc n) ∷ (A , 0) , copy D (suc n))}
      (E-L
        (doPumping G pump)
        (copy Γ (suc n))
        (copy D (suc n))
        A
        (PumpingLemmaGen
          (G ∣ (Γ , D))
          p
          (consPumping
            G
            pump
            (Γ , D)
            (suc n))))
      (cong
        (λ x -> (doPumping G pump) ∣ ((copy Γ (suc n) ∷ (A , x)) , copy D (suc n)))
        (sym
          (a*0=0 n)))
  PumpingLemmaGen .(G ∣ (T , (Δ ∷ (A , 0)))) (E-R .G .T Δ A p) (consPumping G pump (T , .(Δ ∷ (A , 0))) (suc n)) = 
    MGA-SR†Cong
      {(doPumping G pump) ∣ (copy T (suc n) , copy Δ (suc n) ∷ (A , 0))}
      (E-R
        (doPumping G pump)
        (copy T (suc n))
        (copy Δ (suc n))
        A
        (PumpingLemmaGen
          (G ∣ (T , Δ))
          p
          (consPumping
            G
            pump
            (T , Δ)
            (suc n))))
      (cong
        (λ x -> (doPumping G pump) ∣ (copy T (suc n) , copy Δ (suc n) ∷ (A , x)))
        (sym
          (a*0=0 n)))
  PumpingLemmaGen .(G ∣ ((Γ ∷ (A +S B , n₁)) , D)) (plus-L .G Γ .D A B n₁ p) (consPumping G pump (.(Γ ∷ (A +S B , n₁)) , D) (suc n)) = 
    plus-L
      (doPumping G pump)
      (copy Γ (suc n))
      (copy D (suc n))
      A
      B
      ((suc n) * n₁)
      (PumpingLemmaGen
        (G ∣ (Γ ∷ (A , n₁) ∷ (B , n₁) , D))
        p
        (consPumping
          G
          pump
          (Γ ∷ (A , n₁) ∷ (B , n₁) , D)
          (suc n)))
  PumpingLemmaGen .(G ∣ ((Γ ∷ (-S A , n₁)) , D)) (minus-L .G Γ .D A n₁ p) (consPumping G pump (.(Γ ∷ (-S A , n₁)) , D) (suc n)) = 
    minus-L
      (doPumping G pump)
      (copy Γ (suc n))
      (copy D (suc n))
      A
      ((suc n) * n₁)
      (PumpingLemmaGen
        (G ∣ (Γ , D ∷ (A , n₁)))
        p
        (consPumping
          G
          pump
          (Γ , D ∷ (A , n₁))
          (suc n)))
  PumpingLemmaGen .(G ∣ ((Γ ∷ (botAG , n₁)) , D)) (Z-L .G Γ .D n₁ p) (consPumping G pump (.(Γ ∷ (botAG , n₁)) , D) (suc n)) = 
    Z-L
      (doPumping G pump)
      (copy Γ (suc n))
      (copy D (suc n))
      ((suc n) * n₁)
      (PumpingLemmaGen
        (G ∣ (Γ , D))
        p
        (consPumping
          G
          pump
          (Γ , D)
          (suc n)))
  PumpingLemmaGen .(G ∣ (T , (Δ ∷ (A +S B , n₁)))) (plus-R .G .T Δ A B n₁ p) (consPumping G pump (T , .(Δ ∷ (A +S B , n₁))) (suc n)) = 
    plus-R
      (doPumping G pump)
      (copy T (suc n))
      (copy Δ (suc n))
      A
      B
      ((suc n) * n₁)
      (PumpingLemmaGen
        (G ∣ (T , Δ ∷ (A , n₁) ∷ (B , n₁)))
        p
        (consPumping
          G
          pump
          (T , Δ ∷ (A , n₁) ∷ (B , n₁))
          (suc n)))
  PumpingLemmaGen .(G ∣ (T , (Δ ∷ (-S A , n₁)))) (minus-R .G .T Δ A n₁ p) (consPumping G pump (T , .(Δ ∷ (-S A , n₁))) (suc n)) = 
    minus-R
      (doPumping G pump)
      (copy T (suc n))
      (copy Δ (suc n))
      A
      ((suc n) * n₁)
      (PumpingLemmaGen
        (G ∣ (T ∷ (A , n₁) , Δ))
        p
        (consPumping
          G
          pump
          (T ∷ (A , n₁) , Δ)
          (suc n)))
  PumpingLemmaGen .(G ∣ (T , (Δ ∷ (botAG , n₁)))) (Z-R .G .T Δ n₁ p) (consPumping G pump (T , .(Δ ∷ (botAG , n₁))) (suc n)) = 
    Z-R
      (doPumping G pump)
      (copy T (suc n))
      (copy Δ (suc n))
      ((suc n) * n₁)
      (PumpingLemmaGen
        (G ∣ (T , Δ))
        p
        (consPumping
          G
          pump
          (T , Δ)
          (suc n)))
  PumpingLemmaGen .(G ∣ ((Γ ∷ (A ⊔S B , n₁)) , D)) (max-L .G Γ .D A B n₁ p p₁) (consPumping G pump (.(Γ ∷ (A ⊔S B , n₁)) , D) (suc n)) = 
    max-L
      (doPumping G pump)
      (copy Γ (suc n))
      (copy D (suc n))
      A
      B
      ((suc n) * n₁)
      (PumpingLemmaGen
        (G ∣ (Γ ∷ (A , n₁) , D))
        p
        (consPumping
          G
          pump
          (Γ ∷ (A , n₁) , D)
          (suc n)))
      (PumpingLemmaGen
        (G ∣ (Γ ∷ (B , n₁) , D))
        p₁
        (consPumping
          G
          pump
          (Γ ∷ (B , n₁) , D)
          (suc n)))
  PumpingLemmaGen .(G ∣ (Γ , (D ∷ (A ⊓S B , n₁)))) (min-R .G .Γ D A B n₁ p p₁) (consPumping G pump (Γ , .(D ∷ (A ⊓S B , n₁))) (suc n)) = 
    min-R
      (doPumping G pump)
      (copy Γ (suc n))
      (copy D (suc n))
      A
      B
      ((suc n) * n₁)
      (PumpingLemmaGen
        (G ∣ (Γ , D ∷ (A , n₁)))
        p
        (consPumping
          G
          pump
          (Γ , D ∷ (A , n₁))
          (suc n)))
      (PumpingLemmaGen
        (G ∣ (Γ , D ∷ (B , n₁)))
        p₁
        (consPumping
          G
          pump
          (Γ , D ∷ (B , n₁))
          (suc n)))
  PumpingLemmaGen .(G ∣ (T , (Δ ∷ (A ⊔S B , n₁)))) (max-R .G .T Δ A B n₁ p) (consPumping G pump (T , .(Δ ∷ (A ⊔S B , n₁))) (suc n)) = 
    max-R
      (doPumping G pump)
      (copy T (suc n))
      (copy Δ (suc n))
      A
      B
      (suc n * n₁)
      (PumpingLemmaGen
        (G ∣ (T , Δ ∷ (A , n₁)) ∣ (T , Δ ∷ (B , n₁)))
        p
        (consPumping
          (G ∣ (T , Δ ∷ (A , n₁)))
          (consPumping
            G
            pump
            (T , Δ ∷ (A , n₁))
            (suc n))
          (T , Δ ∷ (B , n₁))
          (suc n)))
  PumpingLemmaGen .(G ∣ ((T ∷ (A ⊓S B , n₁)) , Δ)) (min-L .G T .Δ A B n₁ p) (consPumping G pump (.(T ∷ (A ⊓S B , n₁)) , Δ) (suc n)) = 
    min-L
      (doPumping G pump)
      (copy T (suc n))
      (copy Δ (suc n))
      A
      B
      (suc n * n₁)
      (PumpingLemmaGen
        (G ∣ (T ∷ (A , n₁) , Δ) ∣ (T ∷ (B , n₁) , Δ))
        p
        (consPumping
          (G ∣ (T ∷ (A , n₁) , Δ))
          (consPumping
            G
            pump
            (T ∷ (A , n₁) , Δ)
            (suc n))
          (T ∷ (B , n₁) , Δ)
          (suc n)))
  PumpingLemmaGen .(G ∣ (T , D)) (seq-exchange .G Γ .T Δ .D x x₁ p) (consPumping G pump (T , D) (suc n)) = 
    seq-exchange
      (doPumping G pump)
      (copy Γ (suc n))
      (copy T (suc n))
      (copy Δ (suc n))
      (copy D (suc n))
      (copyKeepExchange Γ T x (suc n))
      (copyKeepExchange Δ D x₁ (suc n))
      (PumpingLemmaGen ( G ∣ (Γ , Δ)) p
        (consPumping G pump (Γ , Δ) (suc n)))
  PumpingLemmaGen .(G ∣ (T , D)) (hseq-exchange G₁ .(G ∣ (T , D)) x p) (consPumping G pump (T , D) (suc n)) = 
    hseq-exchange
      (doPumping G₁ (pumpExchange (G ∣ (T , D)) G₁ (consPumping G pump (T , D) (suc n)) (LHSeqExchangeSym x)))
      (doPumping (G ∣ (T , D)) (consPumping G pump (T , D) (suc n)))
      (LHSeqExchangeSym
        (doPumpingExchange
          (G ∣ (T , D))
          G₁
          (consPumping G pump (T , D) (suc n))
          (LHSeqExchangeSym x)))
      (PumpingLemmaGen
        G₁
        p
        (pumpExchange (G ∣ (T , D)) G₁ (consPumping G pump (T , D) (suc n)) (LHSeqExchangeSym x)))
  PumpingLemmaGen (head .(T , D ∷ (one , k))) (1-rule-head T D k p) (headPumping (.T , .(D ∷ (one , k))) (suc n)) =
    1-rule-head
      (copy T (suc n))
      (copy D (suc n))
      (k + n * k)
      (PumpingLemmaGen
        (head (T , D))
        p
        (headPumping (T , D) (suc n)))
  PumpingLemmaGen .(G ∣ (T , D ∷ (one , k))) (1-rule G T D k p) (consPumping .G pump .(T , D ∷ (one , k)) (suc n)) =
    1-rule
      (doPumping G pump)
      (copy T (suc n))
      (copy D (suc n))
      (k + n * k)
      (PumpingLemmaGen
        (G ∣ (T , D))
        p
        (consPumping G pump (T , D) (suc n)))
  PumpingLemmaGen .(G ∣ (T , D)) (can-rule G T D (A , k') p) (consPumping .G pump .(T , D) (suc n)) =
    can-rule
      (doPumping G pump)
      (copy T (suc n))
      (copy D (suc n))
      (A , (suc n) * k')
      (PumpingLemmaGen
        (G ∣ (T ∷ (A , k') , D ∷ (A , k')))
        p
        (consPumping
          G
          pump
          (T ∷ (A , k') , D ∷ (A , k'))
          (suc n)))
  PumpingLemmaGen .(head (T , D)) (can-rule-head T D (A , k') p) (headPumping .(T , D) (suc n)) =
    can-rule-head
      (copy T (suc n))
      (copy D (suc n))
      (A , (suc n) * k')
      (PumpingLemmaGen
        (head (T ∷ (A , k') , D ∷ (A , k')))
        p
        (headPumping
          (T ∷ (A , k') , D ∷ (A , k'))
          (suc n)))
--}}}

  PropPumpingLemmaGen :
    (G : LHSeq) ->
    (p : MGA-SR† G) ->
    (pump : Pumping G) ->
    #◆ (PumpingLemmaGen G p pump) ≤ #◆ p
--{{{
  PropPumpingLemmaGen .(head (T , D)) p (headPumping (T , D) zero) =
    z≤n
  PropPumpingLemmaGen .(head ([] , [])) ax (headPumping (.[] , .[]) (suc n)) =
    z≤n
  PropPumpingLemmaGen .(head (T , D)) (C-head .T .D p) (headPumping (T , D) (suc n)) =
    PropPumpingLemmaGen
      (head (T , D) ∣ (T , D))
      p
      (consPumping (head (T , D)) (headPumping (T , D) (suc n)) (T , D) (suc n))
  PropPumpingLemmaGen .(head ((Γ ∷ (A , n')) , (Δ ∷ (A , n')))) (Id-rule-head Γ Δ (A , n') p) (headPumping (.(Γ ∷ (A , n')) , .(Δ ∷ (A , n'))) (suc n)) =
    PropPumpingLemmaGen
      (head (Γ , Δ))
      p
      (headPumping (Γ , Δ) (suc n))
  PropPumpingLemmaGen .(head ((Γ ∷ (A , n1) ∷ (A , n2)) , D)) (U-L-head Γ .D A n1 n2 refl p) (headPumping (.(Γ ∷ (A , n1) ∷ (A , n2)) , D) (suc n)) = 
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          (PumpingLemmaGen
            (head (Γ ∷ (A , n1 + n2) , D))
            p
            (headPumping
              (Γ ∷ (A , n1 + n2) , D)
              (suc n)))
          (cong
            (λ x -> head ((copy Γ (suc n)) ∷ (A , x) , copy D (suc n)))
            (c*a+b=c*a+c*b n1 n2 (suc n)))))
      (PropPumpingLemmaGen
        (head ((Γ ∷ (A , n1 + n2)) , D))
        p
        (headPumping ((Γ ∷ (A , n1 + n2)) , D) (suc n)))
  PropPumpingLemmaGen .(head (T , (Δ ∷ (A , n1) ∷ (A , n2)))) (U-R-head .T Δ A n1 n2 refl p) (headPumping (T , .(Δ ∷ (A , n1) ∷ (A , n2))) (suc n)) =
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          (PumpingLemmaGen
            (head (T , Δ  ∷ (A , n1 + n2)))
            p
            (headPumping
              (T , Δ  ∷ (A , n1 + n2))
              (suc n)))
          (cong
            (λ x -> head ((copy T (suc n)) , copy Δ (suc n) ∷ (A , x)))
            (c*a+b=c*a+c*b n1 n2 (suc n)))))
      (PropPumpingLemmaGen
        (head (T , Δ ∷ (A , n1 + n2)))
        p
        (headPumping (T , Δ ∷ (A , n1 + n2)) (suc n)))
  PropPumpingLemmaGen .(head ((Γ ∷ (A , n1 + n2)) , D)) (F-L-head Γ .D A n1 n2 refl p) (headPumping (.(Γ ∷ (A , n1 + n2)) , D) (suc n)) = 
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          (F-L-head
            (copy Γ (suc n))
            (copy D (suc n))
            A
            ((suc n) * n1)
            ((suc n) * n2)
            refl
            (PumpingLemmaGen
              (head (Γ ∷ (A , n1) ∷ (A , n2) , D))
              p
              (headPumping
                (Γ ∷ (A , n1) ∷ (A , n2) , D)
                (suc n))))
          (cong
            (λ x -> head ((copy Γ (suc n) ∷ (A , x)) , copy D (suc n)))
            (sym
              (c*a+b=c*a+c*b n1 n2 (suc n))))))
      (PropPumpingLemmaGen
        (head (Γ ∷ (A , n1) ∷ (A , n2) , D))
        p
        (headPumping (Γ ∷ (A , n1) ∷ (A , n2) , D) (suc n)))
  PropPumpingLemmaGen .(head (T , (Δ ∷ (A , n1 + n2)))) (F-R-head .T Δ A n1 n2 refl p) (headPumping (T , .(Δ ∷ (A , n1 + n2))) (suc n)) =
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          (F-R-head
            (copy T (suc n))
            (copy Δ (suc n))
            A
            ((suc n) * n1)
            ((suc n) * n2)
            refl
            (PumpingLemmaGen
              (head (T , Δ ∷ (A , n1) ∷ (A , n2)))
              p
              (headPumping
                (T , Δ ∷ (A , n1) ∷ (A , n2))
                (suc n))))
          (cong
            (λ x -> head ((copy T (suc n) , copy Δ (suc n) ∷ (A , x))))
            (sym
              (c*a+b=c*a+c*b n1 n2 (suc n))))))
      (PropPumpingLemmaGen
        (head (T , Δ ∷ (A , n1) ∷ (A , n2)))
        p
        (headPumping (T , (Δ ∷ (A , n1) ∷ (A , n2))) (suc n)))
  PropPumpingLemmaGen .(head ((Γ ∷ (A , 0)) , D)) (E-L-head Γ .D A p) (headPumping (.(Γ ∷ (A , 0)) , D) (suc n)) =
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          (E-L-head
            (copy Γ (suc n))
            (copy D (suc n))
            A
            (PumpingLemmaGen
              (head (Γ , D))
              p
              (headPumping
                (Γ , D)
                (suc n))))
          (cong
            (λ x -> head ((copy Γ (suc n) ∷ (A , x)) , copy D (suc n)))
            (sym
              (a*0=0 n)))))
      (PropPumpingLemmaGen
        ((head (Γ , D)))
        p
        (headPumping (Γ , D) (suc n)))
  PropPumpingLemmaGen .(head (T , (Δ ∷ (A , 0)))) (E-R-head .T Δ A p) (headPumping (T , .(Δ ∷ (A , 0))) (suc n)) = 
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          (E-R-head
            (copy T (suc n))
            (copy Δ (suc n))
            A
            (PumpingLemmaGen
              (head (T , Δ))
              p
              (headPumping
                (T , Δ)
                (suc n))))
          (cong
            (λ x -> head (copy T (suc n) , (copy Δ (suc n) ∷ (A , x))))
            (sym
              (a*0=0 n)))))
      (PropPumpingLemmaGen
        ((head (T , Δ)))
        p
        (headPumping (T , Δ) (suc n)))
  PropPumpingLemmaGen .(head ((Γ ∷ (A +S B , n₁)) , D)) (plus-L-head Γ .D A B n₁ p) (headPumping (.(Γ ∷ (A +S B , n₁)) , D) (suc n)) =
    PropPumpingLemmaGen
      (head (Γ ∷ (A , n₁) ∷ (B , n₁) , D))
      p
      (headPumping (Γ ∷ (A , n₁) ∷ (B , n₁), D) (suc n))
  PropPumpingLemmaGen .(head (T , (Δ ∷ (A +S B , n₁)))) (plus-R-head .T Δ A B n₁ p) (headPumping (T , .(Δ ∷ (A +S B , n₁))) (suc n)) =
    PropPumpingLemmaGen
      (head (T , Δ ∷ (A , n₁) ∷ (B , n₁)))
      p
      (headPumping (T , (Δ ∷ (A , n₁) ∷ (B , n₁))) (suc n))
  PropPumpingLemmaGen .(head ((Γ ∷ (-S A , n₁)) , D)) (minus-L-head Γ .D A n₁ p) (headPumping (.(Γ ∷ (-S A , n₁)) , D) (suc n)) =
    PropPumpingLemmaGen
      (head (Γ , D ∷ (A , n₁)))
      p
      (headPumping (Γ , D ∷ (A , n₁)) (suc n))
  PropPumpingLemmaGen .(head (T , (Δ ∷ (-S A , n₁)))) (minus-R-head .T Δ A n₁ p) (headPumping (T , .(Δ ∷ (-S A , n₁))) (suc n)) =
    PropPumpingLemmaGen
      (head (T ∷ (A , n₁) , Δ))
      p
      (headPumping (T ∷ (A , n₁) , Δ) (suc n))
  PropPumpingLemmaGen .(head ((Γ ∷ (botAG , n₁)) , D)) (Z-L-head Γ .D n₁ p) (headPumping (.(Γ ∷ (botAG , n₁)) , D) (suc n)) =
    PropPumpingLemmaGen
      (head (Γ , D))
      p
      (headPumping (Γ , D) (suc n))
  PropPumpingLemmaGen .(head (T , (Δ ∷ (botAG , n₁)))) (Z-R-head .T Δ n₁ p) (headPumping (T , .(Δ ∷ (botAG , n₁))) (suc n)) =
    PropPumpingLemmaGen
      (head (T , Δ))
      p
      (headPumping (T , Δ) (suc n))
  PropPumpingLemmaGen .(head ((Γ ∷ (A ⊔S B , n₁)) , D)) (max-L-head Γ .D A B n₁ p p₁) (headPumping (.(Γ ∷ (A ⊔S B , n₁)) , D) (suc n)) =
    a≤b=>c≤d=>a+c≤b+d
      (PropPumpingLemmaGen
        (head (Γ ∷ (A , n₁) , D))
        p
        (headPumping (Γ ∷ (A , n₁) , D) (suc n)))
      (PropPumpingLemmaGen
        (head (Γ ∷ (B , n₁) , D))
        p₁
        (headPumping (Γ ∷ (B , n₁) , D) (suc n)))
  PropPumpingLemmaGen .(head ((T ∷ (A ⊓S B , n₁)) , Δ)) (min-L-head T .Δ A B n₁ p) (headPumping (.(T ∷ (A ⊓S B , n₁)) , Δ) (suc n)) =
    PropPumpingLemmaGen
      (head (T ∷ (A , n₁) , Δ) ∣ (T ∷ (B , n₁) , Δ))
      p
      (consPumping
        (head (T ∷ (A , n₁) , Δ))
        (headPumping
          (T ∷ (A , n₁) , Δ)
          (suc n))
        (T ∷ (B , n₁) , Δ)
        (suc n))
  PropPumpingLemmaGen .(head (Γ , (D ∷ (A ⊓S B , n₁)))) (min-R-head .Γ D A B n₁ p p₁) (headPumping (Γ , .(D ∷ (A ⊓S B , n₁))) (suc n)) =
    a≤b=>c≤d=>a+c≤b+d
      (PropPumpingLemmaGen
        (head (Γ , D ∷ (A , n₁)))
        p
        (headPumping (Γ , D ∷ (A , n₁)) (suc n)))
      (PropPumpingLemmaGen
        (head (Γ , D ∷ (B , n₁)))
        p₁
        (headPumping (Γ , D ∷ (B , n₁)) (suc n)))
  PropPumpingLemmaGen .(head (T , (Δ ∷ (A ⊔S B , n₁)))) (max-R-head .T Δ A B n₁ p) (headPumping (T , .(Δ ∷ (A ⊔S B , n₁))) (suc n)) =
    PropPumpingLemmaGen
      (head (T , Δ ∷ (A , n₁)) ∣ (T , Δ ∷ (B , n₁)))
      p
      (consPumping
        (head (T , Δ ∷ (A , n₁)))
        (headPumping
          (T , Δ ∷ (A , n₁))
          (suc n))
        (T , Δ ∷ (B , n₁))
        (suc n))
  PropPumpingLemmaGen (head (.T , .D ∷ (one , .(suc k)))) (◆1-rule .T .D ◆Γ ◆Δ refl refl k p) (headPumping (T , D ∷ (one , .(suc k))) (suc n)) =
    cong-≤-l
      (cong
        suc
        (sym
          (MGA-SR†CongKeep#◆
            (PumpingLemmaGen (head (remove◆ ◆Γ , remove◆ ◆Δ ∷ (one , suc k))) p (headPumping (remove◆ ◆Γ , remove◆ ◆Δ ∷ (one , suc k)) (suc n)))
            (cong₂
              (λ x y -> head (x , y ∷ (one , (suc n) * (suc k))))
              (copyRemove ◆Γ (suc n))
              (copyRemove ◆Δ (suc n))))))
      (s≤s
        (PropPumpingLemmaGen
          (head (remove◆ ◆Γ , remove◆ ◆Δ ∷ (one , suc k)))
          p
          (headPumping (remove◆ ◆Γ , remove◆ ◆Δ ∷ (one , suc k)) (suc n))))
  PropPumpingLemmaGen (head (.T , .D)) (◆-rule .T .D ◆Γ ◆Δ refl refl p) (headPumping (T , D) (suc n)) =
    cong-≤-l
      (cong
        suc
        (sym
          (MGA-SR†CongKeep#◆
            (PumpingLemmaGen (head (remove◆ ◆Γ , remove◆ ◆Δ)) p (headPumping (remove◆ ◆Γ , remove◆ ◆Δ) (suc n)))
            (cong₂
              (λ x y -> head (x , y))
              (copyRemove ◆Γ (suc n))
              (copyRemove ◆Δ (suc n))))))
      (s≤s
        (PropPumpingLemmaGen
          (head (remove◆ ◆Γ , remove◆ ◆Δ))
          p
          (headPumping (remove◆ ◆Γ , remove◆ ◆Δ) (suc n))))
  PropPumpingLemmaGen .(head (T , D)) (seq-exchange-head Γ .T Δ .D x x₁ p) (headPumping (T , D) (suc n)) =
    PropPumpingLemmaGen
      (head (Γ , Δ))
      p
      (headPumping (Γ , Δ) (suc n))
  PropPumpingLemmaGen .(head (T , D)) (hseq-exchange G .(head (T , D)) x p) (headPumping (T , D) (suc n)) =
    PropPumpingLemmaGen
      G
      p
      (pumpExchange (head (T , D)) G (headPumping (T , D) (suc n)) (LHSeqExchangeSym x))
  PropPumpingLemmaGen .(G ∣ (T , D)) p (consPumping G pump (T , D) zero) =
    cong-≤-l
      (sym
        (ΔGenNo◆ (doPumping G pump)))
      z≤n
  PropPumpingLemmaGen .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) (W G Γ1 Γ2 Δ1 Δ2 p) (consPumping .(G ∣ (Γ1 , Δ1)) (consPumping .G pump .(Γ1 , Δ1) n₁) .(Γ2 , Δ2) (suc n)) =
    PropPumpingLemmaGen
      (G ∣ (Γ1 , Δ1))
      p
      (consPumping G pump (Γ1 , Δ1) n₁)
  PropPumpingLemmaGen .(G ∣ (Γ , Δ)) (C .G Γ Δ p) (consPumping G pump .(Γ , Δ) (suc n)) =
    PropPumpingLemmaGen
      (G ∣ (Γ , Δ) ∣ (Γ , Δ))
      p
      (consPumping
        (G ∣ (Γ , Δ))
        (consPumping
          G
          pump
          (Γ , Δ)
          (suc n))
        (Γ , Δ)
        (suc n))
  PropPumpingLemmaGen .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) (S G Γ1 Γ2 Δ1 Δ2 refl refl p) (consPumping .(G ∣ (Γ1 , Δ1)) (consPumping .G pump .(Γ1 , Δ1) n₁) .(Γ2 , Δ2) (suc n)) =
    ≤-trans
      (PropPumpingLemmaGen-S-Lemma2
        (doPumping G pump)
        Γ1
        Γ2
        Δ1
        Δ2
        n₁
        (suc n)
        (MGA-SR†Cong
          (PumpingLemmaGen
            (G ∣ (union Γ1 Γ2 , union Δ1 Δ2))
            p
            (consPumping G pump (union Γ1 Γ2 , union Δ1 Δ2) (n₁ * suc n)))
          (cong₂
            (λ x y → doPumping G pump ∣ (x , y))
            (copyUnion Γ1 Γ2 (n₁ * suc n))
            (copyUnion Δ1 Δ2 (n₁ * suc n)))))
      (cong-≤-l
        (sym
          (MGA-SR†CongKeep#◆
            (PumpingLemmaGen
              (G ∣ (union Γ1 Γ2 , union Δ1 Δ2))
              p
              (consPumping G pump (union Γ1 Γ2 , union Δ1 Δ2) (n₁ * suc n)))
            (cong₂
              (λ x y -> doPumping G pump ∣ (x , y))
              (copyUnion Γ1 Γ2 (n₁ * suc n))
              (copyUnion Δ1 Δ2 (n₁ * suc n)))))
        (PropPumpingLemmaGen
          (G ∣ (union Γ1 Γ2 , union Δ1 Δ2))
          p
          (consPumping G pump (union Γ1 Γ2 , union Δ1 Δ2) (n₁ * suc n))))
  PropPumpingLemmaGen .(G ∣ ((Γ ∷ A) , (Δ ∷ A))) (Id-rule .G Γ Δ A p) (consPumping G pump .((Γ ∷ A) , (Δ ∷ A)) (suc n)) =
    PropPumpingLemmaGen
      (G ∣ (Γ , Δ))
      p
      (consPumping
        G
        pump
        (Γ , Δ)
        (suc n))
  PropPumpingLemmaGen .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) (W-head Γ1 Γ2 Δ1 Δ2 p) (consPumping .(head (Γ1 , Δ1)) (headPumping .(Γ1 , Δ1) n₁) .(Γ2 , Δ2) (suc n)) =
    PropPumpingLemmaGen
      (head (Γ1 , Δ1))
      p
      (headPumping (Γ1 , Δ1) n₁)
  PropPumpingLemmaGen .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) (S-head Γ1 Γ2 Δ1 Δ2 refl refl p) (consPumping .(head (Γ1 , Δ1)) (headPumping .(Γ1 , Δ1) n₁) .(Γ2 , Δ2) (suc n)) =
    ≤-trans
      (PropPumpingLemmaGen-S-head-Lemma2
        Γ1
        Γ2
        Δ1
        Δ2
        n₁
        (suc n)
        (MGA-SR†Cong
          (PumpingLemmaGen
            (head (union Γ1 Γ2 , union Δ1 Δ2))
            p
            (headPumping (union Γ1 Γ2 , union Δ1 Δ2) (n₁ * suc n)))
        (cong₂
          (λ x y → head (x , y))
          (copyUnion Γ1 Γ2 (n₁ * suc n))
          (copyUnion Δ1 Δ2 (n₁ * suc n)))))
      (cong-≤-l
        (sym
          (MGA-SR†CongKeep#◆
            (PumpingLemmaGen
              (head (union Γ1 Γ2 , union Δ1 Δ2))
              p
              (headPumping (union Γ1 Γ2 , union Δ1 Δ2) (n₁ * suc n)))
            (cong₂
              (λ x y → head (x , y))
              (copyUnion Γ1 Γ2 (n₁ * suc n))
              (copyUnion Δ1 Δ2 (n₁ * suc n)))))
        (PropPumpingLemmaGen
          (head (union Γ1 Γ2 , union Δ1 Δ2))
          p
          (headPumping (union Γ1 Γ2 , union Δ1 Δ2) (n₁ * suc n))))
  PropPumpingLemmaGen .(G ∣ ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ)) (U-L .G Γ Δ A n1 n2 refl p) (consPumping G pump .((Γ ∷ (A , n1) ∷ (A , n2)) , Δ) (suc n)) =
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          (PumpingLemmaGen
            (G ∣ (Γ ∷ (A , n1 + n2) , Δ))
            p
            (consPumping
              G
              pump
              (Γ ∷ (A , n1 + n2) , Δ)
              (suc n)))
          (cong
            (λ x -> (doPumping G pump) ∣ ((copy Γ (suc n)) ∷ (A , x) , copy Δ (suc n)))
            (c*a+b=c*a+c*b n1 n2 (suc n)))))
      (PropPumpingLemmaGen
        (G ∣ ((Γ ∷ (A , n1 + n2)) , Δ))
        p
        (consPumping G pump ((Γ ∷ (A , n1 + n2)) , Δ) (suc n)))
  PropPumpingLemmaGen .(G ∣ (Γ , (Δ ∷ (A , n1) ∷ (A , n2)))) (U-R .G Γ Δ A n1 n2 refl p) (consPumping G pump .(Γ , (Δ ∷ (A , n1) ∷ (A , n2))) (suc n)) = 
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          (PumpingLemmaGen
            (G ∣ (Γ , Δ  ∷ (A , n1 + n2)))
            p
            (consPumping
              G
              pump
              (Γ , Δ  ∷ (A , n1 + n2))
              (suc n)))
          (cong
            (λ x -> (doPumping G pump) ∣ ((copy Γ (suc n)) , copy Δ (suc n) ∷ (A , x)))
            (c*a+b=c*a+c*b n1 n2 (suc n)))))
      (PropPumpingLemmaGen
        (G ∣ (Γ , (Δ ∷ (A , n1 + n2))))
        p
        (consPumping G pump (Γ , (Δ ∷ (A , n1 + n2))) (suc n)))
  PropPumpingLemmaGen .(G ∣ ((Γ ∷ (A , n1 + n2)) , Δ)) (F-L .G Γ Δ A n1 n2 refl p) (consPumping G pump .((Γ ∷ (A , n1 + n2)) , Δ) (suc n)) = 
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆ 
          (F-L
            (doPumping G pump)
            (copy Γ (suc n))
            (copy Δ (suc n))
            A
            ((suc n) * n1)
            ((suc n) * n2)
            refl
            (PumpingLemmaGen
              (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
              p
              (consPumping
                G
                pump
                (Γ ∷ (A , n1) ∷ (A , n2) , Δ)
                (suc n))))
          (cong
            (λ x -> (doPumping G pump) ∣ ((copy Γ (suc n) ∷ (A , x)) , copy Δ (suc n)))
            (sym
              (c*a+b=c*a+c*b n1 n2 (suc n))))))
      (PropPumpingLemmaGen
        (G ∣ ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ))
        p
        (consPumping G pump ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ) (suc n)))
  PropPumpingLemmaGen .(G ∣ (Γ , (Δ ∷ (A , n1 + n2)))) (F-R .G Γ Δ A n1 n2 refl p) (consPumping G pump .(Γ , (Δ ∷ (A , n1 + n2))) (suc n)) = 
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          (F-R
            (doPumping G pump)
            (copy Γ (suc n))
            (copy Δ (suc n))
            A
            ((suc n) * n1)
            ((suc n) * n2)
            refl
            (PumpingLemmaGen
              (G ∣ (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
              p
              (consPumping
                G
                pump
                (Γ , Δ ∷ (A , n1) ∷ (A , n2))
                (suc n))))
          (cong
            (λ x -> (doPumping G pump) ∣ ((copy Γ (suc n) , copy Δ (suc n) ∷ (A , x))))
            (sym
              (c*a+b=c*a+c*b n1 n2 (suc n))))))
      (PropPumpingLemmaGen
        (G ∣ (Γ , (Δ ∷ (A , n1) ∷ (A , n2))))
        p
        (consPumping G pump (Γ , (Δ ∷ (A , n1) ∷ (A , n2))) (suc n)))
  PropPumpingLemmaGen .(G ∣ ((Γ ∷ (A , 0)) , Δ)) (E-L .G Γ Δ A p) (consPumping G pump .((Γ ∷ (A , 0)) , Δ) (suc n)) = 
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          (E-L
            (doPumping G pump)
            (copy Γ (suc n))
            (copy Δ (suc n))
            A
            (PumpingLemmaGen (G ∣ (Γ , Δ)) p (consPumping G pump (Γ , Δ) (suc n))))
          (cong
            (λ x -> doPumping G pump ∣ ((copy Γ (suc n) ∷ (A , x)) , copy Δ (suc n)))
            (sym (a*0=0 ((suc n)))))))
      (PropPumpingLemmaGen
        (G ∣ (Γ , Δ))
        p
        (consPumping G pump (Γ , Δ) (suc n)))
  PropPumpingLemmaGen .(G ∣ (Γ , (Δ ∷ (A , 0)))) (E-R .G Γ Δ A p) (consPumping G pump .(Γ , (Δ ∷ (A , 0))) (suc n)) = 
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆
          (E-R
            (doPumping G pump)
            (copy Γ (suc n))
            (copy Δ (suc n))
            A
            (PumpingLemmaGen (G ∣ (Γ , Δ)) p (consPumping G pump (Γ , Δ) (suc n))))
          (cong
            (λ x -> doPumping G pump ∣ (copy Γ (suc n) , (copy Δ (suc n) ∷ (A , x))))
            (sym (a*0=0 ((suc n)))))))
      (PropPumpingLemmaGen
        (G ∣ (Γ , Δ))
        p
        (consPumping G pump (Γ , Δ) (suc n)))
  PropPumpingLemmaGen .(G ∣ ((Γ ∷ (A +S B , n₁)) , Δ)) (plus-L .G Γ Δ A B n₁ p) (consPumping G pump .((Γ ∷ (A +S B , n₁)) , Δ) (suc n)) =
    PropPumpingLemmaGen
      (G ∣ (Γ ∷ (A , n₁) ∷ (B , n₁) , Δ))
      p
      (consPumping
        G
        pump
        (Γ ∷ (A , n₁) ∷ (B , n₁) , Δ)
        (suc n))
  PropPumpingLemmaGen .(G ∣ (Γ , (Δ ∷ (A +S B , n₁)))) (plus-R .G Γ Δ A B n₁ p) (consPumping G pump .(Γ , (Δ ∷ (A +S B , n₁))) (suc n)) = 
    PropPumpingLemmaGen
      (G ∣ (Γ , Δ ∷ (A , n₁) ∷ (B , n₁)))
      p
      (consPumping
        G
        pump
        (Γ , Δ ∷ (A , n₁) ∷ (B , n₁))
        (suc n))
  PropPumpingLemmaGen .(G ∣ ((Γ ∷ (-S A , n₁)) , Δ)) (minus-L .G Γ Δ A n₁ p) (consPumping G pump .((Γ ∷ (-S A , n₁)) , Δ) (suc n)) =
    PropPumpingLemmaGen
      (G ∣ (Γ , Δ ∷ (A , n₁)))
      p
      (consPumping
        G
        pump
        (Γ , Δ ∷ (A , n₁))
        (suc n))
  PropPumpingLemmaGen .(G ∣ (Γ , (Δ ∷ (-S A , n₁)))) (minus-R .G Γ Δ A n₁ p) (consPumping G pump .(Γ , (Δ ∷ (-S A , n₁))) (suc n)) = 
    PropPumpingLemmaGen
      (G ∣ (Γ ∷ (A , n₁) , Δ))
      p
      (consPumping
        G
        pump
        (Γ ∷ (A , n₁) , Δ)
        (suc n))
  PropPumpingLemmaGen .(G ∣ ((Γ ∷ (botAG , n₁)) , Δ)) (Z-L .G Γ Δ n₁ p) (consPumping G pump .((Γ ∷ (botAG , n₁)) , Δ) (suc n)) =
    PropPumpingLemmaGen
      (G ∣ (Γ , Δ))
      p
      (consPumping
        G
        pump
        (Γ , Δ)
        (suc n))
  PropPumpingLemmaGen .(G ∣ (Γ , (Δ ∷ (botAG , n₁)))) (Z-R .G Γ Δ n₁ p) (consPumping G pump .(Γ , (Δ ∷ (botAG , n₁))) (suc n)) = 
    PropPumpingLemmaGen
      (G ∣ (Γ , Δ))
      p
      (consPumping
        G
        pump
        (Γ , Δ)
        (suc n))
  PropPumpingLemmaGen .(G ∣ ((Γ ∷ (A ⊔S B , n₁)) , Δ)) (max-L .G Γ Δ A B n₁ p p₁) (consPumping G pump .((Γ ∷ (A ⊔S B , n₁)) , Δ) (suc n)) =
    a≤b=>c≤d=>a+c≤b+d
      (PropPumpingLemmaGen
        (G ∣ (Γ ∷ (A , n₁) , Δ))
        p
        (consPumping
          G
          pump
          (Γ ∷ (A , n₁) , Δ)
          (suc n)))
      (PropPumpingLemmaGen
        (G ∣ (Γ ∷ (B , n₁) , Δ))
        p₁
        (consPumping
          G
          pump
          (Γ ∷ (B , n₁) , Δ)
          (suc n)))
  PropPumpingLemmaGen .(G ∣ (Γ , (Δ ∷ (A ⊔S B , n₁)))) (max-R .G Γ Δ A B n₁ p) (consPumping G pump .(Γ , (Δ ∷ (A ⊔S B , n₁))) (suc n)) =
    PropPumpingLemmaGen
      (G ∣ (Γ , (Δ ∷ (A , n₁))) ∣ (Γ , (Δ ∷ (B , n₁))))
      p
      (consPumping
        (G ∣ (Γ , (Δ ∷ (A , n₁))))
        (consPumping
          G
          pump
          (Γ , (Δ ∷ (A , n₁)))
          (suc n))
        (Γ , (Δ ∷ (B , n₁)))
        (suc n))
  PropPumpingLemmaGen .(G ∣ (Γ , (Δ ∷ (A ⊓S B , n₁)))) (min-R .G Γ Δ A B n₁ p p₁) (consPumping G pump .(Γ , (Δ ∷ (A ⊓S B , n₁))) (suc n)) =
    a≤b=>c≤d=>a+c≤b+d
      (PropPumpingLemmaGen
        (G ∣ (Γ , Δ ∷ (A , n₁)))
        p
        (consPumping
          G
          pump
          (Γ , Δ ∷ (A , n₁))
          (suc n)))
      (PropPumpingLemmaGen
        (G ∣ (Γ , Δ ∷ (B , n₁)))
        p₁
        (consPumping
          G
          pump
          (Γ , Δ ∷ (B , n₁))
          (suc n)))
  PropPumpingLemmaGen .(G ∣ ((Γ ∷ (A ⊓S B , n₁)) , Δ)) (min-L .G Γ Δ A B n₁ p) (consPumping G pump .((Γ ∷ (A ⊓S B , n₁)) , Δ) (suc n)) =
    PropPumpingLemmaGen
      (G ∣ ((Γ ∷ (A , n₁)) , Δ) ∣ ((Γ ∷ (B , n₁)) , Δ))
      p
      (consPumping
        (G ∣ ((Γ ∷ (A , n₁)) , Δ))
        (consPumping
          G
          pump
          ((Γ ∷ (A , n₁)) , Δ)
          (suc n))
        ((Γ ∷ (B , n₁)) , Δ)
        (suc n))
  PropPumpingLemmaGen .(G ∣ (Γ' , Δ')) (seq-exchange .G Γ Γ' Δ Δ' x x₁ p) (consPumping G pump .(Γ' , Δ') (suc n)) =
    PropPumpingLemmaGen
      (G ∣ (Γ , Δ))
      p
      (consPumping G pump (Γ , Δ) (suc n))
  PropPumpingLemmaGen .(G ∣ (T , D)) (hseq-exchange G₁ .(G ∣ (T , D)) x p) (consPumping G pump (T , D) (suc n)) =
    PropPumpingLemmaGen
      G₁
      p
      (pumpExchange
        (G ∣ (T , D))
        G₁
        (consPumping G pump (T , D) (suc n))
        (LHSeqExchangeSym x))
  PropPumpingLemmaGen .(G ∣ (T , D ∷ (one , k))) (1-rule G T D k p) (consPumping .G pump .(T , D ∷ (one , k)) (suc n)) =
    PropPumpingLemmaGen
      (G ∣ (T , D))
      p
      (consPumping G pump (T , D) (suc n))
  PropPumpingLemmaGen (head .(T , D ∷ (one , k))) (1-rule-head T D k p) (headPumping .(T , D ∷ (one , k)) (suc n)) =
    PropPumpingLemmaGen
      (head (T , D))
      p
      (headPumping (T , D) (suc n))
  PropPumpingLemmaGen (head .(T , D)) (can-rule-head T D (A , k) p) (headPumping .(T , D) (suc n)) =
    PropPumpingLemmaGen
      (head (T ∷ (A , k) , D ∷ (A , k)))
      p
      (headPumping (T ∷ (A , k) , D ∷ (A , k)) (suc n))
  PropPumpingLemmaGen (.G ∣ .(T , D)) (can-rule G T D (A , k) p) (consPumping .G pump .(T , D) (suc n)) =
    PropPumpingLemmaGen
      (G ∣ (T ∷ (A , k) , D ∷ (A , k)))
      p
      (consPumping
        G
        pump
        (T ∷ (A , k) , D ∷ (A , k))
        (suc n))
--}}}

  PumpingLemma :
    (G : LHSeq) ->
    (H : LSeq) ->
    (n : ℕ) ->
    (p : MGA-SR† (G ∣ H)) ->
    MGA-SR† (G ∣ (copyLSeq H n))
--{{{
  PumpingLemma G H n p =
    MGA-SR†Cong
      {doPumping G (idPumping G) ∣ (copyLSeq H n)}
      {G ∣ copyLSeq H n}
      (PumpingLemmaGen
        (G ∣ H)
        p
        (consPumping
          G
          (idPumping G)
          H
          n))
      (cong (λ x -> x ∣ copyLSeq H n)
        (idDoPumping G))
--}}}

  PropPumpingLemma :
    (G : LHSeq) ->
    (H : LSeq) ->
    (n : ℕ) ->
    (p : MGA-SR† (G ∣ H)) ->
    #◆ (PumpingLemma G H n p) ≤ #◆ p
--{{{
  PropPumpingLemma G H n p =
    cong-≤-l
      (sym
        (MGA-SR†CongKeep#◆ 
          (PumpingLemmaGen
            (G ∣ H)
            p
            (consPumping
              G
              (idPumping G)
              H
              n))
          (cong (λ x -> x ∣ copyLSeq H n)
            (idDoPumping G))))
      (PropPumpingLemmaGen
        (G ∣ H)
        p
        (consPumping G (idPumping G) H n))
--}}}

  PumpingLemma-head :
    (H : LSeq) ->
    (n : ℕ) ->
    (p : MGA-SR† (head H)) ->
    MGA-SR† (head (copyLSeq H n))
--{{{
  PumpingLemma-head H n p =
    PumpingLemmaGen
      (head H)
      p
      (headPumping
        H
        n)
--}}}

  PropPumpingLemma-head :
    (H : LSeq) ->
    (n : ℕ) ->
    (p : MGA-SR† (head H)) ->
    #◆ (PumpingLemma-head H n p) ≤ #◆ p
--{{{
  PropPumpingLemma-head H n p =
    PropPumpingLemmaGen
      (head H)
      p
      (headPumping H n)
--}}}
