module Syntax.MGA-SR.M-ElimCan.Step2 where
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
  open import Syntax.MGA-SR.M-ElimCan.Preproof
  open import Syntax.MGA-SR
  open import Syntax.MGA-SR.M-ElimCan.PumpingLemma
  open import Syntax.MGA-SR.M-ElimCan.InteractionProofPreproof
  open import Syntax.MGA-SR.M-ElimCan.Step1
  open import Syntax.ListLTerm.Properties
  open import Syntax.LHSeq.Properties
  open import Syntax.MGA-SR.Properties


  mutual
    step2 :
      (G : LHSeq) ->
      (pG : MGA-SR† G) ->
      (H : LHSeq) ->
      (T D : ListLTerm) ->
      (pHTD : MGA-SR† (H ∣ (T , D))) ->
      (n : ℕ) ->
      (◆pG≤n : #◆ pG ≤ n) ->
      (l : LHSeqList) ->
      (propL : propLeavesStep1 H T D (#◆ pG) l) ->
      Acc _<_ (#◆ pG) ->
      Prooflist l
    step2 G pG H T D pHTD n' ◆pG≤n .[]H ([]P1 .H .T .D .(#◆ pG)) (acc rs) =
      []P
    step2 G pG H T D pHTD n' ◆pG≤n(.(H ∣ (union T₁ (copy T n₁) , union (D₁ ∷ (one , suc k)) (copy D n₁))) ∷H l) (consP1 .H T₁ D₁ .T .D ◆T ◆D k p n₁ .(#◆ pG) x propL) (acc rs) =
      consP
        (step2
          G
          pG
          H
          T
          D
          pHTD
          n'
          ◆pG≤n
          l
          propL
          (acc rs))
        (seq-exchange
          H
          (union (copy T n₁) T₁)
          (union T₁ (copy T n₁))
          (union (copy D n₁) (D₁ ∷ (one , suc k)))
          (union (D₁ ∷ (one , suc k)) (copy D n₁))
          (ListExchangeUnion (copy T n₁) T₁)
          (ListExchangeUnion (copy D n₁) (D₁ ∷ (one , suc k)))
          (MGA-SR†Cong
            (MGA-SR†Cong
              (finishPreproof
                (step1-head
                  (H ∣ (copy T n₁ , copy D n₁))
                  T₁
                  (D₁ ∷ (one , suc k))
                  (PumpingLemma
                    H
                    (T , D)
                    n₁
                    pHTD)
                  (◆1-rule
                    T₁
                    D₁
                    ◆T
                    ◆D
                    refl
                    refl
                    k
                    p)
                  (consMerging
                    H
                    (copy T n₁)
                    (copy D n₁)
                    T₁
                    (D₁ ∷ (one , suc k))
                    1
                    (noMerging
                      H
                      T₁
                      (D₁ ∷ (one , suc k)))))
                (step2-bis
                  G
                  pG
                  T₁
                  (copy T n₁)
                  D₁
                  (copy D n₁)
                  n'
                  ◆pG≤n
                  (leaves
                    (step1-head
                      (H ∣ (copy T n₁ , copy D n₁))
                      T₁
                      (D₁ ∷ (one , suc k))
                      (PumpingLemma
                        H
                        (T , D)
                        n₁
                        pHTD)
                      (◆1-rule
                        T₁
                        D₁
                        ◆T
                        ◆D
                        refl
                        refl
                        k
                        p)
                      (consMerging
                        H
                        (copy T n₁)
                        (copy D n₁)
                        T₁
                        (D₁ ∷ (one , suc k))
                        1
                        (noMerging
                          H
                          T₁
                          (D₁ ∷ (one , suc k))))))
                  k
                  (Propstep1-head-bis
                    (H ∣ (copy T n₁ , copy D n₁))
                    T₁
                    (D₁ ∷ (one , suc k))
                    (PumpingLemma
                      H
                      (T , D)
                      n₁
                      pHTD)
                    (◆1-rule
                      T₁
                      D₁
                      ◆T
                      ◆D
                      refl
                      refl
                      k
                      p)
                    (consMerging
                      H
                      (copy T n₁)
                      (copy D n₁)
                      T₁
                      (D₁ ∷ (one , suc k))
                      1
                      (noMerging H T₁ (D₁ ∷ (one , suc k)))))
                  (acc rs)
                  ◆T
                  ◆D
                  p
                  x))
              (cong₂
                (λ x y -> merge H T₁ (D₁ ∷ (one , suc k)) (noMerging H T₁ (D₁ ∷ (one , suc k))) ∣ ((union (copy T n₁) x) , (union (copy D n₁) y)))
                (idCopy T₁)
                (idCopy (D₁ ∷ (one , suc k)))))
            (cong
              (λ x -> x ∣ (union (copy T n₁) T₁ , union (copy D n₁) (D₁ ∷ (one , suc k))))
              (mergeNoMerging
                H
                T₁
                (D₁ ∷ (one , suc k))))))
    step2 G pG H T D pHTD n' ◆pG≤n(.(H ∣ (union T₁ (copy T n₁) , union D₁ (copy D n₁))) ∷H l) (consP1' .H T₁ D₁ .T .D ◆T ◆D p n₁ .(#◆ pG) x propL) (acc rs) =
      consP
        (step2
          G
          pG
          H
          T
          D
          pHTD
          n'
          ◆pG≤n
          l
          propL
          (acc rs))
        (seq-exchange
          H
          (union (copy T n₁) T₁)
          (union T₁ (copy T n₁))
          (union (copy D n₁) D₁)
          (union D₁ (copy D n₁))
          (ListExchangeUnion
            (copy T n₁)
            T₁)
          (ListExchangeUnion
            (copy D n₁)
            D₁)
          (MGA-SR†Cong
            {merge H T₁ D₁ (noMerging H T₁ D₁) ∣ (union (copy T n₁) (copy T₁ 1) , union (copy D n₁) (copy D₁ 1))}
            (finishPreproof
              (step1-head
                (H ∣ (copy T n₁ , copy D n₁))
                T₁
                D₁
                (PumpingLemma
                  H
                  (T , D)
                  n₁
                  pHTD)
                (◆-rule
                  T₁
                  D₁
                  ◆T
                  ◆D
                  refl
                  refl
                  p)
                (consMerging
                  H
                  (copy T n₁)
                  (copy D n₁)
                  T₁
                  D₁
                  1
                  (noMerging H T₁ D₁)))
              (step2-bis'
                G
                pG
                T₁
                (copy T n₁)
                D₁
                (copy D n₁)
                n'
                ◆pG≤n
                (leaves
                  (step1-head
                    (H ∣ (copy T n₁ , copy D n₁))
                    T₁
                    D₁
                    (PumpingLemma
                      H
                      (T , D)
                      n₁
                      pHTD)
                    (◆-rule
                      T₁
                      D₁
                      ◆T
                      ◆D
                      refl
                      refl
                      p)
                    (consMerging
                      H
                      (copy T n₁)
                      (copy D n₁)
                      T₁
                      D₁
                      1
                      (noMerging H T₁ D₁))))
                (Propstep1-head-bis
                  (H ∣ (copy T n₁ , copy D n₁))
                  T₁
                  D₁
                  (PumpingLemma
                    H
                    (T , D)
                    n₁
                    pHTD)
                  (◆-rule
                    T₁
                    D₁
                    ◆T
                    ◆D
                    refl
                    refl
                    p)
                  (consMerging
                    H
                    (copy T n₁)
                    (copy D n₁)
                    T₁
                    D₁
                    1
                    (noMerging H T₁ D₁)))
                (acc rs)
                ◆T
                ◆D
                p
                x))
            (cong₃
              (λ x y z -> x ∣ (union (copy T n₁) y , union (copy D n₁) z))
              (mergeNoMerging
                H
                T₁
                D₁)
              (idCopy
                T₁)
              (idCopy
                D₁))))

    step2-head :
      (G : LHSeq) ->
      (pG : MGA-SR† G) ->
      (T D : ListLTerm) ->
      (pHTD : MGA-SR† (head (T , D))) ->
      (n : ℕ) ->
      (◆pG≤n : #◆ pG ≤ n) -> 
      (l : LHSeqList) ->
      (propL : propLeavesStep1-head T D (#◆ pG) l) ->
      Acc _<_ (#◆ pG) ->
      Prooflist l
    step2-head G pG T D pHTD n' ◆pG≤n .[]H ([]P1head .T .D .(#◆ pG)) (acc rs) =
      []P
    step2-head G pG T D pHTD n' ◆pG≤n (.(head (union T₁ (copy T n₁) , union (D₁ ∷ (one , suc k)) (copy D n₁))) ∷H l) (consP1head T₁ D₁ .T .D ◆T ◆D k p n₁ .(#◆ pG) x propL) (acc rs) =
      consP
        (step2-head
          G
          pG
          T
          D
          pHTD
          n'
          ◆pG≤n
          l
          propL
          (acc rs))
        (seq-exchange-head
          (union (copy T n₁) T₁)
          (union T₁ (copy T n₁))
          (union (copy D n₁) (D₁ ∷ (one , suc k)))
          (union (D₁ ∷ (one , suc k)) (copy D n₁))
          (ListExchangeUnion (copy T n₁) T₁)
          (ListExchangeUnion (copy D n₁) (D₁ ∷ (one , suc k)))
          (MGA-SR†Cong
            (finishPreproof
              (step1-head
                (head (copy T n₁ , copy D n₁))
                T₁
                (D₁ ∷ (one , suc k))
                (PumpingLemma-head
                  (T , D)
                  n₁
                  pHTD)
                (◆1-rule
                  T₁
                  D₁
                  ◆T
                  ◆D
                  refl
                  refl
                  k
                  p)
                (headMerging
                  (copy T n₁)
                  (copy D n₁)
                  T₁
                  (D₁ ∷ (one , suc k))
                  1))
              (step2-bis
                G
                pG
                T₁
                (copy T n₁)
                D₁
                (copy D n₁)
                n'
                ◆pG≤n
                (leaves
                  (step1-head
                    (head (copy T n₁ , copy D n₁))
                    T₁
                    (D₁ ∷ (one , suc k))
                    (PumpingLemma-head
                      (T , D)
                      n₁
                      pHTD)
                    (◆1-rule
                      T₁
                      D₁
                      ◆T
                      ◆D
                      refl
                      refl
                      k
                      p)
                    (headMerging
                      (copy T n₁)
                      (copy D n₁)
                      T₁
                      (D₁ ∷ (one , suc k))
                      1)))
                k
                (Propstep1-head-bis
                  (head (copy T n₁ , copy D n₁))
                  T₁
                  (D₁ ∷ (one , suc k))
                  (PumpingLemma-head
                    (T , D)
                    n₁
                    pHTD)
                  (◆1-rule
                    T₁
                    D₁
                    ◆T
                    ◆D
                    refl
                    refl
                    k
                    p)
                  (headMerging
                    (copy T n₁)
                    (copy D n₁)
                    T₁
                    (D₁ ∷ (one , suc k))
                    1))
                (acc rs)
                ◆T
                ◆D
                p
                x))
            (cong₂
              (λ x y -> head ((union (copy T n₁) x) , (union (copy D n₁) y)))
              (idCopy T₁)
              (idCopy (D₁ ∷ (one , suc k))))))
    step2-head G pG T D pHTD n' ◆pG≤n (.(head (union T₁ (copy T n₁) , union D₁ (copy D n₁))) ∷H l) (consP1head' T₁ D₁ .T .D ◆T ◆D p n₁ .(#◆ pG) x propL) (acc rs) =
      consP
        (step2-head
          G
          pG
          T
          D
          pHTD
          n'
          ◆pG≤n
          l
          propL
          (acc rs))
        (seq-exchange-head
          (union (copy T n₁) T₁)
          (union T₁ (copy T n₁))
          (union (copy D n₁) D₁)
          (union D₁ (copy D n₁))
          (ListExchangeUnion
            (copy T n₁)
            T₁)
          (ListExchangeUnion
            (copy D n₁)
            D₁)
          (MGA-SR†Cong
            {head (union (copy T n₁) (copy T₁ 1) , union (copy D n₁) (copy D₁ 1))}
            (finishPreproof
              (step1-head
                (head (copy T n₁ , copy D n₁))
                T₁
                D₁
                (PumpingLemma-head
                  (T , D)
                  n₁
                  pHTD)
                (◆-rule
                  T₁
                  D₁
                  ◆T
                  ◆D
                  refl
                  refl
                  p)
                (headMerging
                  (copy T n₁)
                  (copy D n₁)
                  T₁
                  D₁
                  1))
              (step2-bis'
                G
                pG
                T₁
                (copy T n₁)
                D₁
                (copy D n₁)
                n'
                ◆pG≤n
                (leaves
                  (step1-head
                    (head (copy T n₁ , copy D n₁))
                    T₁
                    D₁
                    (PumpingLemma-head
                      (T , D)
                      n₁
                      pHTD)
                    (◆-rule
                      T₁
                      D₁
                      ◆T
                      ◆D
                      refl
                      refl
                      p)
                    (headMerging
                      (copy T n₁)
                      (copy D n₁)
                      T₁
                      D₁
                      1)))
                (Propstep1-head-bis
                  (head (copy T n₁ , copy D n₁))
                  T₁
                  D₁
                  (PumpingLemma-head
                    (T , D)
                    n₁
                    pHTD)
                  (◆-rule
                    T₁
                    D₁
                    ◆T
                    ◆D
                    refl
                    refl
                    p)
                  (headMerging
                    (copy T n₁)
                    (copy D n₁)
                    T₁
                    D₁
                    1))
                (acc rs)
                ◆T
                ◆D
                p
                x))
            (cong₂
              (λ y z -> head (union (copy T n₁) y , union (copy D n₁) z))
              (idCopy
                T₁)
              (idCopy
                D₁))))

    step2-bis :
      (G : LHSeq) ->
      (pG : MGA-SR† G) ->
      (T T' D D' : ListLTerm) ->
      (n : ℕ) ->
      (◆pG≤n : #◆ pG ≤ n) ->
      (l : LHSeqList) ->
      (k : ℕ) ->
      (propL : propLeavesStep1-head-bis T (D ∷ (one , suc k)) l) ->
      Acc _<_ (#◆ pG) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (p : MGA-SR† (head (remove◆ ◆T , remove◆ ◆D ∷ (one , suc k)))) ->
      (x : suc (#◆ p) ≤ #◆ pG) ->
      Prooflist l
    step2-bis G pG T T' D D' n ◆pG≤n .[]H k ([]P1head-bis .T .(D ∷ (one , suc k))) (acc rs) ◆T ◆D p x =
      []P
    step2-bis G pG T T' D D' n ◆pG≤n (head .(T₁ , (D₁ ∷ (one , suc k))) ∷H l) k' (consP1head-bis T₁ D₁ .T .(D ∷ (one , suc k')) ◆T₁ ◆D₁ k p₁ zero propL) (acc rs) ◆T ◆D p x =
      consP
        (step2-bis
          G
          pG
          T
          T'
          D
          D'
          n
          ◆pG≤n
          l
          k'
          propL
          (acc rs)
          ◆T
          ◆D
          p
          x)
        (◆1-rule
          T₁
          D₁
          ◆T₁
          ◆D₁
          refl
          refl
          k
          p₁)
    step2-bis G pG T T' D D' n ◆pG≤n (head .(union T₁ (copy T (suc n₁)) , (union (D₁ ∷ (one , suc k)) (copy D (suc n₁)) ∷ (one , suc k' + n₁ * (suc k')))) ∷H l) k' (consP1head-bis T₁ D₁ .T .(D ∷ (one , suc k')) ◆T₁ ◆D₁ k p₁ (suc n₁) propL) (acc rs) ◆T ◆D p x = 
      consP
        (step2-bis
          G
          pG
          T
          T'
          D
          D'
          n
          ◆pG≤n
          l
          k'
          propL
          (acc rs)
          ◆T
          ◆D
          p
          x)
        (seq-exchange-head
          (union T₁ (copy T (suc n₁)))
          (union T₁ (copy T (suc n₁)))
          (union D₁ (copy D (suc n₁)) ∷ (one , suc k) ∷ (one , suc k' + n₁ * (suc k')))
          (union (D₁ ∷ (one , suc k)) (copy D (suc n₁)) ∷ (one , suc k' + n₁ * (suc k')))
          idLE
          (indLE
            (ListExchangeSym
              (exchangeUnionLast
                D₁
                (copy D (suc n₁))
                (one , suc k))))
          (U-R-head
            (union T₁ (copy T (suc n₁)))
            (union D₁ (copy D (suc n₁)))
            one
            (suc k)
            (suc k' + n₁ * (suc k'))
            refl
            (◆1-rule
              (union T₁ (copy T (suc n₁)))
              (union D₁ (copy D (suc n₁)))
              (unionKeep◆
                ◆T₁
                (copyKeep◆
                  ◆T
                  (suc n₁)))
              (unionKeep◆
                ◆D₁
                (copyKeep◆
                  ◆D
                  (suc n₁)))
              refl
              refl
              (k + (suc k' + n₁ * (suc k')))
              (F-R-head
                (remove◆ (unionKeep◆ ◆T₁ (copyKeep◆ ◆T (suc n₁))))
                (remove◆ (unionKeep◆ ◆D₁ (copyKeep◆ ◆D (suc n₁))))
                one
                (suc k)
                (suc k' + n₁ * (suc k'))
                refl
                (MGA-SR†Cong
                  {head (union (remove◆ ◆T₁) (copy (remove◆ ◆T) (suc n₁)) , union (remove◆ ◆D₁) (copy (remove◆ ◆D) (suc n₁)) ∷ (one , suc k) ∷ (one , suc k' + n₁ * (suc k')))}
                  (seq-exchange-head
                    (union (remove◆ ◆T₁) (copy (remove◆ ◆T) (suc n₁)))
                    (union (remove◆ ◆T₁) (copy (remove◆ ◆T) (suc n₁)))
                    (union (remove◆ ◆D₁ ∷ (one , suc k)) (copy (remove◆ ◆D) (suc n₁)) ∷ (one , suc k' + n₁ * (suc k')))
                    (union (remove◆ ◆D₁) (copy (remove◆ ◆D) (suc n₁)) ∷ (one , suc k) ∷ (one , suc k' + n₁ * (suc k')))
                    idLE
                    (indLE
                      (exchangeUnionLast
                        (remove◆ ◆D₁)
                        (copy (remove◆ ◆D) (suc n₁))
                        (one , suc k)))
                    (seq-exchange-head
                      (union (copy (remove◆ ◆T) (suc n₁)) (remove◆ ◆T₁))
                      (union (remove◆ ◆T₁) (copy (remove◆ ◆T) (suc n₁)))
                      (union (copy (remove◆ ◆D ∷ (one , suc k')) (suc n₁)) (remove◆ ◆D₁ ∷ (one , suc k)))
                      (union (remove◆ ◆D₁ ∷ (one , suc k)) (copy (remove◆ ◆D ∷ (one , suc k')) (suc n₁)))
                      (ListExchangeUnion
                        (copy (remove◆ ◆T) (suc n₁))
                        (remove◆ ◆T₁))
                      (ListExchangeUnion
                        (copy (remove◆ ◆D ∷ (one , suc k')) (suc n₁))
                        (remove◆ ◆D₁ ∷ (one , suc k)))
                      (mElim-headGH
                        (copy (remove◆ ◆T) (suc n₁))
                        (remove◆ ◆T₁)
                        (copy (remove◆ ◆D ∷ (one , suc k')) (suc n₁))
                        (remove◆ ◆D₁ ∷ (one , suc k))
                        (PumpingLemma-head
                          (remove◆ ◆T , remove◆ ◆D ∷ (one , suc k'))
                          (suc n₁)
                          p)
                        p₁
                        (rs
                          (#◆ (PumpingLemma-head (remove◆ ◆T , (remove◆ ◆D ∷ (one , suc k'))) (suc n₁) p))
                          (≤-trans
                            (s≤s
                              (PropPumpingLemma-head
                                (remove◆ ◆T , (remove◆ ◆D ∷ (one , suc k')))
                                (suc n₁)
                                p))
                            x)))))
                  (cong₂
                    (λ x y -> head (x , y ∷ (one , suc k) ∷ (one , suc k' + n₁ * (suc k'))))
                    (sym
                      (begin
                        remove◆ (unionKeep◆ ◆T₁ (copyKeep◆ ◆T (suc n₁)))
                          ≡⟨ remove◆Union
                               ◆T₁
                               (copyKeep◆ ◆T (suc n₁)) ⟩
                        union (remove◆ ◆T₁) (remove◆ (copyKeep◆ ◆T (suc n₁)))
                          ≡⟨ cong
                               (λ x -> union (remove◆ ◆T₁) x)
                               (remove◆Copy
                                 ◆T
                                 (suc n₁)) ⟩
                        union (remove◆ ◆T₁) (copy (remove◆ ◆T) (suc n₁)) ∎))
                    (sym
                      (begin
                        remove◆ (unionKeep◆ ◆D₁ (copyKeep◆ ◆D (suc n₁)))
                          ≡⟨ remove◆Union
                               ◆D₁
                               (copyKeep◆ ◆D (suc n₁)) ⟩
                        union (remove◆ ◆D₁) (remove◆ (copyKeep◆ ◆D (suc n₁)))
                          ≡⟨ cong
                               (λ x -> union (remove◆ ◆D₁) x)
                               (remove◆Copy
                                 ◆D
                                 (suc n₁)) ⟩
                        union (remove◆ ◆D₁) (copy (remove◆ ◆D) (suc n₁)) ∎))))))))
    step2-bis G pG T T' D D' n ◆pG≤n (head .(union T₁ (copy T (suc n₁)) , (union D₁ (copy D (suc n₁)) ∷ (one , suc k' + n₁ * (suc k')))) ∷H l) k' (consP1head-bis' T₁ D₁ .T .(D ∷ (one , suc k')) ◆T₁ ◆D₁ p₁ (suc n₁) propL) (acc rs) ◆T ◆D p x = 
      consP
        (step2-bis
          G
          pG
          T
          T'
          D
          D'
          n
          ◆pG≤n
          l
          k'
          propL
          (acc rs)
          ◆T
          ◆D
          p
          x)
        (◆1-rule
          (union T₁ (copy T (suc n₁)))
          (union D₁ (copy D (suc n₁)))
          (unionKeep◆
            ◆T₁
            (copyKeep◆
              ◆T
              (suc n₁)))
          (unionKeep◆
            ◆D₁
            (copyKeep◆
              ◆D
              (suc n₁)))
          refl
          refl
          (k' + n₁ * suc k')
          (MGA-SR†Cong
            {head (union (remove◆ ◆T₁) (copy (remove◆ ◆T) (suc n₁)) , union (remove◆ ◆D₁) (copy (remove◆ ◆D) (suc n₁)) ∷ (one , suc (k' + n₁ * suc k')))}
            (seq-exchange-head
              (union (copy (remove◆ ◆T) (suc n₁)) (remove◆ ◆T₁))
              (union (remove◆ ◆T₁) (copy (remove◆ ◆T) (suc n₁)))
              (union (copy (remove◆ ◆D) (suc n₁) ∷ (one , suc k' + n₁ * suc k')) (remove◆ ◆D₁))
              (union (remove◆ ◆D₁) (copy (remove◆ ◆D) (suc n₁) ∷ (one , suc k' + n₁ * suc k')))
              (ListExchangeUnion
                (copy (remove◆ ◆T) (suc n₁))
                (remove◆ ◆T₁))
              (ListExchangeUnion
                (copy (remove◆ ◆D) (suc n₁) ∷ (one , suc k' + n₁ * suc k'))
                (remove◆ ◆D₁))
              (mElim-headGH
                (copy (remove◆ ◆T) (suc n₁))
                (remove◆ ◆T₁)
                (copy (remove◆ ◆D) (suc n₁) ∷ (one , suc k' + n₁ * suc k'))
                (remove◆ ◆D₁)
                (PumpingLemma-head
                  (remove◆ ◆T , remove◆ ◆D ∷ (one , suc k'))
                  (suc n₁)
                  p)
                p₁
                (rs
                  (#◆
                    (PumpingLemma-head
                      (remove◆ ◆T , remove◆ ◆D ∷ (one , suc k'))
                      (suc n₁)
                      p))
                  (≤-trans
                    (s≤s
                      (PropPumpingLemma-head
                        (remove◆ ◆T , remove◆ ◆D ∷ (one , suc k'))
                        (suc n₁)
                        p))
                    x))))
            (cong₂
              (λ x y -> head (x , y ∷ (one , suc k' + n₁ * suc k')))
              (sym
                (begin
                  remove◆ (unionKeep◆ ◆T₁ (copyKeep◆ ◆T (suc n₁)))
                    ≡⟨ remove◆Union
                         ◆T₁
                         (copyKeep◆ ◆T (suc n₁)) ⟩
                  union (remove◆ ◆T₁) (remove◆ (copyKeep◆ ◆T (suc n₁)))
                    ≡⟨ cong
                         (λ x -> union (remove◆ ◆T₁) x)
                         (remove◆Copy
                           ◆T
                           (suc n₁)) ⟩
                  union (remove◆ ◆T₁) (copy (remove◆ ◆T) (suc n₁)) ∎))
              (sym
                (begin
                  remove◆ (unionKeep◆ ◆D₁ (copyKeep◆ ◆D (suc n₁)))
                    ≡⟨ remove◆Union
                         ◆D₁
                         (copyKeep◆ ◆D (suc n₁)) ⟩
                  union (remove◆ ◆D₁) (remove◆ (copyKeep◆ ◆D (suc n₁)))
                    ≡⟨ cong
                         (λ x -> union (remove◆ ◆D₁) x)
                         (remove◆Copy
                           ◆D
                           (suc n₁)) ⟩
                  union (remove◆ ◆D₁) (copy (remove◆ ◆D) (suc n₁)) ∎)))))
    step2-bis G pG T T' D D' n ◆pG≤n (head .(T₁ , D₁) ∷H l) k' (consP1head-bis' T₁ D₁ .T .(D ∷ (one , suc k')) ◆T₁ ◆D₁ p₁ 0 propL) (acc rs) ◆T ◆D p x = 
      consP
        (step2-bis
          G
          pG
          T
          T'
          D
          D'
          n
          ◆pG≤n
          l
          k'
          propL
          (acc rs)
          ◆T
          ◆D
          p
          x)
        (◆-rule
          T₁
          D₁
          ◆T₁
          ◆D₁
          refl
          refl
          p₁) 

    step2-bis' :
      (G : LHSeq) ->
      (pG : MGA-SR† G) ->
      (T T' D D' : ListLTerm) ->
      (n : ℕ) ->
      (◆pG≤n : #◆ pG ≤ n) ->
      (l : LHSeqList) ->
      (propL : propLeavesStep1-head-bis T D l) ->
      Acc _<_ (#◆ pG) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (p : MGA-SR† (head (remove◆ ◆T , remove◆ ◆D))) ->
      (x : suc (#◆ p) ≤ #◆ pG) ->
      Prooflist l
    step2-bis' G pG T T' D D' n ◆pG≤n .[]H ([]P1head-bis .T .D) (acc rs) ◆T ◆D p x =
      []P
    step2-bis' G pG T T' D D' n ◆pG≤n (head .(union T₁ (copy T n₁) , union (D₁ ∷ (one , suc k)) (copy D n₁)) ∷H l) (consP1head-bis T₁ D₁ .T .D ◆T₁ ◆D₁ k p₁ n₁ propL) (acc rs) ◆T ◆D p x = 
      consP
        (step2-bis'
          G
          pG
          T
          T'
          D
          D'
          n
          ◆pG≤n
          l
          propL
          (acc rs)
          ◆T
          ◆D
          p
          x)
        (seq-exchange-head
          (union (copy T n₁) T₁)
          (union T₁ (copy T n₁))
          (union (copy D n₁) (D₁ ∷ (one , suc k)))
          (union (D₁ ∷ (one , suc k)) (copy D n₁))
          (ListExchangeUnion
            (copy T n₁)
            T₁)
          (ListExchangeUnion
            (copy D n₁)
            (D₁ ∷ (one , suc k)))
          (◆1-rule
            (union (copy T n₁) T₁)
            (union (copy D n₁) D₁)
            (unionKeep◆
              (copyKeep◆ ◆T n₁)
              ◆T₁)
            (unionKeep◆
              (copyKeep◆ ◆D n₁)
              ◆D₁)
            refl
            refl
            k
            (MGA-SR†Cong
              {head (union (copy (remove◆ ◆T) n₁) (remove◆ ◆T₁) , (union (copy (remove◆ ◆D) n₁) (remove◆ ◆D₁)) ∷ (one , suc k))}
              (mElim-headGH
                (copy (remove◆ ◆T) n₁)
                (remove◆ ◆T₁)
                (copy (remove◆ ◆D) n₁)
                (remove◆ ◆D₁ ∷ (one , suc k))
                (PumpingLemma-head
                  (remove◆ ◆T , remove◆ ◆D)
                  n₁
                  p)
                p₁
                (rs
                  (#◆ (PumpingLemma-head (remove◆ ◆T , remove◆ ◆D) n₁ p))
                  (≤-trans
                    (s≤s
                      (PropPumpingLemma-head
                        (remove◆ ◆T , remove◆ ◆D)
                        n₁
                        p))
                    x)))
              (cong₂
                (λ x y -> head (x , y ∷ (one , suc k)))
                (sym
                  (begin
                    remove◆ (unionKeep◆ (copyKeep◆ ◆T n₁) ◆T₁)
                      ≡⟨ remove◆Union
                           (copyKeep◆ ◆T n₁)
                           ◆T₁ ⟩
                    union (remove◆ (copyKeep◆ ◆T n₁)) (remove◆ ◆T₁)
                      ≡⟨ cong
                          (λ x -> union x (remove◆ ◆T₁))
                          (remove◆Copy
                            ◆T
                            n₁) ⟩
                    union (copy (remove◆ ◆T) n₁) (remove◆ ◆T₁) ∎))
                (sym
                  (begin
                    remove◆ (unionKeep◆ (copyKeep◆ ◆D n₁) ◆D₁)
                      ≡⟨ remove◆Union
                           (copyKeep◆ ◆D n₁)
                           ◆D₁ ⟩
                    union (remove◆ (copyKeep◆ ◆D n₁)) (remove◆ ◆D₁)
                      ≡⟨ cong
                          (λ x -> union x (remove◆ ◆D₁))
                          (remove◆Copy
                            ◆D
                            n₁) ⟩
                    union (copy (remove◆ ◆D) n₁) (remove◆ ◆D₁) ∎))))))
    step2-bis' G pG T T' D D' n ◆pG≤n (head .(union T₁ (copy T n₁) , union D₁ (copy D n₁)) ∷H l) (consP1head-bis' T₁ D₁ .T .D ◆T₁ ◆D₁ p₁ n₁ propL) (acc rs) ◆T ◆D p x = 
      consP
        (step2-bis'
          G
          pG
          T
          T'
          D
          D'
          n
          ◆pG≤n
          l
          propL
          (acc rs)
          ◆T
          ◆D
          p
          x)
        (◆-rule
          (union T₁ (copy T n₁))
          (union D₁ (copy D n₁))
          (unionKeep◆
            ◆T₁
            (copyKeep◆ ◆T n₁))
          (unionKeep◆
            ◆D₁
            (copyKeep◆ ◆D n₁))
          refl
          refl
          (MGA-SR†Cong
            {head (union (remove◆ ◆T₁) (copy (remove◆ ◆T) n₁) , union (remove◆ ◆D₁) (copy (remove◆ ◆D) n₁))}
            (seq-exchange-head
              (union (copy (remove◆ ◆T) n₁) (remove◆ ◆T₁))
              (union (remove◆ ◆T₁) (copy (remove◆ ◆T) n₁))
              (union (copy (remove◆ ◆D) n₁) (remove◆ ◆D₁))
              (union (remove◆ ◆D₁) (copy (remove◆ ◆D) n₁))
              (ListExchangeUnion
                (copy (remove◆ ◆T) n₁)
                (remove◆ ◆T₁))
              (ListExchangeUnion
                (copy (remove◆ ◆D) n₁)
                (remove◆ ◆D₁))
              (mElim-headGH
                (copy (remove◆ ◆T) n₁)
                (remove◆ ◆T₁)
                (copy (remove◆ ◆D) n₁)
                (remove◆ ◆D₁)
                (PumpingLemma-head
                  (remove◆ ◆T , remove◆ ◆D)
                  n₁
                  p)
                p₁
                (rs
                  (#◆ (PumpingLemma-head (remove◆ ◆T , remove◆ ◆D) n₁ p))
                  (≤-trans
                    (s≤s
                      (PropPumpingLemma-head
                        (remove◆ ◆T , remove◆ ◆D)
                        n₁
                        p))
                    x))))
            (cong₂
              (λ x y -> head (x , y))
              (sym
                (begin
                  remove◆ (unionKeep◆ ◆T₁ (copyKeep◆ ◆T n₁))
                    ≡⟨ remove◆Union
                         ◆T₁
                         (copyKeep◆ ◆T n₁) ⟩
                  union (remove◆ ◆T₁) (remove◆ (copyKeep◆ ◆T n₁))
                    ≡⟨ cong
                         (λ x -> union (remove◆ ◆T₁) x)
                         (remove◆Copy
                           ◆T
                           n₁) ⟩
                  union (remove◆ ◆T₁) (copy (remove◆ ◆T) n₁) ∎))
              (sym
                (begin
                  remove◆ (unionKeep◆ ◆D₁ (copyKeep◆ ◆D n₁))
                    ≡⟨ remove◆Union
                         ◆D₁
                         (copyKeep◆ ◆D n₁) ⟩
                  union (remove◆ ◆D₁) (remove◆ (copyKeep◆ ◆D n₁))
                    ≡⟨ cong
                         (λ x -> union (remove◆ ◆D₁) x)
                         (remove◆Copy
                           ◆D
                           n₁) ⟩
                  union (remove◆ ◆D₁) (copy (remove◆ ◆D) n₁) ∎)))))

    mElim :
      (G H : LHSeq) ->
      (T T' D D' : ListLTerm) ->
      (pG : MGA-SR† (G ∣ (T , D))) ->
      (pHTD : MGA-SR† (H ∣ (T' , D'))) ->
      Acc _<_ (#◆ pG) ->
      MGA-SR† (unionLHSeq G H ∣ (union T T' , union D D'))
    mElim G H T T' D D' pG pHTD (acc rs) =
      hseq-exchange
        (unionLHSeq H G ∣ (union T T' , union D D'))
        (unionLHSeq G H ∣ (union T T' , union D D'))
        (indHE
          (unionLHSeq H G)
          (unionLHSeq G H)
          (LHSeqExchangeUnion H G))
        (MGA-SR†Cong
          (finishPreproof
            (step1
              (G ∣ (T , D))
              H
              T'
              D'
              pG
              pHTD
              (consMerging
                G
                T
                D
                T'
                D'
                1
                (noMerging G T' D')))
            (step2
              (G ∣ (T , D))
              pG
              H
              T'
              D'
              pHTD
              (#◆ pG)
              (k≤k (#◆ pG))
              (leaves
                (step1
                  (G ∣ (T , D))
                  H
                  T'
                  D'
                  pG
                  pHTD
                  (consMerging
                    G
                    T
                    D
                    T'
                    D'
                    1
                    (noMerging G T' D'))))
              (Propstep1
                (G ∣ (T , D))
                H
                T'
                D'
                pG
                pHTD
                (#◆ pG)
                (k≤k (#◆ pG))
                (consMerging
                  G
                  T
                  D
                  T'
                  D'
                  1
                  (noMerging G T' D')))
              (acc rs)))
          (trans
            (cong
              (λ x -> unionLHSeq H x ∣ (union T (copy T' 1) , union D (copy D' 1)))
              (mergeNoMerging G T' D'))
            (cong₂
              (λ x y -> unionLHSeq H G ∣ (union T x , union D y))
              (idCopy T')
              (idCopy D'))))

    mElim-headGH :
      (T T' D D' : ListLTerm) ->
      (pG : MGA-SR† (head (T , D))) ->
      (pHTD : MGA-SR† (head (T' , D'))) ->
      Acc _<_ (#◆ pG) ->
      MGA-SR† (head (union T T' , union D D'))
    mElim-headGH T T' D D' pG pHTD (acc rs) =
      MGA-SR†Cong
        (finishPreproof
          (step1-head
            (head (T , D))
            T'
            D'
            pG
            pHTD
            (headMerging
              T
              D
              T'
              D'
              1))
          (step2-head
            (head (T , D))
            pG
            T'
            D'
            pHTD
            (#◆ pG)
            (k≤k (#◆ pG))
            (leaves
              (step1-head
                (head (T , D))
                T'
                D'
                pG
                pHTD
                (headMerging
                  T
                  D
                  T'
                  D'
                  1)))
            (Propstep1-head
              (head (T , D))
              T'
              D'
              pG
              pHTD
              (#◆ pG)
              (k≤k (#◆ pG))
              (headMerging
                T
                D
                T'
                D'
                1))
            (acc rs)))
        (cong₂
          (λ x y -> (head (union T x , union D y)))
          (idCopy T')
          (idCopy D'))

  applyContraction :
    (G H : LHSeq) ->
    MGA-SR† (unionLHSeq (unionLHSeq G G) H) ->
    MGA-SR† (unionLHSeq G H)
  applyContraction (head (T , D)) H p =
    hseq-exchange
      (H ∣ (T , D))
      (unionLHSeq (head (T , D)) H)
      (LHSeqExchangeUnion H (head (T , D)))
      (C
        H
        T
        D
        (hseq-exchange
          (unionLHSeq (head (T , D) ∣ (T , D)) H)
          (H ∣ (T , D)  ∣ (T , D))
          (LHSeqExchangeUnion (head (T , D) ∣ (T , D)) H)
          p))
  applyContraction (G ∣ (T , D)) H p =
    hseq-exchange
      (unionLHSeq G H ∣ (T , D))
      (unionLHSeq (G ∣ (T , D)) H)
      (LHSeqExchangeSym
        (unionLHSeqExchangeLast G H T D))
      (C
        (unionLHSeq G H)
        T
        D
        (applyContraction
          G
          (H ∣ (T , D) ∣ (T , D))
          (hseq-exchange
            (unionLHSeq (unionLHSeq (G ∣ (T , D)) (G ∣ (T , D))) H)
            (unionLHSeq (unionLHSeq G G) H ∣ (T , D) ∣ (T , D))
            (LHSeqExchangeSym
              (transHE
                (LHSeqExchangeSym (unionLHSeqExchangeLast (unionLHSeq G G) (H ∣ (T , D)) T D))
                (transHE
                  (unionKeepLHSeqExchangeLeft
                    (LHSeqExchangeSym
                      (unionLHSeqExchangeLast
                        G
                        G
                        T
                        D))
                    (H ∣ (T , D)))
                  (LHSeqExchangeSym (unionLHSeqExchangeLast (unionLHSeq (G ∣ (T , D)) G) H T D)))))
            p)))
