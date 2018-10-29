module Syntax.MGA-SR.M-Elim.Step1 where
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
  open import Syntax.MGA-SR.M-Elim.Preproof
  open import Syntax.MGA-SR
  open import Syntax.MGA-SR.M-Elim.PumpingLemma
  open import Syntax.MGA-SR.M-Elim.InteractionProofPreproof
  open import Syntax.ListLTerm.Properties
  open import Syntax.LHSeq.Properties
  open import Syntax.MGA-SR.Properties
  
  data Merging : LHSeq -> ListLTerm -> ListLTerm -> Set where
    headMerging :
      (T D T' D' : ListLTerm) ->
      (n : ℕ) ->
      Merging (head (T , D)) T' D'
    consMerging :
      (G : LHSeq) ->
      (T D T' D' : ListLTerm) ->
      (n : ℕ) ->
      (merging : Merging G T' D') ->
      Merging (G ∣ (T , D)) T' D'

  noMerging :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    Merging G T D
--{{{
  noMerging (head (T₁ , D₁)) T D =
    headMerging
      T₁
      D₁
      T
      D
      0
  noMerging (G ∣ (T₁ , D₁)) T D =
    consMerging
      G
      T₁
      D₁
      T
      D
      0
      (noMerging G T D)
--}}}

  merge :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    Merging G T D ->
    LHSeq
--{{{
  merge .(head (T₁ , D₁)) T D (headMerging T₁ D₁ .T .D n) =
    head (union T₁ (copy T n) , union D₁ (copy D n))
  merge .(G ∣ (T₁ , D₁)) T D (consMerging G T₁ D₁ .T .D n merging) =
    (merge G T D merging) ∣ (union T₁ (copy T n) , union D₁ (copy D n))
--}}}

  mergeNoMerging :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    (merge G T D (noMerging G T D)) ≡ G
--{{{
  mergeNoMerging (head (T₁ , D₁)) T D =
    refl
  mergeNoMerging (G ∣ (T₁ , D₁)) T D =
    cong
      (λ x -> x ∣ (T₁ , D₁))
      (mergeNoMerging G T D)
--}}}

  MergingExchange :
    (G G' : LHSeq) ->
    (T D : ListLTerm) ->
    Merging G T D ->
    LHSeqExchange G G' ->
    Merging G' T D
--{{{
  MergingExchange G .G T D m idHE =
    m
  MergingExchange (G ∣ .(T₂ , D₂) ∣ .(T₁ , D₁)) (G' ∣ _ ∣ _) T D (consMerging .(G ∣ (T₂ , D₂)) T₁ D₁ .T .D n (consMerging .G T₂ D₂ .T .D n₁ m)) (exHE G=G') =
    consMerging
      (G' ∣ (T₁ , D₁))
      T₂
      D₂
      T
      D
      n₁
      (consMerging
        G'
        T₁
        D₁
        T
        D
        n
        (MergingExchange G G' T D m G=G'))
  MergingExchange .(head (T₂ , D₂) ∣ (T₁ , D₁)) .(head (T₁ , D₁) ∣ (T₂ , D₂)) T D (consMerging .(head (T₂ , D₂)) T₁ D₁ .T .D n (headMerging T₂ D₂ .T .D n₁)) exHE-head = 
    consMerging
      (head (T₁ , D₁))
      T₂
      D₂
      T
      D
      n₁
      (headMerging
        T₁
        D₁
        T
        D
        n)
  MergingExchange G G' T D m (transHE {G₂ = G₂} G=G' G=G'') =
    MergingExchange G₂ G' T D (MergingExchange G G₂ T D m G=G') G=G''
  MergingExchange .(G ∣ (T₁ , D₁)) .(G' ∣ (T₁ , D₁)) T D (consMerging .G T₁ D₁ .T .D n m) (indHE G G' G=G') =
    consMerging
      G'
      T₁
      D₁
      T
      D
      n
      (MergingExchange G G' T D m G=G')
--}}}

  mergeExchange :
    (G G' : LHSeq) ->
    (T D : ListLTerm) ->
    (m : Merging G T D) ->
    (G=G' : LHSeqExchange G G') ->
    LHSeqExchange (merge G T D m) (merge G' T D (MergingExchange G G' T D m G=G'))
--{{{
  mergeExchange G .G T D m idHE =
    idHE
  mergeExchange .(G ∣ (T₂ , D₂) ∣ (T₁ , D₁)) (G' ∣ .(T₁ , D₁) ∣ .(T₂ , D₂)) T D (consMerging .(G ∣ (T₂ , D₂)) T₁ D₁ .T .D n (consMerging G T₂ D₂ .T .D n₁ m)) (exHE G=G') =
    exHE
      (mergeExchange G G' T D m G=G')
  mergeExchange .(head (T₂ , D₂) ∣ (T₁ , D₁)) .(head (T₁ , D₁) ∣ (T₂ , D₂)) T D (consMerging .(head (T₂ , D₂)) T₁ D₁ .T .D n (headMerging T₂ D₂ .T .D n₁)) exHE-head = 
    exHE-head
  mergeExchange G G' T D m (transHE {G₂ = G₂} G=G' G=G'') =
    transHE
      (mergeExchange G G₂ T D m G=G')
      (mergeExchange G₂ G' T D (MergingExchange G G₂ T D m G=G') G=G'')
  mergeExchange .(G ∣ (T₁ , D₁)) .(G' ∣ (T₁ , D₁)) T D (consMerging .G T₁ D₁ .T .D n m) (indHE G G' G=G') =
    indHE
      (merge G T D m)
      (merge G' T D (MergingExchange G G' T D m G=G'))
      (mergeExchange G G' T D m G=G')
--}}}


  step1* :
    (G H : LHSeq) ->
    (T D : ListLTerm) ->
    MGA-SR†* G ->
    MGA-SR†* (H ∣ (T , D)) ->
    (m : Merging G T D) ->
    Preproof* (unionLHSeq H (merge G T D m))
--{{{
  step1* .(head ([] , [])) H T D ax pHTD (headMerging .[] .[] .T .D n) =
    Preproof*Cong
      {H ∣ (copy T n , copy D n)}
      (proofToPreproof*
        (PumpingLemma H (T , D) n pHTD))
      (cong₂
        (λ x y -> H ∣ (x , y))
        (sym (union[]T=T (copy T n)))
        (sym (union[]T=T (copy D n))))
  step1* .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) H T D (W G Γ1 Γ2 Δ1 Δ2 pG) pHTD (consMerging .(G ∣ (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (consMerging .G .Γ1 .Δ1 .T .D n₁ m)) =
    W
      (unionLHSeq H (merge G T D m))
      (union Γ1 (copy T n₁))
      (union Γ2 (copy T n))
      (union Δ1 (copy D n₁))
      (union Δ2 (copy D n))
      (step1*
        (G ∣ (Γ1 , Δ1))
        H
        T
        D
        pG
        pHTD
        (consMerging G Γ1 Δ1 T D n₁ m))
  step1* .(G ∣ (Γ , Δ)) H T D (C G Γ Δ pG) pHTD (consMerging .G .Γ .Δ .T .D n m) =
    C
      (unionLHSeq H (merge G T D m))
      (union Γ (copy T n))
      (union Δ (copy D n))
      (step1*
        (G ∣ (Γ , Δ) ∣ (Γ , Δ))
        H
        T
        D
        pG
        pHTD
        (consMerging (G ∣ (Γ , Δ)) Γ Δ T D n (consMerging G Γ Δ T D n m)))
  step1* .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) H T D (S G Γ1 Γ2 Δ1 Δ2 refl refl pG) pHTD (consMerging .(G ∣ (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (consMerging .G .Γ1 .Δ1 .T .D n₁ m)) =
    S
      (unionLHSeq H (merge G T D m))
      (union Γ1 (copy T n₁))
      (union Γ2 (copy T n))
      (union Δ1 (copy D n₁))
      (union Δ2 (copy D n))
      refl
      refl
      (seq-exchange
        (unionLHSeq H (merge G T D m))
        (union (union Γ1 Γ2) (union (copy T n₁) (copy T n)))
        (union (union Γ1 (copy T n₁)) (union Γ2 (copy T n)))
        (union (union Δ1 Δ2) (union (copy D n₁) (copy D n)))
        (union (union Δ1 (copy D n₁)) (union Δ2 (copy D n)))
        (ListExchangeSym
          (transLE
            (union-assoc
              Γ1
              (copy T n₁)
              (union Γ2 (copy T n)))
            (transLE
              (unionKeepExchangeRight
                Γ1
                (transLE
                  (ListExchangeSym
                    (union-assoc
                      (copy T n₁)
                      Γ2
                      (copy T n)))
                  (transLE
                    (unionKeepExchangeLeft
                      (ListExchangeUnion
                        (copy T n₁)
                        Γ2)
                      (copy T n))
                    (union-assoc
                      Γ2
                      (copy T n₁)
                      (copy T n)))))
                (ListExchangeSym
                  (union-assoc
                    Γ1
                    Γ2
                    (union (copy T n₁) (copy T n))))))) 
        (ListExchangeSym
          (transLE
            (union-assoc
              Δ1
              (copy D n₁)
              (union Δ2 (copy D n)))
            (transLE
              (unionKeepExchangeRight
                Δ1
                (transLE
                  (ListExchangeSym
                    (union-assoc
                      (copy D n₁)
                      Δ2
                      (copy D n)))
                  (transLE
                    (unionKeepExchangeLeft
                      (ListExchangeUnion
                        (copy D n₁)
                        Δ2)
                      (copy D n))
                    (union-assoc
                      Δ2
                      (copy D n₁)
                      (copy D n)))))
                (ListExchangeSym
                  (union-assoc
                    Δ1
                    Δ2
                    (union (copy D n₁) (copy D n)))))))
        (unionCopy-L*
          (unionLHSeq H (merge G T D m))
          (union Γ1 Γ2)
          T
          (union (union Δ1 Δ2) (union (copy D n₁) (copy D n)))
          n₁
          n
          (unionCopy-R*
            (unionLHSeq H (merge G T D m))
            (union (union Γ1 Γ2) (copy T (n₁ + n)))
            (union Δ1 Δ2)
            D
            n₁
            n
            (step1*
              (G ∣ (union Γ1 Γ2 , union Δ1 Δ2))
              H
              T
              D
              pG
              pHTD
              (consMerging
                G
                (union Γ1 Γ2)
                (union Δ1 Δ2)
                T
                D
                (n₁ + n)
                m)))))
  step1* .(G ∣ ((Γ ∷ (A , n')) , (Δ ∷ (A , n')))) H T D (Id-rule G Γ Δ (A , n') pG) pHTD (consMerging .G .(Γ ∷ (A , n')) .(Δ ∷ (A , n')) .T .D n m) =
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n)) ∷ (A , n'))
      (union (Γ ∷ (A , n')) (copy T n))
      ((union Δ (copy D n)) ∷ (A , n'))
      (union (Δ ∷ (A , n')) (copy  D n))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n)
          (A , n')))
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n)
          (A , n')))
      (Id-rule
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n))
        (union Δ (copy D n))
        (A , n')
        (step1*
          (G ∣ (Γ , Δ))
          H
          T
          D
          pG
          pHTD
          (consMerging G Γ Δ T D n m)))
  step1* .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) H T D (W-head Γ1 Γ2 Δ1 Δ2 pG) pHTD (consMerging .(head (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (headMerging .Γ1 .Δ1 .T .D n₁)) = 
    W
      H
      (union Γ1 (copy T n₁))
      (union Γ2 (copy T n))
      (union Δ1 (copy D n₁))
      (union Δ2 (copy D n))
      (step1*
        (head (Γ1 , Δ1))
        H
        T
        D
        pG
        pHTD
        (headMerging Γ1 Δ1 T D n₁))
  step1* .(head (Γ , Δ)) H T D (C-head Γ Δ pG) pHTD (headMerging .Γ .Δ .T .D n) = 
    C
      H
      (union Γ (copy T n))
      (union Δ (copy D n))
      (step1*
        (head (Γ , Δ) ∣ (Γ , Δ))
        H
        T
        D
        pG
        pHTD
        (consMerging (head (Γ , Δ)) Γ Δ T D n (headMerging Γ Δ T D n)))
  step1* .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) H T D (S-head Γ1 Γ2 Δ1 Δ2 refl refl pG) pHTD (consMerging .(head (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (headMerging .Γ1 .Δ1 .T .D n₁)) = 
    S
      H
      (union Γ1 (copy T n₁))
      (union Γ2 (copy T n))
      (union Δ1 (copy D n₁))
      (union Δ2 (copy D n))
      refl
      refl
      (seq-exchange
        H
        (union (union Γ1 Γ2) (union (copy T n₁) (copy T n)))
        (union (union Γ1 (copy T n₁)) (union Γ2 (copy T n)))
        (union (union Δ1 Δ2) (union (copy D n₁) (copy D n)))
        (union (union Δ1 (copy D n₁)) (union Δ2 (copy D n)))
        (ListExchangeSym
          (transLE
            (union-assoc
              Γ1
              (copy T n₁)
              (union Γ2 (copy T n)))
            (transLE
              (unionKeepExchangeRight
                Γ1
                (transLE
                  (ListExchangeSym
                    (union-assoc
                      (copy T n₁)
                      Γ2
                      (copy T n)))
                  (transLE
                    (unionKeepExchangeLeft
                      (ListExchangeUnion
                        (copy T n₁)
                        Γ2)
                      (copy T n))
                    (union-assoc
                      Γ2
                      (copy T n₁)
                      (copy T n)))))
                (ListExchangeSym
                  (union-assoc
                    Γ1
                    Γ2
                    (union (copy T n₁) (copy T n))))))) 
        (ListExchangeSym
          (transLE
            (union-assoc
              Δ1
              (copy D n₁)
              (union Δ2 (copy D n)))
            (transLE
              (unionKeepExchangeRight
                Δ1
                (transLE
                  (ListExchangeSym
                    (union-assoc
                      (copy D n₁)
                      Δ2
                      (copy D n)))
                  (transLE
                    (unionKeepExchangeLeft
                      (ListExchangeUnion
                        (copy D n₁)
                        Δ2)
                      (copy D n))
                    (union-assoc
                      Δ2
                      (copy D n₁)
                      (copy D n)))))
                (ListExchangeSym
                  (union-assoc
                    Δ1
                    Δ2
                    (union (copy D n₁) (copy D n)))))))
        (unionCopy-L*
          H
          (union Γ1 Γ2)
          T
          (union (union Δ1 Δ2) (union (copy D n₁) (copy D n)))
          n₁
          n
          (unionCopy-R*
            H
            (union (union Γ1 Γ2) (copy T (n₁ + n)))
            (union Δ1 Δ2)
            D
            n₁
            n
            (step1*
              (head (union Γ1 Γ2 , union Δ1 Δ2))
              H
              T
              D
              pG
              pHTD
              (headMerging
                (union Γ1 Γ2)
                (union Δ1 Δ2)
                T
                D
                (n₁ + n))))))
  step1* .(head ((Γ ∷ (A , n')) , (Δ ∷ (A , n')))) H T D (Id-rule-head Γ Δ (A , n') pG) pHTD (headMerging .(Γ ∷ (A , n')) .(Δ ∷ (A , n')) .T .D n) = 
    seq-exchange
      H
      ((union Γ (copy T n)) ∷ (A , n'))
      (union (Γ ∷ (A , n')) (copy T n))
      ((union Δ (copy D n)) ∷ (A , n'))
      (union (Δ ∷ (A , n')) (copy  D n))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n)
          (A , n')))
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n)
          (A , n')))
      (Id-rule
        H
        (union Γ (copy T n))
        (union Δ (copy D n))
        (A , n')
        (step1*
          (head (Γ , Δ))
          H
          T
          D
          pG
          pHTD
          (headMerging Γ Δ T D n)))
  step1* .(G ∣ ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ)) H T D (U-L G Γ Δ A n1 n2 refl pG) pHTD (consMerging .G .(Γ ∷ (A , n1) ∷ (A , n2)) .Δ .T .D n m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n)) ∷ (A , n1) ∷ (A , n2))
      (union (Γ ∷ (A , n1) ∷ (A , n2)) (copy T n))
      ((union Δ (copy D n)))
      (union Δ (copy  D n))
      (ListExchangeSym
        (transLE
          (exchangeUnionLast
            (Γ ∷ (A , n1))
            (copy T n)
            (A , n2))
          (indLE
            (exchangeUnionLast
              Γ
              (copy T n)
              (A , n1)))))
      idLE
      (U-L
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange
          (unionLHSeq H (merge G T D m))
          (union (Γ ∷ (A , n1 + n2)) (copy T n))
          ((union Γ (copy T n)) ∷ (A , n1 + n2))
          (union Δ (copy D n))
          (union Δ (copy D n))
          (exchangeUnionLast
            Γ
            (copy T n)
            (A , n1 + n2))
          idLE
          (step1*
            (G ∣ (Γ ∷ (A , n1 + n2) , Δ))
            H
            T
            D
            pG
            pHTD
            (consMerging
              G
              (Γ ∷ (A , n1 + n2))
              Δ
              T
              D
              n
              m))))
  step1* .(G ∣ (Γ , (Δ ∷ (A , n1) ∷ (A , n2)))) H T D (U-R G Γ Δ A n1 n2 refl pG) pHTD (consMerging G Γ (Δ ∷ (A , n1) ∷ (A , n2)) T D n m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n)))
      (union Γ (copy  T n))
      ((union Δ (copy D n)) ∷ (A , n1) ∷ (A , n2))
      (union (Δ ∷ (A , n1) ∷ (A , n2)) (copy D n))
      idLE
      (ListExchangeSym
        (transLE
          (exchangeUnionLast
            (Δ ∷ (A , n1))
            (copy D n)
            (A , n2))
          (indLE
            (exchangeUnionLast
              Δ
              (copy D n)
              (A , n1)))))
      (U-R
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange
          (unionLHSeq H (merge G T D m))
          (union Γ (copy T n))
          (union Γ (copy T n))
          (union (Δ ∷ (A , n1 + n2)) (copy D n))
          ((union Δ (copy D n)) ∷ (A , n1 + n2))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n)
            (A , n1 + n2))
          (step1*
            (G ∣ (Γ , Δ ∷ (A , n1 + n2)))
            H
            T
            D
            pG
            pHTD
            (consMerging
              G
              Γ
              (Δ ∷ (A , n1 + n2))
              T
              D
              n
              m))))
  step1* .(G ∣ ((Γ ∷ (A , n1 + n2)) , Δ)) H T D (F-L G Γ Δ A n1 n2 refl pG) pHTD (consMerging .G .(Γ ∷ (A , n1 + n2)) .Δ .T .D n m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n)) ∷ (A , n1 + n2))
      (union (Γ ∷ (A , n1 + n2)) (copy T n))
      ((union Δ (copy D n)))
      (union Δ (copy  D n))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n)
          (A , n1 + n2)))
      idLE
      (F-L
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange
          (unionLHSeq H (merge G T D m))
          (union (Γ ∷ (A , n1) ∷ (A , n2)) (copy T n))
          ((union Γ (copy T n)) ∷ (A , n1) ∷ (A , n2))
          (union Δ (copy D n))
          (union Δ (copy D n))
          (transLE
            (exchangeUnionLast
              (Γ ∷ (A , n1))
              (copy T n)
              (A , n2))
            (indLE
              (exchangeUnionLast
                Γ
                (copy T n)
                (A , n1))))
          idLE
          (step1*
            (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
            H
            T
            D
            pG
            pHTD
            (consMerging
              G
              (Γ ∷ (A , n1) ∷ (A , n2))
              Δ
              T
              D
              n
              m))))
  step1* .(G ∣ (Γ , (Δ ∷ (A , n1 + n2)))) H T D (F-R G Γ Δ A n1 n2 refl pG) pHTD (consMerging .G .Γ .(Δ ∷ (A , n1 + n2)) .T .D n m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n)))
      (union Γ (copy  T n))
      ((union Δ (copy D n)) ∷ (A , n1 + n2))
      (union (Δ ∷ (A , n1 + n2)) (copy D n))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n)
          (A , n1 + n2)))
      (F-R
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange
          (unionLHSeq H (merge G T D m))
          (union Γ (copy T n))
          (union Γ (copy T n))
          (union (Δ ∷ (A , n1) ∷ (A , n2)) (copy D n))
          ((union Δ (copy D n)) ∷ (A , n1) ∷ (A , n2))
          idLE
          (transLE
            (exchangeUnionLast
              (Δ ∷ (A , n1))
              (copy D n)
              (A , n2))
            (indLE
              (exchangeUnionLast
                Δ
                (copy D n)
                (A , n1))))
          (step1*
            (G ∣ (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
            H
            T
            D
            pG
            pHTD
            (consMerging
              G
              Γ
              (Δ ∷ (A , n1) ∷ (A , n2))
              T
              D
              n
              m))))
  step1* .(head ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ)) H T D (U-L-head Γ Δ A n1 n2 refl pG) pHTD (headMerging .(Γ ∷ (A , n1) ∷ (A , n2)) .Δ .T .D n) = 
    seq-exchange
      H
      ((union Γ (copy T n)) ∷ (A , n1) ∷ (A , n2))
      (union (Γ ∷ (A , n1) ∷ (A , n2)) (copy T n))
      ((union Δ (copy D n)))
      (union Δ (copy  D n))
      (ListExchangeSym
        (transLE
          (exchangeUnionLast
            (Γ ∷ (A , n1))
            (copy T n)
            (A , n2))
          (indLE
            (exchangeUnionLast
              Γ
              (copy T n)
              (A , n1)))))
      idLE
      (U-L
        H
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange
          H
          (union (Γ ∷ (A , n1 + n2)) (copy T n))
          ((union Γ (copy T n)) ∷ (A , n1 + n2))
          (union Δ (copy D n))
          (union Δ (copy D n))
          (exchangeUnionLast
            Γ
            (copy T n)
            (A , n1 + n2))
          idLE
          (step1*
            (head (Γ ∷ (A , n1 + n2) , Δ))
            H
            T
            D
            pG
            pHTD
            (headMerging
              (Γ ∷ (A , n1 + n2))
              Δ
              T
              D
              n))))
  step1* .(head (Γ , (Δ ∷ (A , n1) ∷ (A , n2)))) H T D (U-R-head Γ Δ A n1 n2 refl pG) pHTD (headMerging .Γ .(Δ ∷ (A , n1) ∷ (A , n2)) .T .D n) = 
    seq-exchange
      H
      ((union Γ (copy T n)))
      (union Γ (copy  T n))
      ((union Δ (copy D n)) ∷ (A , n1) ∷ (A , n2))
      (union (Δ ∷ (A , n1) ∷ (A , n2)) (copy D n))
      idLE
      (ListExchangeSym
        (transLE
          (exchangeUnionLast
            (Δ ∷ (A , n1))
            (copy D n)
            (A , n2))
          (indLE
            (exchangeUnionLast
              Δ
              (copy D n)
              (A , n1)))))
      (U-R
        H
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange
          H
          (union Γ (copy T n))
          (union Γ (copy T n))
          (union (Δ ∷ (A , n1 + n2)) (copy D n))
          ((union Δ (copy D n)) ∷ (A , n1 + n2))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n)
            (A , n1 + n2))
          (step1*
            (head (Γ , Δ ∷ (A , n1 + n2)))
            H
            T
            D
            pG
            pHTD
            (headMerging
              Γ
              (Δ ∷ (A , n1 + n2))
              T
              D
              n))))
  step1* .(head ((Γ ∷ (A , n1 + n2)) , Δ)) H T D (F-L-head Γ Δ A n1 n2 refl pG) pHTD (headMerging .(Γ ∷ (A , n1 + n2)) .Δ .T .D n) = 
    seq-exchange
      H
      ((union Γ (copy T n)) ∷ (A , n1 + n2))
      (union (Γ ∷ (A , n1 + n2)) (copy T n))
      ((union Δ (copy D n)))
      (union Δ (copy  D n))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n)
          (A , n1 + n2)))
      idLE
      (F-L
        H
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange
          H
          (union (Γ ∷ (A , n1) ∷ (A , n2)) (copy T n))
          ((union Γ (copy T n)) ∷ (A , n1) ∷ (A , n2))
          (union Δ (copy D n))
          (union Δ (copy D n))
          (transLE
            (exchangeUnionLast
              (Γ ∷ (A , n1))
              (copy T n)
              (A , n2))
            (indLE
              (exchangeUnionLast
                Γ
                (copy T n)
                (A , n1))))
          idLE
          (step1*
            (head (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
            H
            T
            D
            pG
            pHTD
            (headMerging
              (Γ ∷ (A , n1) ∷ (A , n2))
              Δ
              T
              D
              n))))
  step1* .(head (Γ , (Δ ∷ (A , n1 + n2)))) H T D (F-R-head Γ Δ A n1 n2 refl pG) pHTD (headMerging .Γ .(Δ ∷ (A , n1 + n2)) .T .D n) = 
    seq-exchange
      H
      ((union Γ (copy T n)))
      (union Γ (copy  T n))
      ((union Δ (copy D n)) ∷ (A , n1 + n2))
      (union (Δ ∷ (A , n1 + n2)) (copy D n))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n)
          (A , n1 + n2)))
      (F-R
        H
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange
          H
          (union Γ (copy T n))
          (union Γ (copy T n))
          (union (Δ ∷ (A , n1) ∷ (A , n2)) (copy D n))
          ((union Δ (copy D n)) ∷ (A , n1) ∷ (A , n2))
          idLE
          (transLE
            (exchangeUnionLast
              (Δ ∷ (A , n1))
              (copy D n)
              (A , n2))
            (indLE
              (exchangeUnionLast
                Δ
                (copy D n)
                (A , n1))))
          (step1*
            (head (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
            H
            T
            D
            pG
            pHTD
            (headMerging
              Γ
              (Δ ∷ (A , n1) ∷ (A , n2))
              T
              D
              n))))
  step1* .(G ∣ ((Γ ∷ (A , 0)) , Δ)) H T D (E-L G Γ Δ A pG) pHTD (consMerging .G .(Γ ∷ (A , 0)) .Δ .T .D n m) =  
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n)) ∷ (A , 0))
      (union (Γ ∷ (A , 0)) (copy T n))
      ((union Δ (copy D n)))
      (union Δ (copy  D n))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n)
          (A , 0)))
      idLE
      (E-L
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        (step1*
          (G ∣ (Γ , Δ))
          H
          T
          D
          pG
          pHTD
          (consMerging
            G
            Γ
            Δ
            T
            D
            n
            m)))
  step1* .(G ∣ (Γ , (Δ ∷ (A , 0)))) H T D (E-R G Γ Δ A pG) pHTD (consMerging .G .Γ .(Δ ∷ (A , 0)) .T .D n m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n)))
      (union Γ (copy  T n))
      ((union Δ (copy D n)) ∷ (A , 0))
      (union (Δ ∷ (A , 0)) (copy D n))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n)
          (A , 0)))
      (E-R
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        (step1*
          (G ∣ (Γ , Δ))
          H
          T
          D
          pG
          pHTD
          (consMerging
            G
            Γ
            Δ
            T
            D
            n
            m)))
  step1* .(head ((Γ ∷ (A , 0)) , Δ)) H T D (E-L-head Γ Δ A pG) pHTD (headMerging .(Γ ∷ (A , 0)) .Δ .T .D n) = 
    seq-exchange
      H
      ((union Γ (copy T n)) ∷ (A , 0))
      (union (Γ ∷ (A , 0)) (copy T n))
      ((union Δ (copy D n)))
      (union Δ (copy  D n))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n)
          (A , 0)))
      idLE
      (E-L
        H
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        (step1*
          (head (Γ , Δ))
          H
          T
          D
          pG
          pHTD
          (headMerging
            Γ
            Δ
            T
            D
            n)))
  step1* .(head (Γ , (Δ ∷ (A , 0)))) H T D (E-R-head Γ Δ A pG) pHTD (headMerging .Γ .(Δ ∷ (A , 0)) .T .D n) = 
    seq-exchange
      H
      ((union Γ (copy T n)))
      (union Γ (copy  T n))
      ((union Δ (copy D n)) ∷ (A , 0))
      (union (Δ ∷ (A , 0)) (copy D n))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n)
          (A , 0)))
      (E-R
        H
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        (step1*
          (head (Γ , Δ))
          H
          T
          D
          pG
          pHTD
          (headMerging
            Γ
            Δ
            T
            D
            n)))
  step1* .(G ∣ ((Γ ∷ (A +S B , n)) , Δ)) H T D (plus-L G Γ Δ A B n pG) pHTD (consMerging .G .(Γ ∷ (A +S B , n)) .Δ .T .D n₁ m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n₁)) ∷ (A +S B , n))
      (union (Γ ∷ (A +S B , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (A +S B , n)))
      idLE
      (plus-L
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange
          (unionLHSeq H (merge G T D m))
          (union (Γ ∷ (A , n) ∷ (B , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (A , n) ∷ (B , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (transLE
            (exchangeUnionLast
              (Γ ∷ (A , n))
              (copy T n₁)
              (B , n))
            (indLE
              (exchangeUnionLast
                Γ
                (copy T n₁)
                (A , n))))
          idLE
          (step1*
            (G ∣ (Γ ∷ (A , n) ∷ (B , n) , Δ))
            H
            T
            D
            pG
            pHTD
            (consMerging
              G
              (Γ ∷ (A , n) ∷ (B , n))
              Δ
              T
              D
              n₁
              m))))
  step1* .(G ∣ (Γ , (Δ ∷ (A +S B , n)))) H T D (plus-R G Γ Δ A B n pG) pHTD (consMerging .G .Γ  .(Δ ∷ (A +S B , n)) .T .D n₁ m)  = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (A +S B , n))
      (union (Δ ∷ (A +S B , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (A +S B , n)))
      (plus-R
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange
          (unionLHSeq H (merge G T D m))
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (A , n) ∷ (B , n)) (copy D n₁))
          ((union Δ (copy D n₁)) ∷ (A , n) ∷ (B , n))
          idLE
          (transLE
            (exchangeUnionLast
              (Δ ∷ (A , n))
              (copy D n₁)
              (B , n))
            (indLE
              (exchangeUnionLast
                Δ
                (copy D n₁)
                (A , n))))
          (step1*
            (G ∣ (Γ , Δ ∷ (A , n) ∷ (B , n)))
            H
            T
            D
            pG
            pHTD
            (consMerging
              G
              Γ
              (Δ ∷ (A , n) ∷ (B , n))
              T
              D
              n₁
              m))))
  step1* .(G ∣ ((Γ ∷ (botAG , n)) , Δ)) H T D (Z-L G Γ Δ n pG) pHTD (consMerging .G .(Γ ∷ (botAG , n)) .Δ .T .D n₁ m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n₁)) ∷ (botAG , n))
      (union (Γ ∷ (botAG , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (botAG , n)))
      idLE
      (Z-L
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        n
        (step1*
          (G ∣ (Γ , Δ))
          H
          T
          D
          pG
          pHTD
          (consMerging
            G
            Γ
            Δ
            T
            D
            n₁
            m)))
  step1* .(G ∣ (Γ , (Δ ∷ (botAG , n)))) H T D (Z-R G Γ Δ n pG) pHTD (consMerging .G .Γ  .(Δ ∷ (botAG , n)) .T .D n₁ m)  = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (botAG , n))
      (union (Δ ∷ (botAG , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (botAG , n)))
      (Z-R
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        n
        (step1*
          (G ∣ (Γ , Δ))
          H
          T
          D
          pG
          pHTD
          (consMerging
            G
            Γ
            Δ
            T
            D
            n₁
            m)))
  step1* .(G ∣ ((Γ ∷ (-S A , n)) , Δ)) H T D (minus-L G Γ Δ A n pG) pHTD (consMerging .G .(Γ ∷ (-S A , n)) .Δ .T .D n₁ m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n₁)) ∷ (-S A , n))
      (union (Γ ∷ (-S A , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (-S A , n)))
      idLE
      (minus-L
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        n
        (seq-exchange
          (unionLHSeq H (merge G T D m))
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (A , n)) (copy D n₁))
          (union Δ (copy D n₁) ∷ (A , n))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n₁)
            (A , n))
          (step1*
            (G ∣ (Γ , Δ ∷ (A , n)))
            H
            T
            D
            pG
            pHTD
            (consMerging
              G
              Γ
              (Δ ∷ (A , n))
              T
              D
              n₁
              m))))
  step1* .(G ∣ (Γ , (Δ ∷ (-S A , n)))) H T D (minus-R G Γ Δ A n pG) pHTD (consMerging .G .Γ  .(Δ ∷ (-S A , n)) .T .D n₁ m)  = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (-S A , n))
      (union (Δ ∷ (-S A , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (-S A , n)))
      (minus-R
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        n
        (seq-exchange
          (unionLHSeq H (merge G T D m))
          (union (Γ ∷ (A , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (A , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (exchangeUnionLast
            Γ
            (copy T n₁)
            (A , n))
          idLE
          (step1*
            (G ∣ (Γ ∷ (A , n) , Δ))
            H
            T
            D
            pG
            pHTD
            (consMerging
              G
              (Γ ∷ (A , n))
              Δ
              T
              D
              n₁
              m))))
  step1* .(G ∣ ((Γ ∷ (A ⊔S B , n)) , Δ)) H T D (max-L G Γ Δ A B n pG pG₁) pHTD (consMerging .G .(Γ ∷ (A ⊔S B , n)) .Δ .T .D n₁ m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n₁)) ∷ (A ⊔S B , n))
      (union (Γ ∷ (A ⊔S B , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (A ⊔S B , n)))
      idLE
      (max-L
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange
          (unionLHSeq H (merge G T D m))
          (union (Γ ∷ (A , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (A , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (exchangeUnionLast
            Γ
            (copy T n₁)
            (A , n))
          idLE
          (step1*
            (G ∣ (Γ ∷ (A , n) , Δ))
            H
            T
            D
            pG
            pHTD
            (consMerging
              G
              (Γ ∷ (A , n))
              Δ
              T
              D
              n₁
              m)))
        (seq-exchange
          (unionLHSeq H (merge G T D m))
          (union (Γ ∷ (B , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (B , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (exchangeUnionLast
            Γ
            (copy T n₁)
            (B , n))
          idLE
          (step1*
            (G ∣ (Γ ∷ (B , n) , Δ))
            H
            T
            D
            pG₁
            pHTD
            (consMerging
              G
              (Γ ∷ (B , n))
              Δ
              T
              D
              n₁
              m))))
  step1* .(G ∣ (Γ , (Δ ∷ (A ⊔S B , n)))) H T D (max-R G Γ Δ A B n pG) pHTD (consMerging .G .Γ .(Δ ∷ (A ⊔S B , n)) .T .D n₁ m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (A ⊔S B , n))
      (union (Δ ∷ (A ⊔S B , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (A ⊔S B , n)))
      (max-R
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (hseq-exchange
          (unionLHSeq H (merge G T D m) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (A , n))))
          (unionLHSeq H (merge G T D m) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (A , n))) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))))
          (exHE
            idHE)
          (seq-exchange
            (unionLHSeq H (merge G T D m) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁)) ∷ (B , n)))
            (union Γ (copy T n₁))
            (union Γ (copy T n₁))
            (union (Δ ∷ (A , n)) (copy D n₁))
            ((union Δ (copy D n₁)) ∷ (A , n))
            idLE
            (exchangeUnionLast
              Δ
              (copy D n₁)
              (A , n))
            (hseq-exchange
              (unionLHSeq H (merge G T D m) ∣ (union Γ (copy T n₁) , union (Δ ∷ (A , n)) (copy D n₁)) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))))
              (unionLHSeq H (merge G T D m) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))) ∣ (union Γ (copy T n₁) , union (Δ ∷ (A , n)) (copy D n₁)))
              (exHE
                idHE)
              (seq-exchange
                (unionLHSeq H (merge G T D m) ∣ (union Γ (copy T n₁) , union (Δ ∷ (A , n)) (copy D n₁)))
                (union Γ (copy T n₁))
                (union Γ (copy T n₁))
                (union (Δ ∷ (B , n)) (copy D n₁))
                ((union Δ (copy D n₁)) ∷ (B , n))
                idLE
                (exchangeUnionLast
                  Δ
                  (copy D n₁)
                  (B , n))
                (step1*
                  (G ∣ (Γ , Δ ∷ (A , n)) ∣ (Γ , Δ ∷ (B , n)))
                  H
                  T
                  D
                  pG
                  pHTD
                  (consMerging
                    (G ∣ (Γ , (Δ ∷ (A , n))))
                    Γ
                    (Δ ∷ (B , n))
                    T
                    D
                    n₁
                    (consMerging
                      G
                      Γ
                      (Δ ∷ (A , n))
                      T
                      D
                      n₁
                      m))))))))
  step1* .(G ∣ (Γ , (Δ ∷ (A ⊓S B , n)))) H T D (min-R G Γ Δ A B n pG pG₁) pHTD (consMerging .G .Γ .(Δ ∷ (A ⊓S B , n)) .T .D n₁ m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (A ⊓S B , n))
      (union (Δ ∷ (A ⊓S B , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (A ⊓S B , n)))
      (min-R
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange
          (unionLHSeq H (merge G T D m))
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (A , n)) (copy D n₁))
          ((union Δ (copy D n₁)) ∷ (A , n))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n₁)
            (A , n))
          (step1*
            (G ∣ (Γ , Δ ∷ (A , n)))
            H
            T
            D
            pG
            pHTD
            (consMerging
              G
              Γ
              (Δ ∷ (A , n))
              T
              D
              n₁
              m)))
        (seq-exchange
          (unionLHSeq H (merge G T D m))
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (B , n)) (copy D n₁))
          ((union Δ (copy D n₁)) ∷ (B , n))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n₁)
            (B , n))
          (step1*
            (G ∣ (Γ , Δ ∷ (B , n)))
            H
            T
            D
            pG₁
            pHTD
            (consMerging
              G
              Γ
              (Δ ∷ (B , n))
              T
              D
              n₁
              m))))
  step1* .(G ∣ ((Γ ∷ (A ⊓S B , n)) , Δ)) H T D (min-L G Γ Δ A B n pG) pHTD (consMerging .G .(Γ ∷ (A ⊓S B , n)) .Δ .T .D n₁ m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      ((union Γ (copy T n₁)) ∷ (A ⊓S B , n))
      (union (Γ ∷ (A ⊓S B , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (A ⊓S B , n)))
      idLE
      (min-L
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (hseq-exchange
          (unionLHSeq H (merge G T D m) ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)) ∣ ((union Γ (copy T n₁) ∷ (A , n)) , union Δ (copy D n₁)))
          (unionLHSeq H (merge G T D m) ∣ ((union Γ (copy T n₁) ∷ (A , n)) , union Δ (copy D n₁)) ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)))
          (exHE
            idHE)
          (seq-exchange
            (unionLHSeq H (merge G T D m) ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)))
            (union (Γ ∷ (A , n)) (copy T n₁))
            ((union Γ (copy T n₁)) ∷ (A , n))
            (union Δ (copy D n₁))
            (union Δ (copy D n₁))
            (exchangeUnionLast
              Γ
              (copy T n₁)
              (A , n))
            idLE
            (hseq-exchange
              (unionLHSeq H (merge G T D m) ∣ (union (Γ ∷ (A , n)) (copy T n₁) , union Δ (copy D n₁)) ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)))
              (unionLHSeq H (merge G T D m) ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)) ∣ (union (Γ ∷ (A , n)) (copy T n₁) , union Δ (copy D n₁)))
              (exHE
                idHE)
              (seq-exchange
                (unionLHSeq H (merge G T D m) ∣ (union (Γ ∷ (A , n)) (copy T n₁) , union Δ (copy D n₁)))
                (union (Γ ∷ (B , n)) (copy T n₁))
                ((union Γ (copy T n₁)) ∷ (B , n))
                (union Δ (copy D n₁))
                (union Δ (copy D n₁))
                (exchangeUnionLast
                  Γ
                  (copy T n₁)
                  (B , n))
                idLE
                (step1*
                  (G ∣ (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ))
                  H
                  T
                  D
                  pG
                  pHTD
                  (consMerging
                    (G ∣ (Γ ∷ (A , n) , Δ))
                    (Γ ∷ (B , n))
                    Δ
                    T
                    D
                    n₁
                    (consMerging
                      G
                      (Γ ∷ (A , n))
                      Δ
                      T
                      D
                      n₁
                      m))))))))
  step1* .(head ((Γ ∷ (A +S B , n)) , Δ)) H T D (plus-L-head Γ Δ A B n pG) pHTD (headMerging .(Γ ∷ (A +S B , n)) .Δ .T .D n₁) = 
    seq-exchange
      H
      ((union Γ (copy T n₁)) ∷ (A +S B , n))
      (union (Γ ∷ (A +S B , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (A +S B , n)))
      idLE
      (plus-L
        H
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange
          H
          (union (Γ ∷ (A , n) ∷ (B , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (A , n) ∷ (B , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (transLE
            (exchangeUnionLast
              (Γ ∷ (A , n))
              (copy T n₁)
              (B , n))
            (indLE
              (exchangeUnionLast
                Γ
                (copy T n₁)
                (A , n))))
          idLE
          (step1*
            (head (Γ ∷ (A , n) ∷ (B , n) , Δ))
            H
            T
            D
            pG
            pHTD
            (headMerging
              (Γ ∷ (A , n) ∷ (B , n))
              Δ
              T
              D
              n₁))))
  step1* .(head (Γ , (Δ ∷ (A +S B , n)))) H T D (plus-R-head Γ Δ A B n pG) pHTD (headMerging .Γ .(Δ ∷ (A +S B , n)) .T .D n₁) = 
    seq-exchange
      H
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (A +S B , n))
      (union (Δ ∷ (A +S B , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (A +S B , n)))
      (plus-R
        H
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange
          H
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (A , n) ∷ (B , n)) (copy D n₁))
          ((union Δ (copy D n₁)) ∷ (A , n) ∷ (B , n))
          idLE
          (transLE
            (exchangeUnionLast
              (Δ ∷ (A , n))
              (copy D n₁)
              (B , n))
            (indLE
              (exchangeUnionLast
                Δ
                (copy D n₁)
                (A , n))))
          (step1*
            (head (Γ , Δ ∷ (A , n) ∷ (B , n)))
            H
            T
            D
            pG
            pHTD
            (headMerging
              Γ
              (Δ ∷ (A , n) ∷ (B , n))
              T
              D
              n₁))))
  step1* .(head ((Γ ∷ (botAG , n)) , Δ)) H T D (Z-L-head Γ Δ n pG) pHTD (headMerging .(Γ ∷ (botAG , n)) .Δ .T .D n₁) = 
    seq-exchange
      H
      ((union Γ (copy T n₁)) ∷ (botAG , n))
      (union (Γ ∷ (botAG , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (botAG , n)))
      idLE
      (Z-L
        H
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        n
        (step1*
          (head (Γ , Δ))
          H
          T
          D
          pG
          pHTD
          (headMerging
            Γ
            Δ
            T
            D
            n₁)))
  step1* .(head (Γ , (Δ ∷ (botAG , n)))) H T D (Z-R-head Γ Δ n pG) pHTD (headMerging .Γ  .(Δ ∷ (botAG , n)) .T .D n₁)  = 
    seq-exchange
      H
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (botAG , n))
      (union (Δ ∷ (botAG , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (botAG , n)))
      (Z-R
        H
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        n
        (step1*
          (head (Γ , Δ))
          H
          T
          D
          pG
          pHTD
          (headMerging
            Γ
            Δ
            T
            D
            n₁)))
  step1* .(head ((Γ ∷ (-S A , n)) , Δ)) H T D (minus-L-head Γ Δ A n pG) pHTD (headMerging .(Γ ∷ (-S A , n)) .Δ .T .D n₁) = 
    seq-exchange
      H
      ((union Γ (copy T n₁)) ∷ (-S A , n))
      (union (Γ ∷ (-S A , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (-S A , n)))
      idLE
      (minus-L
        H
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        n
        (seq-exchange
          H
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (A , n)) (copy D n₁))
          (union Δ (copy D n₁) ∷ (A , n))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n₁)
            (A , n))
          (step1*
            (head (Γ , Δ ∷ (A , n)))
            H
            T
            D
            pG
            pHTD
            (headMerging
              Γ
              (Δ ∷ (A , n))
              T
              D
              n₁))))
  step1* .(head (Γ , (Δ ∷ (-S A , n)))) H T D (minus-R-head Γ Δ A n pG) pHTD (headMerging .Γ  .(Δ ∷ (-S A , n)) .T .D n₁)  = 
    seq-exchange
      H
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (-S A , n))
      (union (Δ ∷ (-S A , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (-S A , n)))
      (minus-R
        H
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        n
        (seq-exchange
          H
          (union (Γ ∷ (A , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (A , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (exchangeUnionLast
            Γ
            (copy T n₁)
            (A , n))
          idLE
          (step1*
            (head (Γ ∷ (A , n) , Δ))
            H
            T
            D
            pG
            pHTD
            (headMerging
              (Γ ∷ (A , n))
              Δ
              T
              D
              n₁))))
  step1* .(head ((Γ ∷ (A ⊔S B , n)) , Δ)) H T D (max-L-head Γ Δ A B n pG pG₁) pHTD (headMerging .(Γ ∷ (A ⊔S B , n)) .Δ .T .D n₁) = 
    seq-exchange
      H
      ((union Γ (copy T n₁)) ∷ (A ⊔S B , n))
      (union (Γ ∷ (A ⊔S B , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (A ⊔S B , n)))
      idLE
      (max-L
        H
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange
          H
          (union (Γ ∷ (A , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (A , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (exchangeUnionLast
            Γ
            (copy T n₁)
            (A , n))
          idLE
          (step1*
            (head (Γ ∷ (A , n) , Δ))
            H
            T
            D
            pG
            pHTD
            (headMerging
              (Γ ∷ (A , n))
              Δ
              T
              D
              n₁)))
        (seq-exchange
          H
          (union (Γ ∷ (B , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (B , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (exchangeUnionLast
            Γ
            (copy T n₁)
            (B , n))
          idLE
          (step1*
            (head (Γ ∷ (B , n) , Δ))
            H
            T
            D
            pG₁
            pHTD
            (headMerging
              (Γ ∷ (B , n))
              Δ
              T
              D
              n₁))))
  step1* .(head (Γ , (Δ ∷ (A ⊔S B , n)))) H T D (max-R-head Γ Δ A B n pG) pHTD (headMerging .Γ .(Δ ∷ (A ⊔S B , n)) .T .D n₁) = 
    seq-exchange
      H
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (A ⊔S B , n))
      (union (Δ ∷ (A ⊔S B , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (A ⊔S B , n)))
      (max-R
        H
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (hseq-exchange
          (H ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (A , n))))
          (H ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (A , n))) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))))
          (exHE
            idHE)
          (seq-exchange
            (H ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁)) ∷ (B , n)))
            (union Γ (copy T n₁))
            (union Γ (copy T n₁))
            (union (Δ ∷ (A , n)) (copy D n₁))
            ((union Δ (copy D n₁)) ∷ (A , n))
            idLE
            (exchangeUnionLast
              Δ
              (copy D n₁)
              (A , n))
            (hseq-exchange
              (H ∣ (union Γ (copy T n₁) , union (Δ ∷ (A , n)) (copy D n₁)) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))))
              (H ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))) ∣ (union Γ (copy T n₁) , union (Δ ∷ (A , n)) (copy D n₁)))
              (exHE
                idHE)
              (seq-exchange
                (H ∣ (union Γ (copy T n₁) , union (Δ ∷ (A , n)) (copy D n₁)))
                (union Γ (copy T n₁))
                (union Γ (copy T n₁))
                (union (Δ ∷ (B , n)) (copy D n₁))
                ((union Δ (copy D n₁)) ∷ (B , n))
                idLE
                (exchangeUnionLast
                  Δ
                  (copy D n₁)
                  (B , n))
                (step1*
                  (head (Γ , Δ ∷ (A , n)) ∣ (Γ , Δ ∷ (B , n)))
                  H
                  T
                  D
                  pG
                  pHTD
                  (consMerging
                    (head (Γ , (Δ ∷ (A , n))))
                    Γ
                    (Δ ∷ (B , n))
                    T
                    D
                    n₁
                    (headMerging
                      Γ
                      (Δ ∷ (A , n))
                      T
                      D
                      n₁))))))))
  step1* .(head (Γ , (Δ ∷ (A ⊓S B , n)))) H T D (min-R-head Γ Δ A B n pG pG₁) pHTD (headMerging .Γ .(Δ ∷ (A ⊓S B , n)) .T .D n₁) = 
    seq-exchange
      H
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (A ⊓S B , n))
      (union (Δ ∷ (A ⊓S B , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (A ⊓S B , n)))
      (min-R
        H
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange
          H
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (A , n)) (copy D n₁))
          ((union Δ (copy D n₁)) ∷ (A , n))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n₁)
            (A , n))
          (step1*
            (head (Γ , Δ ∷ (A , n)))
            H
            T
            D
            pG
            pHTD
            (headMerging
              Γ
              (Δ ∷ (A , n))
              T
              D
              n₁)))
        (seq-exchange
          H
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (B , n)) (copy D n₁))
          ((union Δ (copy D n₁)) ∷ (B , n))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n₁)
            (B , n))
          (step1*
            (head (Γ , Δ ∷ (B , n)))
            H
            T
            D
            pG₁
            pHTD
            (headMerging
              Γ
              (Δ ∷ (B , n))
              T
              D
              n₁))))
  step1* .(head ((Γ ∷ (A ⊓S B , n)) , Δ)) H T D (min-L-head Γ Δ A B n pG) pHTD (headMerging .(Γ ∷ (A ⊓S B , n)) .Δ .T .D n₁) = 
    seq-exchange
      H
      ((union Γ (copy T n₁)) ∷ (A ⊓S B , n))
      (union (Γ ∷ (A ⊓S B , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (A ⊓S B , n)))
      idLE
      (min-L
        H
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (hseq-exchange
          (H ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)) ∣ ((union Γ (copy T n₁) ∷ (A , n)) , union Δ (copy D n₁)))
          (H ∣ ((union Γ (copy T n₁) ∷ (A , n)) , union Δ (copy D n₁)) ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)))
          (exHE
            idHE)
          (seq-exchange
            (H ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)))
            (union (Γ ∷ (A , n)) (copy T n₁))
            ((union Γ (copy T n₁)) ∷ (A , n))
            (union Δ (copy D n₁))
            (union Δ (copy D n₁))
            (exchangeUnionLast
              Γ
              (copy T n₁)
              (A , n))
            idLE
            (hseq-exchange
              (H ∣ (union (Γ ∷ (A , n)) (copy T n₁) , union Δ (copy D n₁)) ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)))
              (H ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)) ∣ (union (Γ ∷ (A , n)) (copy T n₁) , union Δ (copy D n₁)))
              (exHE
                idHE)
              (seq-exchange
                (H ∣ (union (Γ ∷ (A , n)) (copy T n₁) , union Δ (copy D n₁)))
                (union (Γ ∷ (B , n)) (copy T n₁))
                ((union Γ (copy T n₁)) ∷ (B , n))
                (union Δ (copy D n₁))
                (union Δ (copy D n₁))
                (exchangeUnionLast
                  Γ
                  (copy T n₁)
                  (B , n))
                idLE
                (step1*
                  (head (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ))
                  H
                  T
                  D
                  pG
                  pHTD
                  (consMerging
                    (head (Γ ∷ (A , n) , Δ))
                    (Γ ∷ (B , n))
                    Δ
                    T
                    D
                    n₁
                    (headMerging
                      (Γ ∷ (A , n))
                      Δ
                      T
                      D
                      n₁))))))))
  step1* .(head (Γ , (Δ ∷ (one , suc k)))) H T D (◆1-rule Γ Δ ◆Γ ◆Δ refl refl k pG) pHTD (headMerging .Γ .(Δ ∷ (one , suc k)) .T .D n) =
    leaf (H ∣ (union Γ (copy T n) , union (Δ ∷ (one , (suc k))) (copy D n)))
  step1* .(head (Γ , Δ)) H T D (◆-rule Γ Δ ◆Γ ◆Δ refl refl pG) pHTD (headMerging .Γ .Δ .T .D n) =
    leaf (H ∣ (union Γ (copy T n) , union Δ (copy D n)))
  step1* .(G ∣ (Γ' , Δ')) H T D (seq-exchange G Γ Γ' Δ Δ' x x₁ pG) pHTD (consMerging .G .Γ' .Δ' .T .D n m) =
    seq-exchange
      (unionLHSeq H (merge G T D m))
      (union Γ (copy T n))
      (union Γ' (copy T n))
      (union Δ (copy D n))
      (union Δ' (copy D n))
      (unionKeepExchangeLeft
        x
        (copy T n))
      (unionKeepExchangeLeft
        x₁
        (copy D n))
      (step1*
        (G ∣ (Γ , Δ))
        H
        T
        D
        pG
        pHTD
        (consMerging
          G
          Γ
          Δ
          T
          D
          n
          m))
  step1* .(head (Γ' , Δ')) H T D (seq-exchange-head Γ Γ' Δ Δ' x x₁ pG) pHTD (headMerging .Γ' .Δ' .T .D n) = 
    seq-exchange
      H
      (union Γ (copy T n))
      (union Γ' (copy T n))
      (union Δ (copy D n))
      (union Δ' (copy D n))
      (unionKeepExchangeLeft
        x
        (copy T n))
      (unionKeepExchangeLeft
        x₁
        (copy D n))
      (step1*
        (head (Γ , Δ))
        H
        T
        D
        pG
        pHTD
        (headMerging
          Γ
          Δ
          T
          D
          n))
  step1* G H T D (hseq-exchange G₁ .G x pG) pHTD m =
    hseq-exchange
      (unionLHSeq H (merge G₁ T D (MergingExchange G G₁ T D m (LHSeqExchangeSym x))))
      (unionLHSeq H (merge G T D m))
      (unionKeepLHSeqExchangeRight
        H
        (LHSeqExchangeSym
          (mergeExchange
            G
            G₁
            T
            D
            m
            (LHSeqExchangeSym x))))
      (step1*
        G₁
        H
        T
        D
        pG
        pHTD
        (MergingExchange G G₁ T D m (LHSeqExchangeSym x)))
  step1* .(G ∣ (Γ , Δ ∷ (one , k))) H T D (1-rule G Γ Δ k pG) pHTD (consMerging .G .Γ .(Δ ∷ (one , k)) .T .D n m) = 
    seq-exchange
      (unionLHSeq H (merge G T D m))
      (union Γ (copy T n))
      (union Γ (copy T n))
      (union Δ (copy D n) ∷ (one , k))
      (union (Δ ∷ (one , k)) (copy D n))
      idLE
      (ListExchangeSym (exchangeUnionLast Δ (copy D n) (one , k)))
      (1-rule
        (unionLHSeq H (merge G T D m))
        (union Γ (copy T n))
        (union Δ (copy D n))
        k
        (step1* (G ∣ (Γ , Δ)) H T D pG pHTD (consMerging G Γ Δ T D n m)))
  step1* .(head (Γ , Δ ∷ (one , k))) H T D (1-rule-head Γ Δ k pG) pHTD (headMerging .Γ .(Δ ∷ (one , k)) .T .D n) = 
    seq-exchange
      H
      (union Γ (copy T n))
      (union Γ (copy T n))
      (union Δ (copy D n) ∷ (one , k))
      (union (Δ ∷ (one , k)) (copy D n))
      idLE
      (ListExchangeSym (exchangeUnionLast Δ (copy D n) (one , k)))
      (1-rule
        H
        (union Γ (copy T n))
        (union Δ (copy D n))
        k
        (step1* (head (Γ , Δ)) H T D pG pHTD (headMerging Γ Δ T D n)))
--}}}


  step1*-head :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    MGA-SR†* G ->
    MGA-SR†* (head (T , D)) ->
    (m : Merging G T D) ->
    Preproof* (merge G T D m)
--{{{
  step1*-head .(head ([] , [])) T D ax pHTD (headMerging .[] .[] .T .D n) =
    Preproof*Cong
      {head (copy T n , copy D n)}
      (proofToPreproof*
        (PumpingLemma-head (T , D) n pHTD))
      (cong₂
        (λ x y -> head (x , y))
        (sym (union[]T=T (copy T n)))
        (sym (union[]T=T (copy D n))))
  step1*-head .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) T D (W G Γ1 Γ2 Δ1 Δ2 pG) pHTD (consMerging .(G ∣ (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (consMerging .G .Γ1 .Δ1 .T .D n₁ m)) =
    W
      (merge G T D m)
      (union Γ1 (copy T n₁))
      (union Γ2 (copy T n))
      (union Δ1 (copy D n₁))
      (union Δ2 (copy D n))
      (step1*-head
        (G ∣ (Γ1 , Δ1))
        T
        D
        pG
        pHTD
        (consMerging G Γ1 Δ1 T D n₁ m))
  step1*-head .(G ∣ (Γ , Δ)) T D (C G Γ Δ pG) pHTD (consMerging .G .Γ .Δ .T .D n m) =
    C(merge G T D m)
      (union Γ (copy T n))
      (union Δ (copy D n))
      (step1*-head
        (G ∣ (Γ , Δ) ∣ (Γ , Δ))
        T
        D
        pG
        pHTD
        (consMerging (G ∣ (Γ , Δ)) Γ Δ T D n (consMerging G Γ Δ T D n m)))
  step1*-head .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) T D (S G Γ1 Γ2 Δ1 Δ2 refl refl pG) pHTD (consMerging .(G ∣ (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (consMerging .G .Γ1 .Δ1 .T .D n₁ m)) =
    S
      (merge G T D m)
      (union Γ1 (copy T n₁))
      (union Γ2 (copy T n))
      (union Δ1 (copy D n₁))
      (union Δ2 (copy D n))
      refl
      refl
      (seq-exchange
        (merge G T D m)
        (union (union Γ1 Γ2) (union (copy T n₁) (copy T n)))
        (union (union Γ1 (copy T n₁)) (union Γ2 (copy T n)))
        (union (union Δ1 Δ2) (union (copy D n₁) (copy D n)))
        (union (union Δ1 (copy D n₁)) (union Δ2 (copy D n)))
        (ListExchangeSym
          (transLE
            (union-assoc
              Γ1
              (copy T n₁)
              (union Γ2 (copy T n)))
            (transLE
              (unionKeepExchangeRight
                Γ1
                (transLE
                  (ListExchangeSym
                    (union-assoc
                      (copy T n₁)
                      Γ2
                      (copy T n)))
                  (transLE
                    (unionKeepExchangeLeft
                      (ListExchangeUnion
                        (copy T n₁)
                        Γ2)
                      (copy T n))
                    (union-assoc
                      Γ2
                      (copy T n₁)
                      (copy T n)))))
                (ListExchangeSym
                  (union-assoc
                    Γ1
                    Γ2
                    (union (copy T n₁) (copy T n))))))) 
        (ListExchangeSym
          (transLE
            (union-assoc
              Δ1
              (copy D n₁)
              (union Δ2 (copy D n)))
            (transLE
              (unionKeepExchangeRight
                Δ1
                (transLE
                  (ListExchangeSym
                    (union-assoc
                      (copy D n₁)
                      Δ2
                      (copy D n)))
                  (transLE
                    (unionKeepExchangeLeft
                      (ListExchangeUnion
                        (copy D n₁)
                        Δ2)
                      (copy D n))
                    (union-assoc
                      Δ2
                      (copy D n₁)
                      (copy D n)))))
                (ListExchangeSym
                  (union-assoc
                    Δ1
                    Δ2
                    (union (copy D n₁) (copy D n)))))))
        (unionCopy-L*
          (merge G T D m)
          (union Γ1 Γ2)
          T
          (union (union Δ1 Δ2) (union (copy D n₁) (copy D n)))
          n₁
          n
          (unionCopy-R*
            (merge G T D m)
            (union (union Γ1 Γ2) (copy T (n₁ + n)))
            (union Δ1 Δ2)
            D
            n₁
            n
            (step1*-head
              (G ∣ (union Γ1 Γ2 , union Δ1 Δ2))
              T
              D
              pG
              pHTD
              (consMerging
                G
                (union Γ1 Γ2)
                (union Δ1 Δ2)
                T
                D
                (n₁ + n)
                m)))))
  step1*-head .(G ∣ ((Γ ∷ (A , n')) , (Δ ∷ (A , n')))) T D (Id-rule G Γ Δ (A , n') pG) pHTD (consMerging .G .(Γ ∷ (A , n')) .(Δ ∷ (A , n')) .T .D n m) =
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n)) ∷ (A , n'))
      (union (Γ ∷ (A , n')) (copy T n))
      ((union Δ (copy D n)) ∷ (A , n'))
      (union (Δ ∷ (A , n')) (copy  D n))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n)
          (A , n')))
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n)
          (A , n')))
      (Id-rule
        (merge G T D m)
        (union Γ (copy T n))
        (union Δ (copy D n))
        (A , n')
        (step1*-head
          (G ∣ (Γ , Δ))
          T
          D
          pG
          pHTD
          (consMerging G Γ Δ T D n m)))
  step1*-head .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) T D (W-head Γ1 Γ2 Δ1 Δ2 pG) pHTD (consMerging .(head (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (headMerging .Γ1 .Δ1 .T .D n₁)) = 
    W-head
      (union Γ1 (copy T n₁))
      (union Γ2 (copy T n))
      (union Δ1 (copy D n₁))
      (union Δ2 (copy D n))
      (step1*-head
        (head (Γ1 , Δ1))
        T
        D
        pG
        pHTD
        (headMerging Γ1 Δ1 T D n₁))
  step1*-head .(head (Γ , Δ)) T D (C-head Γ Δ pG) pHTD (headMerging .Γ .Δ .T .D n) = 
    C-head
      (union Γ (copy T n))
      (union Δ (copy D n))
      (step1*-head
        (head (Γ , Δ) ∣ (Γ , Δ))
        T
        D
        pG
        pHTD
        (consMerging (head (Γ , Δ)) Γ Δ T D n (headMerging Γ Δ T D n)))
  step1*-head .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) T D (S-head Γ1 Γ2 Δ1 Δ2 refl refl pG) pHTD (consMerging .(head (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (headMerging .Γ1 .Δ1 .T .D n₁)) = 
    S-head
      (union Γ1 (copy T n₁))
      (union Γ2 (copy T n))
      (union Δ1 (copy D n₁))
      (union Δ2 (copy D n))
      refl
      refl
      (seq-exchange-head
        (union (union Γ1 Γ2) (union (copy T n₁) (copy T n)))
        (union (union Γ1 (copy T n₁)) (union Γ2 (copy T n)))
        (union (union Δ1 Δ2) (union (copy D n₁) (copy D n)))
        (union (union Δ1 (copy D n₁)) (union Δ2 (copy D n)))
        (ListExchangeSym
          (transLE
            (union-assoc
              Γ1
              (copy T n₁)
              (union Γ2 (copy T n)))
            (transLE
              (unionKeepExchangeRight
                Γ1
                (transLE
                  (ListExchangeSym
                    (union-assoc
                      (copy T n₁)
                      Γ2
                      (copy T n)))
                  (transLE
                    (unionKeepExchangeLeft
                      (ListExchangeUnion
                        (copy T n₁)
                        Γ2)
                      (copy T n))
                    (union-assoc
                      Γ2
                      (copy T n₁)
                      (copy T n)))))
                (ListExchangeSym
                  (union-assoc
                    Γ1
                    Γ2
                    (union (copy T n₁) (copy T n))))))) 
        (ListExchangeSym
          (transLE
            (union-assoc
              Δ1
              (copy D n₁)
              (union Δ2 (copy D n)))
            (transLE
              (unionKeepExchangeRight
                Δ1
                (transLE
                  (ListExchangeSym
                    (union-assoc
                      (copy D n₁)
                      Δ2
                      (copy D n)))
                  (transLE
                    (unionKeepExchangeLeft
                      (ListExchangeUnion
                        (copy D n₁)
                        Δ2)
                      (copy D n))
                    (union-assoc
                      Δ2
                      (copy D n₁)
                      (copy D n)))))
                (ListExchangeSym
                  (union-assoc
                    Δ1
                    Δ2
                    (union (copy D n₁) (copy D n)))))))
        (unionCopy-L*-head
          (union Γ1 Γ2)
          T
          (union (union Δ1 Δ2) (union (copy D n₁) (copy D n)))
          n₁
          n
          (unionCopy-R*-head
            (union (union Γ1 Γ2) (copy T (n₁ + n)))
            (union Δ1 Δ2)
            D
            n₁
            n
            (step1*-head
              (head (union Γ1 Γ2 , union Δ1 Δ2))
              T
              D
              pG
              pHTD
              (headMerging
                (union Γ1 Γ2)
                (union Δ1 Δ2)
                T
                D
                (n₁ + n))))))
  step1*-head .(head ((Γ ∷ (A , n')) , (Δ ∷ (A , n')))) T D (Id-rule-head Γ Δ (A , n') pG) pHTD (headMerging .(Γ ∷ (A , n')) .(Δ ∷ (A , n')) .T .D n) = 
    seq-exchange-head
      ((union Γ (copy T n)) ∷ (A , n'))
      (union (Γ ∷ (A , n')) (copy T n))
      ((union Δ (copy D n)) ∷ (A , n'))
      (union (Δ ∷ (A , n')) (copy  D n))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n)
          (A , n')))
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n)
          (A , n')))
      (Id-rule-head
        (union Γ (copy T n))
        (union Δ (copy D n))
        (A , n')
        (step1*-head
          (head (Γ , Δ))
          T
          D
          pG
          pHTD
          (headMerging Γ Δ T D n)))
  step1*-head .(G ∣ ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ)) T D (U-L G Γ Δ A n1 n2 refl pG) pHTD (consMerging .G .(Γ ∷ (A , n1) ∷ (A , n2)) .Δ .T .D n m) = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n)) ∷ (A , n1) ∷ (A , n2))
      (union (Γ ∷ (A , n1) ∷ (A , n2)) (copy T n))
      ((union Δ (copy D n)))
      (union Δ (copy  D n))
      (ListExchangeSym
        (transLE
          (exchangeUnionLast
            (Γ ∷ (A , n1))
            (copy T n)
            (A , n2))
          (indLE
            (exchangeUnionLast
              Γ
              (copy T n)
              (A , n1)))))
      idLE
      (U-L
        (merge G T D m)
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange
          (merge G T D m)
          (union (Γ ∷ (A , n1 + n2)) (copy T n))
          ((union Γ (copy T n)) ∷ (A , n1 + n2))
          (union Δ (copy D n))
          (union Δ (copy D n))
          (exchangeUnionLast
            Γ
            (copy T n)
            (A , n1 + n2))
          idLE
          (step1*-head
            (G ∣ (Γ ∷ (A , n1 + n2) , Δ))
            T
            D
            pG
            pHTD
            (consMerging
              G
              (Γ ∷ (A , n1 + n2))
              Δ
              T
              D
              n
              m))))
  step1*-head .(G ∣ (Γ , (Δ ∷ (A , n1) ∷ (A , n2)))) T D (U-R G Γ Δ A n1 n2 refl pG) pHTD (consMerging G Γ (Δ ∷ (A , n1) ∷ (A , n2)) T D n m) = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n)))
      (union Γ (copy  T n))
      ((union Δ (copy D n)) ∷ (A , n1) ∷ (A , n2))
      (union (Δ ∷ (A , n1) ∷ (A , n2)) (copy D n))
      idLE
      (ListExchangeSym
        (transLE
          (exchangeUnionLast
            (Δ ∷ (A , n1))
            (copy D n)
            (A , n2))
          (indLE
            (exchangeUnionLast
              Δ
              (copy D n)
              (A , n1)))))
      (U-R
        (merge G T D m)
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange
          (merge G T D m)
          (union Γ (copy T n))
          (union Γ (copy T n))
          (union (Δ ∷ (A , n1 + n2)) (copy D n))
          ((union Δ (copy D n)) ∷ (A , n1 + n2))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n)
            (A , n1 + n2))
          (step1*-head
            (G ∣ (Γ , Δ ∷ (A , n1 + n2)))
            T
            D
            pG
            pHTD
            (consMerging
              G
              Γ
              (Δ ∷ (A , n1 + n2))
              T
              D
              n
              m))))
  step1*-head .(G ∣ ((Γ ∷ (A , n1 + n2)) , Δ)) T D (F-L G Γ Δ A n1 n2 refl pG) pHTD (consMerging .G .(Γ ∷ (A , n1 + n2)) .Δ .T .D n m) = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n)) ∷ (A , n1 + n2))
      (union (Γ ∷ (A , n1 + n2)) (copy T n))
      ((union Δ (copy D n)))
      (union Δ (copy  D n))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n)
          (A , n1 + n2)))
      idLE
      (F-L
        (merge G T D m)
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange
          (merge G T D m)
          (union (Γ ∷ (A , n1) ∷ (A , n2)) (copy T n))
          ((union Γ (copy T n)) ∷ (A , n1) ∷ (A , n2))
          (union Δ (copy D n))
          (union Δ (copy D n))
          (transLE
            (exchangeUnionLast
              (Γ ∷ (A , n1))
              (copy T n)
              (A , n2))
            (indLE
              (exchangeUnionLast
                Γ
                (copy T n)
                (A , n1))))
          idLE
          (step1*-head
            (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
            T
            D
            pG
            pHTD
            (consMerging
              G
              (Γ ∷ (A , n1) ∷ (A , n2))
              Δ
              T
              D
              n
              m))))
  step1*-head .(G ∣ (Γ , (Δ ∷ (A , n1 + n2)))) T D (F-R G Γ Δ A n1 n2 refl pG) pHTD (consMerging .G .Γ .(Δ ∷ (A , n1 + n2)) .T .D n m) = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n)))
      (union Γ (copy  T n))
      ((union Δ (copy D n)) ∷ (A , n1 + n2))
      (union (Δ ∷ (A , n1 + n2)) (copy D n))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n)
          (A , n1 + n2)))
      (F-R
        (merge G T D m)
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange
          (merge G T D m)
          (union Γ (copy T n))
          (union Γ (copy T n))
          (union (Δ ∷ (A , n1) ∷ (A , n2)) (copy D n))
          ((union Δ (copy D n)) ∷ (A , n1) ∷ (A , n2))
          idLE
          (transLE
            (exchangeUnionLast
              (Δ ∷ (A , n1))
              (copy D n)
              (A , n2))
            (indLE
              (exchangeUnionLast
                Δ
                (copy D n)
                (A , n1))))
          (step1*-head
            (G ∣ (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
            T
            D
            pG
            pHTD
            (consMerging
              G
              Γ
              (Δ ∷ (A , n1) ∷ (A , n2))
              T
              D
              n
              m))))
  step1*-head .(head ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ)) T D (U-L-head Γ Δ A n1 n2 refl pG) pHTD (headMerging .(Γ ∷ (A , n1) ∷ (A , n2)) .Δ .T .D n) = 
    seq-exchange-head
      ((union Γ (copy T n)) ∷ (A , n1) ∷ (A , n2))
      (union (Γ ∷ (A , n1) ∷ (A , n2)) (copy T n))
      ((union Δ (copy D n)))
      (union Δ (copy  D n))
      (ListExchangeSym
        (transLE
          (exchangeUnionLast
            (Γ ∷ (A , n1))
            (copy T n)
            (A , n2))
          (indLE
            (exchangeUnionLast
              Γ
              (copy T n)
              (A , n1)))))
      idLE
      (U-L-head
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange-head
          (union (Γ ∷ (A , n1 + n2)) (copy T n))
          ((union Γ (copy T n)) ∷ (A , n1 + n2))
          (union Δ (copy D n))
          (union Δ (copy D n))
          (exchangeUnionLast
            Γ
            (copy T n)
            (A , n1 + n2))
          idLE
          (step1*-head
            (head (Γ ∷ (A , n1 + n2) , Δ))
            T
            D
            pG
            pHTD
            (headMerging
              (Γ ∷ (A , n1 + n2))
              Δ
              T
              D
              n))))
  step1*-head .(head (Γ , (Δ ∷ (A , n1) ∷ (A , n2)))) T D (U-R-head Γ Δ A n1 n2 refl pG) pHTD (headMerging .Γ .(Δ ∷ (A , n1) ∷ (A , n2)) .T .D n) = 
    seq-exchange-head
      ((union Γ (copy T n)))
      (union Γ (copy  T n))
      ((union Δ (copy D n)) ∷ (A , n1) ∷ (A , n2))
      (union (Δ ∷ (A , n1) ∷ (A , n2)) (copy D n))
      idLE
      (ListExchangeSym
        (transLE
          (exchangeUnionLast
            (Δ ∷ (A , n1))
            (copy D n)
            (A , n2))
          (indLE
            (exchangeUnionLast
              Δ
              (copy D n)
              (A , n1)))))
      (U-R-head
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange-head
          (union Γ (copy T n))
          (union Γ (copy T n))
          (union (Δ ∷ (A , n1 + n2)) (copy D n))
          ((union Δ (copy D n)) ∷ (A , n1 + n2))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n)
            (A , n1 + n2))
          (step1*-head
            (head (Γ , Δ ∷ (A , n1 + n2)))
            T
            D
            pG
            pHTD
            (headMerging
              Γ
              (Δ ∷ (A , n1 + n2))
              T
              D
              n))))
  step1*-head .(head ((Γ ∷ (A , n1 + n2)) , Δ)) T D (F-L-head Γ Δ A n1 n2 refl pG) pHTD (headMerging .(Γ ∷ (A , n1 + n2)) .Δ .T .D n) = 
    seq-exchange-head
      ((union Γ (copy T n)) ∷ (A , n1 + n2))
      (union (Γ ∷ (A , n1 + n2)) (copy T n))
      ((union Δ (copy D n)))
      (union Δ (copy  D n))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n)
          (A , n1 + n2)))
      idLE
      (F-L-head
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange-head
          (union (Γ ∷ (A , n1) ∷ (A , n2)) (copy T n))
          ((union Γ (copy T n)) ∷ (A , n1) ∷ (A , n2))
          (union Δ (copy D n))
          (union Δ (copy D n))
          (transLE
            (exchangeUnionLast
              (Γ ∷ (A , n1))
              (copy T n)
              (A , n2))
            (indLE
              (exchangeUnionLast
                Γ
                (copy T n)
                (A , n1))))
          idLE
          (step1*-head
            (head (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
            T
            D
            pG
            pHTD
            (headMerging
              (Γ ∷ (A , n1) ∷ (A , n2))
              Δ
              T
              D
              n))))
  step1*-head .(head (Γ , (Δ ∷ (A , n1 + n2)))) T D (F-R-head Γ Δ A n1 n2 refl pG) pHTD (headMerging .Γ .(Δ ∷ (A , n1 + n2)) .T .D n) = 
    seq-exchange-head
      ((union Γ (copy T n)))
      (union Γ (copy  T n))
      ((union Δ (copy D n)) ∷ (A , n1 + n2))
      (union (Δ ∷ (A , n1 + n2)) (copy D n))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n)
          (A , n1 + n2)))
      (F-R-head
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        n1
        n2
        refl
        (seq-exchange-head
          (union Γ (copy T n))
          (union Γ (copy T n))
          (union (Δ ∷ (A , n1) ∷ (A , n2)) (copy D n))
          ((union Δ (copy D n)) ∷ (A , n1) ∷ (A , n2))
          idLE
          (transLE
            (exchangeUnionLast
              (Δ ∷ (A , n1))
              (copy D n)
              (A , n2))
            (indLE
              (exchangeUnionLast
                Δ
                (copy D n)
                (A , n1))))
          (step1*-head
            (head (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
            T
            D
            pG
            pHTD
            (headMerging
              Γ
              (Δ ∷ (A , n1) ∷ (A , n2))
              T
              D
              n))))
  step1*-head .(G ∣ ((Γ ∷ (A , 0)) , Δ)) T D (E-L G Γ Δ A pG) pHTD (consMerging .G .(Γ ∷ (A , 0)) .Δ .T .D n m) =  
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n)) ∷ (A , 0))
      (union (Γ ∷ (A , 0)) (copy T n))
      ((union Δ (copy D n)))
      (union Δ (copy  D n))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n)
          (A , 0)))
      idLE
      (E-L
        (merge G T D m)
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        (step1*-head
          (G ∣ (Γ , Δ))
          T
          D
          pG
          pHTD
          (consMerging
            G
            Γ
            Δ
            T
            D
            n
            m)))
  step1*-head .(G ∣ (Γ , (Δ ∷ (A , 0)))) T D (E-R G Γ Δ A pG) pHTD (consMerging .G .Γ .(Δ ∷ (A , 0)) .T .D n m) = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n)))
      (union Γ (copy  T n))
      ((union Δ (copy D n)) ∷ (A , 0))
      (union (Δ ∷ (A , 0)) (copy D n))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n)
          (A , 0)))
      (E-R
        (merge G T D m)
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        (step1*-head
          (G ∣ (Γ , Δ))
          T
          D
          pG
          pHTD
          (consMerging
            G
            Γ
            Δ
            T
            D
            n
            m)))
  step1*-head .(head ((Γ ∷ (A , 0)) , Δ)) T D (E-L-head Γ Δ A pG) pHTD (headMerging .(Γ ∷ (A , 0)) .Δ .T .D n) = 
    seq-exchange-head
      ((union Γ (copy T n)) ∷ (A , 0))
      (union (Γ ∷ (A , 0)) (copy T n))
      ((union Δ (copy D n)))
      (union Δ (copy  D n))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n)
          (A , 0)))
      idLE
      (E-L-head
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        (step1*-head
          (head (Γ , Δ))
          T
          D
          pG
          pHTD
          (headMerging
            Γ
            Δ
            T
            D
            n)))
  step1*-head .(head (Γ , (Δ ∷ (A , 0)))) T D (E-R-head Γ Δ A pG) pHTD (headMerging .Γ .(Δ ∷ (A , 0)) .T .D n) = 
    seq-exchange-head
      ((union Γ (copy T n)))
      (union Γ (copy  T n))
      ((union Δ (copy D n)) ∷ (A , 0))
      (union (Δ ∷ (A , 0)) (copy D n))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n)
          (A , 0)))
      (E-R-head
        (union Γ (copy T n))
        (union Δ (copy D n))
        A
        (step1*-head
          (head (Γ , Δ))
          T
          D
          pG
          pHTD
          (headMerging
            Γ
            Δ
            T
            D
            n)))
  step1*-head .(G ∣ ((Γ ∷ (A +S B , n)) , Δ)) T D (plus-L G Γ Δ A B n pG) pHTD (consMerging .G .(Γ ∷ (A +S B , n)) .Δ .T .D n₁ m) = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n₁)) ∷ (A +S B , n))
      (union (Γ ∷ (A +S B , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (A +S B , n)))
      idLE
      (plus-L
        (merge G T D m)
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange
          (merge G T D m)
          (union (Γ ∷ (A , n) ∷ (B , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (A , n) ∷ (B , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (transLE
            (exchangeUnionLast
              (Γ ∷ (A , n))
              (copy T n₁)
              (B , n))
            (indLE
              (exchangeUnionLast
                Γ
                (copy T n₁)
                (A , n))))
          idLE
          (step1*-head
            (G ∣ (Γ ∷ (A , n) ∷ (B , n) , Δ))
            T
            D
            pG
            pHTD
            (consMerging
              G
              (Γ ∷ (A , n) ∷ (B , n))
              Δ
              T
              D
              n₁
              m))))
  step1*-head .(G ∣ (Γ , (Δ ∷ (A +S B , n)))) T D (plus-R G Γ Δ A B n pG) pHTD (consMerging .G .Γ  .(Δ ∷ (A +S B , n)) .T .D n₁ m)  = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (A +S B , n))
      (union (Δ ∷ (A +S B , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (A +S B , n)))
      (plus-R
        (merge G T D m)
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange
          (merge G T D m)
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (A , n) ∷ (B , n)) (copy D n₁))
          ((union Δ (copy D n₁)) ∷ (A , n) ∷ (B , n))
          idLE
          (transLE
            (exchangeUnionLast
              (Δ ∷ (A , n))
              (copy D n₁)
              (B , n))
            (indLE
              (exchangeUnionLast
                Δ
                (copy D n₁)
                (A , n))))
          (step1*-head
            (G ∣ (Γ , Δ ∷ (A , n) ∷ (B , n)))
            T
            D
            pG
            pHTD
            (consMerging
              G
              Γ
              (Δ ∷ (A , n) ∷ (B , n))
              T
              D
              n₁
              m))))
  step1*-head .(G ∣ ((Γ ∷ (A ⊔S B , n)) , Δ)) T D (max-L G Γ Δ A B n pG pG₁) pHTD (consMerging .G .(Γ ∷ (A ⊔S B , n)) .Δ .T .D n₁ m) = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n₁)) ∷ (A ⊔S B , n))
      (union (Γ ∷ (A ⊔S B , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (A ⊔S B , n)))
      idLE
      (max-L
        (merge G T D m)
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange
          (merge G T D m)
          (union (Γ ∷ (A , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (A , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (exchangeUnionLast
            Γ
            (copy T n₁)
            (A , n))
          idLE
          (step1*-head
            (G ∣ (Γ ∷ (A , n) , Δ))
            T
            D
            pG
            pHTD
            (consMerging
              G
              (Γ ∷ (A , n))
              Δ
              T
              D
              n₁
              m)))
        (seq-exchange
          (merge G T D m)
          (union (Γ ∷ (B , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (B , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (exchangeUnionLast
            Γ
            (copy T n₁)
            (B , n))
          idLE
          (step1*-head
            (G ∣ (Γ ∷ (B , n) , Δ))
            T
            D
            pG₁
            pHTD
            (consMerging
              G
              (Γ ∷ (B , n))
              Δ
              T
              D
              n₁
              m))))
  step1*-head .(G ∣ (Γ , (Δ ∷ (A ⊔S B , n)))) T D (max-R G Γ Δ A B n pG) pHTD (consMerging .G .Γ .(Δ ∷ (A ⊔S B , n)) .T .D n₁ m) = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (A ⊔S B , n))
      (union (Δ ∷ (A ⊔S B , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (A ⊔S B , n)))
      (max-R
        (merge G T D m)
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (hseq-exchange
          (merge G T D m ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (A , n))))
          (merge G T D m ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (A , n))) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))))
          (exHE
            idHE)
          (seq-exchange
            (merge G T D m ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁)) ∷ (B , n)))
            (union Γ (copy T n₁))
            (union Γ (copy T n₁))
            (union (Δ ∷ (A , n)) (copy D n₁))
            ((union Δ (copy D n₁)) ∷ (A , n))
            idLE
            (exchangeUnionLast
              Δ
              (copy D n₁)
              (A , n))
            (hseq-exchange
              (merge G T D m ∣ (union Γ (copy T n₁) , union (Δ ∷ (A , n)) (copy D n₁)) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))))
              (merge G T D m ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))) ∣ (union Γ (copy T n₁) , union (Δ ∷ (A , n)) (copy D n₁)))
              (exHE
                idHE)
              (seq-exchange
                (merge G T D m ∣ (union Γ (copy T n₁) , union (Δ ∷ (A , n)) (copy D n₁)))
                (union Γ (copy T n₁))
                (union Γ (copy T n₁))
                (union (Δ ∷ (B , n)) (copy D n₁))
                ((union Δ (copy D n₁)) ∷ (B , n))
                idLE
                (exchangeUnionLast
                  Δ
                  (copy D n₁)
                  (B , n))
                (step1*-head
                  (G ∣ (Γ , Δ ∷ (A , n)) ∣ (Γ , Δ ∷ (B , n)))
                  T
                  D
                  pG
                  pHTD
                  (consMerging
                    (G ∣ (Γ , (Δ ∷ (A , n))))
                    Γ
                    (Δ ∷ (B , n))
                    T
                    D
                    n₁
                    (consMerging
                      G
                      Γ
                      (Δ ∷ (A , n))
                      T
                      D
                      n₁
                      m))))))))
  step1*-head .(head ((Γ ∷ (A +S B , n)) , Δ)) T D (plus-L-head Γ Δ A B n pG) pHTD (headMerging .(Γ ∷ (A +S B , n)) .Δ .T .D n₁) = 
    seq-exchange-head
      ((union Γ (copy T n₁)) ∷ (A +S B , n))
      (union (Γ ∷ (A +S B , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (A +S B , n)))
      idLE
      (plus-L-head
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange-head
          (union (Γ ∷ (A , n) ∷ (B , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (A , n) ∷ (B , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (transLE
            (exchangeUnionLast
              (Γ ∷ (A , n))
              (copy T n₁)
              (B , n))
            (indLE
              (exchangeUnionLast
                Γ
                (copy T n₁)
                (A , n))))
          idLE
          (step1*-head
            (head (Γ ∷ (A , n) ∷ (B , n) , Δ))
            T
            D
            pG
            pHTD
            (headMerging
              (Γ ∷ (A , n) ∷ (B , n))
              Δ
              T
              D
              n₁))))
  step1*-head .(head (Γ , (Δ ∷ (A +S B , n)))) T D (plus-R-head Γ Δ A B n pG) pHTD (headMerging .Γ .(Δ ∷ (A +S B , n)) .T .D n₁) = 
    seq-exchange-head
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (A +S B , n))
      (union (Δ ∷ (A +S B , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (A +S B , n)))
      (plus-R-head
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange-head
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (A , n) ∷ (B , n)) (copy D n₁))
          ((union Δ (copy D n₁)) ∷ (A , n) ∷ (B , n))
          idLE
          (transLE
            (exchangeUnionLast
              (Δ ∷ (A , n))
              (copy D n₁)
              (B , n))
            (indLE
              (exchangeUnionLast
                Δ
                (copy D n₁)
                (A , n))))
          (step1*-head
            (head (Γ , Δ ∷ (A , n) ∷ (B , n)))
            T
            D
            pG
            pHTD
            (headMerging
              Γ
              (Δ ∷ (A , n) ∷ (B , n))
              T
              D
              n₁))))
  step1*-head .(head ((Γ ∷ (A ⊔S B , n)) , Δ)) T D (max-L-head Γ Δ A B n pG pG₁) pHTD (headMerging .(Γ ∷ (A ⊔S B , n)) .Δ .T .D n₁) = 
    seq-exchange-head
      ((union Γ (copy T n₁)) ∷ (A ⊔S B , n))
      (union (Γ ∷ (A ⊔S B , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (A ⊔S B , n)))
      idLE
      (max-L-head
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange-head
          (union (Γ ∷ (A , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (A , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (exchangeUnionLast
            Γ
            (copy T n₁)
            (A , n))
          idLE
          (step1*-head
            (head (Γ ∷ (A , n) , Δ))
            T
            D
            pG
            pHTD
            (headMerging
              (Γ ∷ (A , n))
              Δ
              T
              D
              n₁)))
        (seq-exchange-head
          (union (Γ ∷ (B , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (B , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (exchangeUnionLast
            Γ
            (copy T n₁)
            (B , n))
          idLE
          (step1*-head
            (head (Γ ∷ (B , n) , Δ))
            T
            D
            pG₁
            pHTD
            (headMerging
              (Γ ∷ (B , n))
              Δ
              T
              D
              n₁))))
  step1*-head .(head (Γ , (Δ ∷ (A ⊔S B , n)))) T D (max-R-head Γ Δ A B n pG) pHTD (headMerging .Γ .(Δ ∷ (A ⊔S B , n)) .T .D n₁) = 
    seq-exchange-head
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (A ⊔S B , n))
      (union (Δ ∷ (A ⊔S B , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (A ⊔S B , n)))
      (max-R-head
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (hseq-exchange
          (head (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (A , n))))
          (head (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (A , n))) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))))
          exHE-head
          (seq-exchange
            (head (union Γ (copy T n₁) , (union Δ (copy D n₁)) ∷ (B , n)))
            (union Γ (copy T n₁))
            (union Γ (copy T n₁))
            (union (Δ ∷ (A , n)) (copy D n₁))
            ((union Δ (copy D n₁)) ∷ (A , n))
            idLE
            (exchangeUnionLast
              Δ
              (copy D n₁)
              (A , n))
            (hseq-exchange
              (head (union Γ (copy T n₁) , union (Δ ∷ (A , n)) (copy D n₁)) ∣ (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))))
              (head (union Γ (copy T n₁) , (union Δ (copy D n₁) ∷ (B , n))) ∣ (union Γ (copy T n₁) , union (Δ ∷ (A , n)) (copy D n₁)))
              exHE-head
              (seq-exchange
                (head (union Γ (copy T n₁) , union (Δ ∷ (A , n)) (copy D n₁)))
                (union Γ (copy T n₁))
                (union Γ (copy T n₁))
                (union (Δ ∷ (B , n)) (copy D n₁))
                ((union Δ (copy D n₁)) ∷ (B , n))
                idLE
                (exchangeUnionLast
                  Δ
                  (copy D n₁)
                  (B , n))
                (step1*-head
                  (head (Γ , Δ ∷ (A , n)) ∣ (Γ , Δ ∷ (B , n)))
                  T
                  D
                  pG
                  pHTD
                  (consMerging
                    (head (Γ , (Δ ∷ (A , n))))
                    Γ
                    (Δ ∷ (B , n))
                    T
                    D
                    n₁
                    (headMerging
                      Γ
                      (Δ ∷ (A , n))
                      T
                      D
                      n₁))))))))
  step1*-head .(head (Γ , (Δ ∷ (one , suc k)))) T D (◆1-rule Γ Δ ◆Γ ◆Δ refl refl k pG) pHTD (headMerging .Γ .(Δ ∷ (one , suc k)) .T .D n) =
    leaf (head (union Γ (copy T n) , union (Δ ∷ (one , suc k)) (copy D n)))
  step1*-head .(head (Γ , Δ)) T D (◆-rule Γ Δ ◆Γ ◆Δ refl refl pG) pHTD (headMerging .Γ .Δ .T .D n) =
    leaf (head (union Γ (copy T n) , union Δ (copy D n)))
  step1*-head .(G ∣ (Γ' , Δ')) T D (seq-exchange G Γ Γ' Δ Δ' x x₁ pG) pHTD (consMerging .G .Γ' .Δ' .T .D n m) =
    seq-exchange
      (merge G T D m)
      (union Γ (copy T n))
      (union Γ' (copy T n))
      (union Δ (copy D n))
      (union Δ' (copy D n))
      (unionKeepExchangeLeft
        x
        (copy T n))
      (unionKeepExchangeLeft
        x₁
        (copy D n))
      (step1*-head
        (G ∣ (Γ , Δ))
        T
        D
        pG
        pHTD
        (consMerging
          G
          Γ
          Δ
          T
          D
          n
          m))
  step1*-head .(head (Γ' , Δ')) T D (seq-exchange-head Γ Γ' Δ Δ' x x₁ pG) pHTD (headMerging .Γ' .Δ' .T .D n) = 
    seq-exchange-head
      (union Γ (copy T n))
      (union Γ' (copy T n))
      (union Δ (copy D n))
      (union Δ' (copy D n))
      (unionKeepExchangeLeft
        x
        (copy T n))
      (unionKeepExchangeLeft
        x₁
        (copy D n))
      (step1*-head
        (head (Γ , Δ))
        T
        D
        pG
        pHTD
        (headMerging
          Γ
          Δ
          T
          D
          n))
  step1*-head G T D (hseq-exchange G₁ .G x pG) pHTD m =
    hseq-exchange
      (merge G₁ T D (MergingExchange G G₁ T D m (LHSeqExchangeSym x)))
      (merge G T D m)
      (LHSeqExchangeSym
        (mergeExchange
          G
          G₁
          T
          D
          m
          (LHSeqExchangeSym x)))
      (step1*-head
        G₁
        T
        D
        pG
        pHTD
        (MergingExchange G G₁ T D m (LHSeqExchangeSym x)))
  step1*-head .(head ((Γ ∷ (botAG , n)) , Δ)) T D (Z-L-head Γ Δ n pG) pHTD (headMerging .(Γ ∷ (botAG , n)) .Δ .T .D n₁) = 
    seq-exchange-head
      ((union Γ (copy T n₁)) ∷ (botAG , n))
      (union (Γ ∷ (botAG , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (botAG , n)))
      idLE
      (Z-L-head
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        n
        (step1*-head
          (head (Γ , Δ))
          T
          D
          pG
          pHTD
          (headMerging
            Γ
            Δ
            T
            D
            n₁)))
  step1*-head .(head (Γ , (Δ ∷ (botAG , n)))) T D (Z-R-head Γ Δ n pG) pHTD (headMerging .Γ  .(Δ ∷ (botAG , n)) .T .D n₁)  = 
    seq-exchange-head
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (botAG , n))
      (union (Δ ∷ (botAG , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (botAG , n)))
      (Z-R-head
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        n
        (step1*-head
          (head (Γ , Δ))
          T
          D
          pG
          pHTD
          (headMerging
            Γ
            Δ
            T
            D
            n₁)))
  step1*-head .(head ((Γ ∷ (-S A , n)) , Δ)) T D (minus-L-head Γ Δ A n pG) pHTD (headMerging .(Γ ∷ (-S A , n)) .Δ .T .D n₁) = 
    seq-exchange-head
      ((union Γ (copy T n₁)) ∷ (-S A , n))
      (union (Γ ∷ (-S A , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (-S A , n)))
      idLE
      (minus-L-head
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        n
        (seq-exchange-head
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (A , n)) (copy D n₁))
          (union Δ (copy D n₁) ∷ (A , n))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n₁)
            (A , n))
          (step1*-head
            (head (Γ , Δ ∷ (A , n)))
            T
            D
            pG
            pHTD
            (headMerging
              Γ
              (Δ ∷ (A , n))
              T
              D
              n₁))))
  step1*-head .(head (Γ , (Δ ∷ (-S A , n)))) T D (minus-R-head Γ Δ A n pG) pHTD (headMerging .Γ  .(Δ ∷ (-S A , n)) .T .D n₁)  = 
    seq-exchange-head
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (-S A , n))
      (union (Δ ∷ (-S A , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (-S A , n)))
      (minus-R-head
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        n
        (seq-exchange-head
          (union (Γ ∷ (A , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (A , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (exchangeUnionLast
            Γ
            (copy T n₁)
            (A , n))
          idLE
          (step1*-head
            (head (Γ ∷ (A , n) , Δ))
            T
            D
            pG
            pHTD
            (headMerging
              (Γ ∷ (A , n))
              Δ
              T
              D
              n₁))))
  step1*-head .(head (Γ , (Δ ∷ (A ⊓S B , n)))) T D (min-R-head Γ Δ A B n pG pG₁) pHTD (headMerging .Γ .(Δ ∷ (A ⊓S B , n)) .T .D n₁) = 
    seq-exchange-head
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (A ⊓S B , n))
      (union (Δ ∷ (A ⊓S B , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (A ⊓S B , n)))
      (min-R-head
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange-head
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (A , n)) (copy D n₁))
          ((union Δ (copy D n₁)) ∷ (A , n))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n₁)
            (A , n))
          (step1*-head
            (head (Γ , Δ ∷ (A , n)))
            T
            D
            pG
            pHTD
            (headMerging
              Γ
              (Δ ∷ (A , n))
              T
              D
              n₁)))
        (seq-exchange-head
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (B , n)) (copy D n₁))
          ((union Δ (copy D n₁)) ∷ (B , n))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n₁)
            (B , n))
          (step1*-head
            (head (Γ , Δ ∷ (B , n)))
            T
            D
            pG₁
            pHTD
            (headMerging
              Γ
              (Δ ∷ (B , n))
              T
              D
              n₁))))
  step1*-head .(head ((Γ ∷ (A ⊓S B , n)) , Δ)) T D (min-L-head Γ Δ A B n pG) pHTD (headMerging .(Γ ∷ (A ⊓S B , n)) .Δ .T .D n₁) = 
    seq-exchange-head
      ((union Γ (copy T n₁)) ∷ (A ⊓S B , n))
      (union (Γ ∷ (A ⊓S B , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (A ⊓S B , n)))
      idLE
      (min-L-head
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (hseq-exchange
          (head ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)) ∣ ((union Γ (copy T n₁) ∷ (A , n)) , union Δ (copy D n₁)))
          (head ((union Γ (copy T n₁) ∷ (A , n)) , union Δ (copy D n₁)) ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)))
          exHE-head
          (seq-exchange
            (head ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)))
            (union (Γ ∷ (A , n)) (copy T n₁))
            ((union Γ (copy T n₁)) ∷ (A , n))
            (union Δ (copy D n₁))
            (union Δ (copy D n₁))
            (exchangeUnionLast
              Γ
              (copy T n₁)
              (A , n))
            idLE
            (hseq-exchange
              (head (union (Γ ∷ (A , n)) (copy T n₁) , union Δ (copy D n₁)) ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)))
              (head ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)) ∣ (union (Γ ∷ (A , n)) (copy T n₁) , union Δ (copy D n₁)))
              exHE-head
              (seq-exchange
                (head (union (Γ ∷ (A , n)) (copy T n₁) , union Δ (copy D n₁)))
                (union (Γ ∷ (B , n)) (copy T n₁))
                ((union Γ (copy T n₁)) ∷ (B , n))
                (union Δ (copy D n₁))
                (union Δ (copy D n₁))
                (exchangeUnionLast
                  Γ
                  (copy T n₁)
                  (B , n))
                idLE
                (step1*-head
                  (head (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ))
                  T
                  D
                  pG
                  pHTD
                  (consMerging
                    (head (Γ ∷ (A , n) , Δ))
                    (Γ ∷ (B , n))
                    Δ
                    T
                    D
                    n₁
                    (headMerging
                      (Γ ∷ (A , n))
                      Δ
                      T
                      D
                      n₁))))))))
  step1*-head .(G ∣ ((Γ ∷ (botAG , n)) , Δ)) T D (Z-L G Γ Δ n pG) pHTD (consMerging .G .(Γ ∷ (botAG , n)) .Δ .T .D n₁ m) = 
    seq-exchange(merge G T D m)
      ((union Γ (copy T n₁)) ∷ (botAG , n))
      (union (Γ ∷ (botAG , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (botAG , n)))
      idLE
      (Z-L
        (merge G T D m)
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        n
        (step1*-head
          (G ∣ (Γ , Δ))
          T
          D
          pG
          pHTD
          (consMerging
            G
            Γ
            Δ
            T
            D
            n₁
            m)))
  step1*-head .(G ∣ (Γ , (Δ ∷ (botAG , n)))) T D (Z-R G Γ Δ n pG) pHTD (consMerging .G .Γ  .(Δ ∷ (botAG , n)) .T .D n₁ m)  = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (botAG , n))
      (union (Δ ∷ (botAG , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (botAG , n)))
      (Z-R
        (merge G T D m)
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        n
        (step1*-head
          (G ∣ (Γ , Δ))
          T
          D
          pG
          pHTD
          (consMerging
            G
            Γ
            Δ
            T
            D
            n₁
            m)))
  step1*-head .(G ∣ ((Γ ∷ (-S A , n)) , Δ)) T D (minus-L G Γ Δ A n pG) pHTD (consMerging .G .(Γ ∷ (-S A , n)) .Δ .T .D n₁ m) = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n₁)) ∷ (-S A , n))
      (union (Γ ∷ (-S A , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (-S A , n)))
      idLE
      (minus-L
        (merge G T D m)
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        n
        (seq-exchange
          (merge G T D m)
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (A , n)) (copy D n₁))
          (union Δ (copy D n₁) ∷ (A , n))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n₁)
            (A , n))
          (step1*-head
            (G ∣ (Γ , Δ ∷ (A , n)))
            T
            D
            pG
            pHTD
            (consMerging
              G
              Γ
              (Δ ∷ (A , n))
              T
              D
              n₁
              m))))
  step1*-head .(G ∣ (Γ , (Δ ∷ (-S A , n)))) T D (minus-R G Γ Δ A n pG) pHTD (consMerging .G .Γ  .(Δ ∷ (-S A , n)) .T .D n₁ m)  = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (-S A , n))
      (union (Δ ∷ (-S A , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (-S A , n)))
      (minus-R
        (merge G T D m)
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        n
        (seq-exchange
          (merge G T D m)
          (union (Γ ∷ (A , n)) (copy T n₁))
          ((union Γ (copy T n₁)) ∷ (A , n))
          (union Δ (copy D n₁))
          (union Δ (copy D n₁))
          (exchangeUnionLast
            Γ
            (copy T n₁)
            (A , n))
          idLE
          (step1*-head
            (G ∣ (Γ ∷ (A , n) , Δ))
            T
            D
            pG
            pHTD
            (consMerging
              G
              (Γ ∷ (A , n))
              Δ
              T
              D
              n₁
              m))))
  step1*-head .(G ∣ (Γ , (Δ ∷ (A ⊓S B , n)))) T D (min-R G Γ Δ A B n pG pG₁) pHTD (consMerging .G .Γ .(Δ ∷ (A ⊓S B , n)) .T .D n₁ m) = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n₁)))
      (union Γ (copy  T n₁))
      ((union Δ (copy D n₁)) ∷ (A ⊓S B , n))
      (union (Δ ∷ (A ⊓S B , n)) (copy D n₁))
      idLE
      (ListExchangeSym
        (exchangeUnionLast
          Δ
          (copy D n₁)
          (A ⊓S B , n)))
      (min-R
        (merge G T D m)
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (seq-exchange
          (merge G T D m)
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (A , n)) (copy D n₁))
          ((union Δ (copy D n₁)) ∷ (A , n))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n₁)
            (A , n))
          (step1*-head
            (G ∣ (Γ , Δ ∷ (A , n)))
            T
            D
            pG
            pHTD
            (consMerging
              G
              Γ
              (Δ ∷ (A , n))
              T
              D
              n₁
              m)))
        (seq-exchange
          (merge G T D m)
          (union Γ (copy T n₁))
          (union Γ (copy T n₁))
          (union (Δ ∷ (B , n)) (copy D n₁))
          ((union Δ (copy D n₁)) ∷ (B , n))
          idLE
          (exchangeUnionLast
            Δ
            (copy D n₁)
            (B , n))
          (step1*-head
            (G ∣ (Γ , Δ ∷ (B , n)))
            T
            D
            pG₁
            pHTD
            (consMerging
              G
              Γ
              (Δ ∷ (B , n))
              T
              D
              n₁
              m))))
  step1*-head .(G ∣ ((Γ ∷ (A ⊓S B , n)) , Δ)) T D (min-L G Γ Δ A B n pG) pHTD (consMerging .G .(Γ ∷ (A ⊓S B , n)) .Δ .T .D n₁ m) = 
    seq-exchange
      (merge G T D m)
      ((union Γ (copy T n₁)) ∷ (A ⊓S B , n))
      (union (Γ ∷ (A ⊓S B , n)) (copy T n₁))
      ((union Δ (copy D n₁)))
      (union Δ (copy  D n₁))
      (ListExchangeSym
        (exchangeUnionLast
          Γ
          (copy T n₁)
          (A ⊓S B , n)))
      idLE
      (min-L
        (merge G T D m)
        (union Γ (copy T n₁))
        (union Δ (copy D n₁))
        A
        B
        n
        (hseq-exchange
          (merge G T D m ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)) ∣ ((union Γ (copy T n₁) ∷ (A , n)) , union Δ (copy D n₁)))
          (merge G T D m ∣ ((union Γ (copy T n₁) ∷ (A , n)) , union Δ (copy D n₁)) ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)))
          (exHE
            idHE)
          (seq-exchange
            (merge G T D m ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)))
            (union (Γ ∷ (A , n)) (copy T n₁))
            ((union Γ (copy T n₁)) ∷ (A , n))
            (union Δ (copy D n₁))
            (union Δ (copy D n₁))
            (exchangeUnionLast
              Γ
              (copy T n₁)
              (A , n))
            idLE
            (hseq-exchange
              (merge G T D m ∣ (union (Γ ∷ (A , n)) (copy T n₁) , union Δ (copy D n₁)) ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)))
              (merge G T D m ∣ ((union Γ (copy T n₁) ∷ (B , n)) , union Δ (copy D n₁)) ∣ (union (Γ ∷ (A , n)) (copy T n₁) , union Δ (copy D n₁)))
              (exHE
                idHE)
              (seq-exchange
                (merge G T D m ∣ (union (Γ ∷ (A , n)) (copy T n₁) , union Δ (copy D n₁)))
                (union (Γ ∷ (B , n)) (copy T n₁))
                ((union Γ (copy T n₁)) ∷ (B , n))
                (union Δ (copy D n₁))
                (union Δ (copy D n₁))
                (exchangeUnionLast
                  Γ
                  (copy T n₁)
                  (B , n))
                idLE
                (step1*-head
                  (G ∣ (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ))
                  T
                  D
                  pG
                  pHTD
                  (consMerging
                    (G ∣ (Γ ∷ (A , n) , Δ))
                    (Γ ∷ (B , n))
                    Δ
                    T
                    D
                    n₁
                    (consMerging
                      G
                      (Γ ∷ (A , n))
                      Δ
                      T
                      D
                      n₁
                      m))))))))
  step1*-head .(G ∣ (Γ , Δ ∷ (one , k))) T D (1-rule G Γ Δ k pG) pHTD (consMerging .G .Γ .(Δ ∷ (one , k)) .T .D n m) = 
    seq-exchange
      (merge G T D m)
      (union Γ (copy T n))
      (union Γ (copy T n))
      (union Δ (copy D n) ∷ (one , k))
      (union (Δ ∷ (one , k)) (copy D n))
      idLE
      (ListExchangeSym (exchangeUnionLast Δ (copy D n) (one , k)))
      (1-rule
        (merge G T D m)
        (union Γ (copy T n))
        (union Δ (copy D n))
        k
        (step1*-head (G ∣ (Γ , Δ)) T D pG pHTD (consMerging G Γ Δ T D n m)))
  step1*-head .(head (Γ , Δ ∷ (one , k))) T D (1-rule-head Γ Δ k pG) pHTD (headMerging .Γ .(Δ ∷ (one , k)) .T .D n) = 
    seq-exchange-head
      (union Γ (copy T n))
      (union Γ (copy T n))
      (union Δ (copy D n) ∷ (one , k))
      (union (Δ ∷ (one , k)) (copy D n))
      idLE
      (ListExchangeSym (exchangeUnionLast Δ (copy D n) (one , k)))
      (1-rule-head
        (union Γ (copy T n))
        (union Δ (copy D n))
        k
        (step1*-head (head (Γ , Δ)) T D pG pHTD (headMerging Γ Δ T D n)))
--}}}

  Propstep1* :
    (G H : LHSeq) ->
    (T D : ListLTerm) ->
    (pG : MGA-SR†* G) ->
    (pHTD : MGA-SR†* (H ∣ (T , D))) ->
    (n : ℕ) ->
    (◆pG≤n : #◆* pG ≤ n) ->
    (m : Merging G T D) ->
    propLeavesStep1* H T D n (leaves* (step1* G H T D pG pHTD m))
--{{{
  Propstep1* .(head ([] , [])) H T D ax pHTD n' ◆pG≤n (headMerging .[] .[] .T .D n) =
    congPropLeavesStep1*
      ([]P1 H T D n')
      (sym
        (trans
          (congKeepLeaves*
            (proofToPreproof* (PumpingLemma H (T , D) n pHTD))
            (cong₂
              (λ x y -> H ∣ (x , y))
              (sym (union[]T=T (copy T n)))
              (sym (union[]T=T (copy D n)))))
          (leavesMGA-SR†*
            (PumpingLemma H (T , D) n pHTD))))
  Propstep1* .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) H T D (W G Γ1 Γ2 Δ1 Δ2 pG) pHTD n' ◆pG≤n (consMerging .(G ∣ (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (consMerging .G .Γ1 .Δ1 .T .D n₁ m)) =
    Propstep1* (G ∣ (Γ1 , Δ1)) H T D pG pHTD n' ◆pG≤n (consMerging G Γ1 Δ1 T D n₁ m)
  Propstep1* .(G ∣ (Γ , Δ)) H T D (C G Γ Δ pG) pHTD n' ◆pG≤n (consMerging .G .Γ .Δ .T .D n m) =
    Propstep1* (G ∣ (Γ , Δ) ∣ (Γ , Δ)) H T D pG pHTD n' ◆pG≤n (consMerging (G ∣ (Γ , Δ)) Γ Δ T D n (consMerging G Γ Δ T D n m))
  Propstep1* .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) H T D (S G Γ1 Γ2 Δ1 Δ2 refl refl pG) pHTD n' ◆pG≤n (consMerging .(G ∣ (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (consMerging .G .Γ1 .Δ1 .T .D n₁ m)) =
    congPropLeavesStep1*
      (Propstep1* (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) H T D pG pHTD n' ◆pG≤n (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m))
      (sym
        (begin
          leaves* (unionCopy-L* (unionLHSeq H (merge G T D m)) (union Γ1 Γ2) T (union (union Δ1 Δ2) (union (copy D n₁) (copy D n))) n₁ n (unionCopy-R* (unionLHSeq H (merge G T D m)) (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1* (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) H T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m))))
            ≡⟨ unionCopy-L*KeepLeaves* {unionLHSeq H (merge G T D m)} {union Γ1 Γ2} {T} {union (union Δ1 Δ2) (union (copy D n₁) (copy D n))} {n₁} {n} (unionCopy-R* (unionLHSeq H (merge G T D m)) (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1* (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) H T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m))) ⟩
          leaves* (unionCopy-R* (unionLHSeq H (merge G T D m)) (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1* (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) H T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m)))
            ≡⟨ unionCopy-R*KeepLeaves* {unionLHSeq H (merge G T D m)} {union (union Γ1 Γ2) (copy T (n₁ + n))} {union Δ1 Δ2} {D} {n₁} {n} (step1* (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) H T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m)) ⟩
          leaves* (step1* (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) H T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m)) ∎))
  Propstep1* .(G ∣ ((Γ ∷ A) , (Δ ∷ A))) H T D (Id-rule G Γ Δ A pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ A) .(Δ ∷ A) .T .D n m) =
    Propstep1* (G ∣ (Γ , Δ)) H T D pG pHTD n' ◆pG≤n (consMerging G Γ Δ T D n m)
  Propstep1* .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) H T D (W-head Γ1 Γ2 Δ1 Δ2 pG) pHTD n' ◆pG≤n (consMerging .(head (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (headMerging .Γ1 .Δ1 .T .D n₁)) =
    Propstep1* (head (Γ1 , Δ1)) H T D pG pHTD n' ◆pG≤n (headMerging Γ1 Δ1 T D n₁)
  Propstep1* .(head (Γ , Δ)) H T D (C-head Γ Δ pG) pHTD n' ◆pG≤n (headMerging .Γ .Δ .T .D n) =
    Propstep1*
      (head (Γ , Δ) ∣ (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging (head (Γ , Δ)) Γ Δ T D n (headMerging Γ Δ T D n))
  Propstep1* .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) H T D (S-head Γ1 Γ2 Δ1 Δ2 refl refl pG) pHTD n' ◆pG≤n (consMerging .(head (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (headMerging .Γ1 .Δ1 .T .D n₁)) = congPropLeavesStep1*
    (Propstep1*
      (head (union Γ1 Γ2 , union Δ1 Δ2))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n)))
    (sym
      (begin
        leaves* (unionCopy-L* H (union Γ1 Γ2) T (union (union Δ1 Δ2) (union (copy D n₁) (copy D n))) n₁ n (unionCopy-R* H (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1* (head (union Γ1 Γ2 , union Δ1 Δ2)) H T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n)))))
          ≡⟨ unionCopy-L*KeepLeaves* {H} {union Γ1 Γ2} {T} {union (union Δ1 Δ2) (union (copy D n₁) (copy D n))} {n₁} {n} (unionCopy-R* H (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1* (head (union Γ1 Γ2 , union Δ1 Δ2)) H T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n)))) ⟩
        leaves* (unionCopy-R* H (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1* (head (union Γ1 Γ2 , union Δ1 Δ2)) H T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n))))
          ≡⟨ unionCopy-R*KeepLeaves* {H} {union (union Γ1 Γ2) (copy T (n₁ + n))} {union Δ1 Δ2} {D} {n₁} {n} (step1* (head (union Γ1 Γ2 , union Δ1 Δ2)) H T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n))) ⟩
        leaves* (step1* (head (union Γ1 Γ2 , union Δ1 Δ2)) H T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n))) ∎))
  Propstep1* .(head ((Γ ∷ A) , (Δ ∷ A))) H T D (Id-rule-head Γ Δ A pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ A) .(Δ ∷ A) .T .D n) =
    Propstep1*
      (head (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging Γ Δ T D n)
  Propstep1* .(G ∣ ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ)) H T D (U-L G Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (A , n1) ∷ (A , n2)) .Δ .T .D n m) =
    Propstep1*
      (G ∣ (Γ ∷ (A , n1 + n2) , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        (Γ ∷ (A , n1 + n2))
        Δ
        T
        D
        n
        m)
  Propstep1* .(G ∣ (Γ , (Δ ∷ (A , n1) ∷ (A , n2)))) H T D (U-R G Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (A , n1) ∷ (A , n2)) .T .D n m) = 
    Propstep1*
      (G ∣ (Γ , Δ ∷ (A , n1 + n2)))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        (Δ ∷ (A , n1 + n2))
        T
        D
        n
        m)
  Propstep1* .(G ∣ ((Γ ∷ (A , n1 + n2)) , Δ)) H T D (F-L G Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (A , n1 + n2)) .Δ .T .D n m) =
    Propstep1*
      (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        (Γ ∷ (A , n1) ∷ (A , n2))
        Δ
        T
        D
        n
        m)
  Propstep1* .(G ∣ (Γ , (Δ ∷ (A , n1 + n2)))) H T D (F-R G Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (A , n1 + n2)) .T .D n m) =
    Propstep1*
      (G ∣ (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        (Δ ∷ (A , n1) ∷ (A , n2))
        T
        D
        n
        m)
  Propstep1* .(head ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ)) H T D (U-L-head Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (headMerging (Γ ∷ (A , n1) ∷ (A , n2)) Δ T D n) = 
    Propstep1*
      (head (Γ ∷ (A , n1 + n2) , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        (Γ ∷ (A , n1 + n2))
        Δ
        T
        D
        n)
  Propstep1* .(head (Γ , (Δ ∷ (A , n1) ∷ (A , n2)))) H T D (U-R-head Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (A , n1) ∷ (A , n2)) .T .D n) = 
    Propstep1*
      (head (Γ , Δ ∷ (A , n1 + n2)))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        (Δ ∷ (A , n1 + n2))
        T
        D
        n)
  Propstep1* .(head ((Γ ∷ (A , n1 + n2)) , Δ)) H T D (F-L-head Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (A , n1 + n2)) .Δ .T .D n) =
    Propstep1*
      (head (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        (Γ ∷ (A , n1) ∷ (A , n2))
        Δ
        T
        D
        n)
  Propstep1* .(head (Γ , (Δ ∷ (A , n1 + n2)))) H T D (F-R-head Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (A , n1 + n2)) .T .D n) =
    Propstep1*
      (head (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        (Δ ∷ (A , n1) ∷ (A , n2))
        T
        D
        n)
  Propstep1* .(G ∣ ((Γ ∷ (A , 0)) , Δ)) H T D (E-L G Γ Δ A pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (A , 0)) .Δ .T .D n m) =
    Propstep1*
      (G ∣ (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        Δ
        T
        D
        n
        m)
  Propstep1* .(G ∣ (Γ , (Δ ∷ (A , 0)))) H T D (E-R G Γ Δ A pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (A , 0)) .T .D n m) = 
    Propstep1*
      (G ∣ (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        Δ
        T
        D
        n
        m)
  Propstep1* .(head ((Γ ∷ (A , 0)) , Δ)) H T D (E-L-head Γ Δ A pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (A , 0)) .Δ .T .D n) = 
    Propstep1*
      (head (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        Δ
        T
        D
        n)
  Propstep1* .(head (Γ , (Δ ∷ (A , 0)))) H T D (E-R-head Γ Δ A pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (A , 0)) .T .D n) = 
    Propstep1*
      (head (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        Δ
        T
        D
        n)
  Propstep1* .(G ∣ ((Γ ∷ (A +S B , n)) , Δ)) H T D (plus-L G Γ Δ A B n pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (A +S B , n)) .Δ .T .D n₁ m) =
    Propstep1*
      (G ∣ (Γ ∷ (A , n) ∷ (B , n) , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        (Γ ∷ (A , n) ∷ (B , n))
        Δ
        T
        D
        n₁
        m)
  Propstep1* .(G ∣ (Γ , (Δ ∷ (A +S B , n)))) H T D (plus-R G Γ Δ A B n pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (A +S B , n)) .T .D n₁ m) = 
    Propstep1*
      (G ∣ (Γ , Δ ∷ (A , n) ∷ (B , n)))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        (Δ ∷ (A , n) ∷ (B , n))
        T
        D
        n₁
        m)
  Propstep1* .(G ∣ ((Γ ∷ (A ⊔S B , n)) , Δ)) H T D (max-L G Γ Δ A B n pG pG₁) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (A ⊔S B , n)) .Δ .T .D n₁ m) = 
    unionPropLeavesStep1*
      (Propstep1*
        (G ∣ (Γ ∷ (A , n) , Δ))
        H
        T
        D
        pG
        pHTD
        n'
        (≤-trans
          (cong-≤-l
            {#◆* pG + 0}
            (+-comm
              (#◆* pG)
              zero)
            (a≤b=>c≤d=>a+c≤b+d
              (k≤k (#◆* pG))
              z≤n))
          ◆pG≤n)
        (consMerging G (Γ ∷ (A , n)) Δ T D n₁ m))
      (Propstep1*
        (G ∣ (Γ ∷ (B , n) , Δ))
        H
        T
        D
        pG₁
        pHTD
        n'
        (≤-trans
          (a≤b=>c≤d=>a+c≤b+d
            z≤n
            (k≤k (#◆* pG₁)))
          ◆pG≤n)
        (consMerging G (Γ ∷ (B , n)) Δ T D n₁ m))
  Propstep1* .(G ∣ (Γ , (Δ ∷ (A ⊔S B , n)))) H T D (max-R G Γ Δ A B n pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (A ⊔S B , n)) .T .D n₁ m) = 
    Propstep1*
      (G ∣ (Γ , Δ ∷ (A , n)) ∣ (Γ , Δ ∷ (B , n)))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        (G ∣ (Γ , Δ ∷ (A , n)))
        Γ
        (Δ ∷ (B , n))
        T
        D
        n₁
        (consMerging
          G
          Γ
          (Δ ∷ (A , n))
          T
          D
          n₁
          m))
  Propstep1* .(head ((Γ ∷ (A +S B , n)) , Δ)) H T D (plus-L-head Γ Δ A B n pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (A +S B , n)) .Δ .T .D n₁) =
    Propstep1*
      (head (Γ ∷ (A , n) ∷ (B , n), Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging (Γ ∷ (A , n) ∷ (B , n)) Δ T D n₁)
  Propstep1* .(head (Γ , (Δ ∷ (A +S B , n)))) H T D (plus-R-head Γ Δ A B n pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (A +S B , n)) .T .D n₁) = 
    Propstep1*
      (head (Γ , Δ ∷ (A , n) ∷ (B , n)))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging Γ (Δ ∷ (A , n) ∷ (B , n)) T D n₁)
  Propstep1* .(head ((Γ ∷ (A ⊔S B , n)) , Δ)) H T D (max-L-head Γ Δ A B n pG pG₁) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (A ⊔S B , n)) .Δ .T .D n₁) =
    unionPropLeavesStep1*
      (Propstep1*
        (head (Γ ∷ (A , n) , Δ))
        H
        T
        D
        pG
        pHTD
        n'
        (≤-trans
          (cong-≤-l
            {#◆* pG + 0}
            (+-comm
              (#◆* pG)
              zero)
            (a≤b=>c≤d=>a+c≤b+d
              (k≤k (#◆* pG))
              z≤n))
          ◆pG≤n)
        (headMerging (Γ ∷ (A , n)) Δ T D n₁))
      (Propstep1*
        (head (Γ ∷ (B , n) , Δ))
        H
        T
        D
        pG₁
        pHTD
        n'
        (≤-trans
          (a≤b=>c≤d=>a+c≤b+d
            z≤n
            (k≤k (#◆* pG₁)))
          ◆pG≤n)
        (headMerging (Γ ∷ (B , n)) Δ T D n₁))
  Propstep1* .(head (Γ , (Δ ∷ (A ⊔S B , n)))) H T D (max-R-head Γ Δ A B n pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (A ⊔S B , n)) .T .D n₁) = 
    Propstep1*
      (head (Γ , Δ ∷ (A , n)) ∣ (Γ , Δ ∷ (B , n)))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        (head (Γ , Δ ∷ (A , n)))
        Γ
        (Δ ∷ (B , n))
        T
        D
        n₁
        (headMerging
          Γ
          (Δ ∷ (A , n))
          T
          D
          n₁))
  Propstep1* .(head (Γ , (Δ ∷ (one , suc k)))) H T D (◆1-rule Γ Δ ◆Γ ◆Δ refl refl k pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (one , suc k)) .T .D n) =
    consP1
      H
      Γ
      Δ
      T
      D
      ◆Γ
      ◆Δ
      k
      pG
      n
      n'
      ◆pG≤n
      ([]P1 H T D n')
  Propstep1* .(head (Γ , Δ)) H T D (◆-rule Γ Δ ◆Γ ◆Δ refl refl pG) pHTD n' ◆pG≤n (headMerging .Γ .Δ .T .D n) =
    consP1'
      H
      Γ
      Δ
      T
      D
      ◆Γ
      ◆Δ
      pG
      n
      n'
      ◆pG≤n
      ([]P1 H T D n')
  Propstep1* .(G ∣ (Γ' , Δ')) H T D (seq-exchange G Γ Γ' Δ Δ' x x₁ pG) pHTD n' ◆pG≤n (consMerging .G .Γ' .Δ' .T .D n m) =
    Propstep1*
      (G ∣ (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        Δ
        T
        D
        n
        m)
  Propstep1* .(head (Γ' , Δ')) H T D (seq-exchange-head Γ Γ' Δ Δ' x x₁ pG) pHTD n' ◆pG≤n (headMerging .Γ' .Δ' .T .D n) = 
    Propstep1*
      (head (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        Δ
        T
        D
        n)
  Propstep1* G H T D (hseq-exchange G₁ .G x pG) pHTD n' ◆pG≤n m = 
    Propstep1*
      G₁
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (MergingExchange G G₁ T D m (LHSeqExchangeSym x))
  Propstep1* .(G ∣ ((Γ ∷ (-S A , n)) , Δ)) H T D (minus-L G Γ Δ A n pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (-S A , n)) .Δ .T .D n₁ m) =
    Propstep1*
      (G ∣ (Γ , Δ ∷ (A , n)))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        (Δ ∷ (A , n))
        T
        D
        n₁
        m)
  Propstep1* .(G ∣ (Γ , (Δ ∷ (-S A , n)))) H T D (minus-R G Γ Δ A n pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (-S A , n)) .T .D n₁ m) = 
    Propstep1*
      (G ∣ (Γ ∷ (A , n) , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        (Γ ∷ (A , n))
        Δ
        T
        D
        n₁
        m)
  Propstep1* .(G ∣ ((Γ ∷ (botAG , n)) , Δ)) H T D (Z-L G Γ Δ n pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (botAG , n)) .Δ .T .D n₁ m) =
    Propstep1*
      (G ∣ (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        Δ
        T
        D
        n₁
        m)
  Propstep1* .(G ∣ (Γ , (Δ ∷ (botAG , n)))) H T D (Z-R G Γ Δ n pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (botAG , n)) .T .D n₁ m) = 
    Propstep1*
      (G ∣ (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        Δ
        T
        D
        n₁
        m)
  Propstep1* .(G ∣ (Γ , (Δ ∷ (A ⊓S B , n)))) H T D (min-R G Γ Δ A B n pG pG₁) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (A ⊓S B , n)) .T .D n₁ m) = 
    unionPropLeavesStep1*
      (Propstep1*
        (G ∣ (Γ , Δ ∷ (A , n)))
        H
        T
        D
        pG
        pHTD
        n'
        (≤-trans
          (cong-≤-l
            {#◆* pG + 0}
            (+-comm
              (#◆* pG)
              zero)
            (a≤b=>c≤d=>a+c≤b+d
              (k≤k (#◆* pG))
              z≤n))
          ◆pG≤n)
        (consMerging G Γ (Δ ∷ (A , n)) T D n₁ m))
      (Propstep1*
        (G ∣ (Γ , Δ ∷ (B , n)))
        H
        T
        D
        pG₁
        pHTD
        n'
        (≤-trans
          (a≤b=>c≤d=>a+c≤b+d
            z≤n
            (k≤k (#◆* pG₁)))
          ◆pG≤n)
        (consMerging G Γ (Δ ∷ (B , n)) T D n₁ m))
  Propstep1* .(G ∣ ((Γ ∷ (A ⊓S B , n)) , Δ)) H T D (min-L G Γ Δ A B n pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (A ⊓S B , n)) .Δ .T .D n₁ m) = 
    Propstep1*
      (G ∣ (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        (G ∣ (Γ ∷ (A , n) , Δ))
        (Γ ∷ (B , n))
        Δ
        T
        D
        n₁
        (consMerging
          G
          (Γ ∷ (A , n))
          Δ
          T
          D
          n₁
          m))
  Propstep1* .(head ((Γ ∷ (-S A , n)) , Δ)) H T D (minus-L-head Γ Δ A n pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (-S A , n)) .Δ .T .D n₁) =
    Propstep1*
      (head (Γ , Δ ∷ (A , n)))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        (Δ ∷ (A , n))
        T
        D
        n₁)
  Propstep1* .(head (Γ , (Δ ∷ (-S A , n)))) H T D (minus-R-head Γ Δ A n pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (-S A , n)) .T .D n₁) = 
    Propstep1*
      (head (Γ ∷ (A , n) , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        (Γ ∷ (A , n))
        Δ
        T
        D
        n₁)
  Propstep1* .(head ((Γ ∷ (botAG , n)) , Δ)) H T D (Z-L-head Γ Δ n pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (botAG , n)) .Δ .T .D n₁) =
    Propstep1*
      (head (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        Δ
        T
        D
        n₁)
  Propstep1* .(head (Γ , (Δ ∷ (botAG , n)))) H T D (Z-R-head Γ Δ n pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (botAG , n)) .T .D n₁) = 
    Propstep1*
      (head (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        Δ
        T
        D
        n₁)
  Propstep1* .(head (Γ , (Δ ∷ (A ⊓S B , n)))) H T D (min-R-head Γ Δ A B n pG pG₁) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (A ⊓S B , n)) .T .D n₁) = 
    unionPropLeavesStep1*
      (Propstep1*
        (head (Γ , Δ ∷ (A , n)))
        H
        T
        D
        pG
        pHTD
        n'
        (≤-trans
          (cong-≤-l
            {#◆* pG + 0}
            (+-comm
              (#◆* pG)
              zero)
            (a≤b=>c≤d=>a+c≤b+d
              (k≤k (#◆* pG))
              z≤n))
          ◆pG≤n)
        (headMerging Γ (Δ ∷ (A , n)) T D n₁))
      (Propstep1*
        (head (Γ , Δ ∷ (B , n)))
        H
        T
        D
        pG₁
        pHTD
        n'
        (≤-trans
          (a≤b=>c≤d=>a+c≤b+d
            z≤n
            (k≤k (#◆* pG₁)))
          ◆pG≤n)
        (headMerging Γ (Δ ∷ (B , n)) T D n₁))
  Propstep1* .(head ((Γ ∷ (A ⊓S B , n)) , Δ)) H T D (min-L-head Γ Δ A B n pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (A ⊓S B , n)) .Δ .T .D n₁) = 
    Propstep1*
      (head (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        (head (Γ ∷ (A , n) , Δ))
        (Γ ∷ (B , n))
        Δ
        T
        D
        n₁
        (headMerging
          (Γ ∷ (A , n))
          Δ
          T
          D
          n₁))
  Propstep1* .(G ∣ (Γ , Δ ∷ (one , k))) H T D (1-rule G Γ Δ k pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (one , k)) T D n m) =
    Propstep1*
      (G ∣ (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging G Γ Δ T D n m)
  Propstep1* .(head (Γ , Δ ∷ (one , k))) H T D (1-rule-head Γ Δ k pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (one , k)) T D n) =
    Propstep1*
      (head (Γ , Δ))
      H
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging Γ Δ T D n)
--}}}
      
  Propstep1*-head :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    (pG : MGA-SR†* G) ->
    (pHTD : MGA-SR†* (head (T , D))) ->
    (n : ℕ) ->
    (◆pG≤n : #◆* pG ≤ n) ->
    (m : Merging G T D) ->
    propLeavesStep1*-head T D n (leaves* (step1*-head G T D pG pHTD m))
--{{{
  Propstep1*-head .(head ([] , [])) T D ax pHTD n' ◆pG≤n (headMerging .[] .[] .T .D n) = congPropLeavesStep1*-head
      ([]P1head T D n')
      (sym
        (trans
          (congKeepLeaves*
            (proofToPreproof* (PumpingLemma-head (T , D) n pHTD))
            (cong₂
              (λ x y -> head (x , y))
              (sym (union[]T=T (copy T n)))
              (sym (union[]T=T (copy D n)))))
          (leavesMGA-SR†*
            (PumpingLemma-head (T , D) n pHTD))))
  Propstep1*-head .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) T D (W G Γ1 Γ2 Δ1 Δ2 pG) pHTD n' ◆pG≤n (consMerging .(G ∣ (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (consMerging .G .Γ1 .Δ1 .T .D n₁ m)) =
    Propstep1*-head (G ∣ (Γ1 , Δ1)) T D pG pHTD n' ◆pG≤n (consMerging G Γ1 Δ1 T D n₁ m)
  Propstep1*-head .(G ∣ (Γ , Δ)) T D (C G Γ Δ pG) pHTD n' ◆pG≤n (consMerging .G .Γ .Δ .T .D n m) =
    Propstep1*-head (G ∣ (Γ , Δ) ∣ (Γ , Δ)) T D pG pHTD n' ◆pG≤n (consMerging (G ∣ (Γ , Δ)) Γ Δ T D n (consMerging G Γ Δ T D n m))
  Propstep1*-head .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) T D (S G Γ1 Γ2 Δ1 Δ2 refl refl pG) pHTD n' ◆pG≤n (consMerging .(G ∣ (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (consMerging .G .Γ1 .Δ1 .T .D n₁ m)) = 
    congPropLeavesStep1*-head
      (Propstep1*-head (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD n' ◆pG≤n (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m))
      (sym
        (begin
          leaves* (unionCopy-L* (merge G T D m) (union Γ1 Γ2) T (union (union Δ1 Δ2) (union (copy D n₁) (copy D n))) n₁ n (unionCopy-R* (merge G T D m) (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1*-head (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m))))
            ≡⟨ unionCopy-L*KeepLeaves* {merge G T D m} {union Γ1 Γ2} {T} {union (union Δ1 Δ2) (union (copy D n₁) (copy D n))} {n₁} {n} (unionCopy-R* (merge G T D m) (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1*-head (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m))) ⟩
          leaves* (unionCopy-R* (merge G T D m) (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1*-head (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m)))
            ≡⟨ unionCopy-R*KeepLeaves* {merge G T D m} {union (union Γ1 Γ2) (copy T (n₁ + n))} {union Δ1 Δ2} {D} {n₁} {n} (step1*-head (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m)) ⟩
          leaves* (step1*-head (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m)) ∎))
  Propstep1*-head .(G ∣ ((Γ ∷ A) , (Δ ∷ A))) T D (Id-rule G Γ Δ A pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ A) .(Δ ∷ A) .T .D n m) =
    Propstep1*-head (G ∣ (Γ , Δ)) T D pG pHTD n' ◆pG≤n (consMerging G Γ Δ T D n m)
  Propstep1*-head .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) T D (W-head Γ1 Γ2 Δ1 Δ2 pG) pHTD n' ◆pG≤n (consMerging .(head (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (headMerging .Γ1 .Δ1 .T .D n₁)) =
    Propstep1*-head (head (Γ1 , Δ1)) T D pG pHTD n' ◆pG≤n (headMerging Γ1 Δ1 T D n₁)
  Propstep1*-head .(head (Γ , Δ)) T D (C-head Γ Δ pG) pHTD n' ◆pG≤n (headMerging .Γ .Δ .T .D n) =
    Propstep1*-head
      (head (Γ , Δ) ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging (head (Γ , Δ)) Γ Δ T D n (headMerging Γ Δ T D n))
  Propstep1*-head .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) T D (S-head Γ1 Γ2 Δ1 Δ2 refl refl pG) pHTD n' ◆pG≤n (consMerging .(head (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (headMerging .Γ1 .Δ1 .T .D n₁)) = congPropLeavesStep1*-head
    (Propstep1*-head
      (head (union Γ1 Γ2 , union Δ1 Δ2))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n)))
    (sym
      (begin
        leaves* (unionCopy-L*-head (union Γ1 Γ2) T (union (union Δ1 Δ2) (union (copy D n₁) (copy D n))) n₁ n (unionCopy-R*-head (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1*-head (head (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n)))))
          ≡⟨ unionCopy-L*-headKeepLeaves* {union Γ1 Γ2} {T} {union (union Δ1 Δ2) (union (copy D n₁) (copy D n))} {n₁} {n} (unionCopy-R*-head (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1*-head (head (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n)))) ⟩
        leaves* (unionCopy-R*-head (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1*-head (head (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n))))
          ≡⟨ unionCopy-R*-headKeepLeaves* {union (union Γ1 Γ2) (copy T (n₁ + n))} {union Δ1 Δ2} {D} {n₁} {n} (step1*-head (head (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n))) ⟩
        leaves* (step1*-head (head (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n))) ∎)) 
  Propstep1*-head .(head ((Γ ∷ A) , (Δ ∷ A))) T D (Id-rule-head Γ Δ A pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ A) .(Δ ∷ A) .T .D n) =
    Propstep1*-head
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging Γ Δ T D n)
  Propstep1*-head .(G ∣ ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ)) T D (U-L G Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (A , n1) ∷ (A , n2)) .Δ .T .D n m) =
    Propstep1*-head
      (G ∣ (Γ ∷ (A , n1 + n2) , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        (Γ ∷ (A , n1 + n2))
        Δ
        T
        D
        n
        m)
  Propstep1*-head .(G ∣ (Γ , (Δ ∷ (A , n1) ∷ (A , n2)))) T D (U-R G Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (A , n1) ∷ (A , n2)) .T .D n m) = 
    Propstep1*-head
      (G ∣ (Γ , Δ ∷ (A , n1 + n2)))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        (Δ ∷ (A , n1 + n2))
        T
        D
        n
        m)
  Propstep1*-head .(G ∣ ((Γ ∷ (A , n1 + n2)) , Δ)) T D (F-L G Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (A , n1 + n2)) .Δ .T .D n m) =
    Propstep1*-head
      (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        (Γ ∷ (A , n1) ∷ (A , n2))
        Δ
        T
        D
        n
        m)
  Propstep1*-head .(G ∣ (Γ , (Δ ∷ (A , n1 + n2)))) T D (F-R G Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (A , n1 + n2)) .T .D n m) =
    Propstep1*-head
      (G ∣ (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        (Δ ∷ (A , n1) ∷ (A , n2))
        T
        D
        n
        m)
  Propstep1*-head .(head ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ)) T D (U-L-head Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (headMerging (Γ ∷ (A , n1) ∷ (A , n2)) Δ T D n) = 
    Propstep1*-head
      (head (Γ ∷ (A , n1 + n2) , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        (Γ ∷ (A , n1 + n2))
        Δ
        T
        D
        n)
  Propstep1*-head .(head (Γ , (Δ ∷ (A , n1) ∷ (A , n2)))) T D (U-R-head Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (A , n1) ∷ (A , n2)) .T .D n) = 
    Propstep1*-head
      (head (Γ , Δ ∷ (A , n1 + n2)))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        (Δ ∷ (A , n1 + n2))
        T
        D
        n)
  Propstep1*-head .(head ((Γ ∷ (A , n1 + n2)) , Δ)) T D (F-L-head Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (A , n1 + n2)) .Δ .T .D n) =
    Propstep1*-head
      (head (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        (Γ ∷ (A , n1) ∷ (A , n2))
        Δ
        T
        D
        n)
  Propstep1*-head .(head (Γ , (Δ ∷ (A , n1 + n2)))) T D (F-R-head Γ Δ A n1 n2 refl pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (A , n1 + n2)) .T .D n) =
    Propstep1*-head
      (head (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        (Δ ∷ (A , n1) ∷ (A , n2))
        T
        D
        n)
  Propstep1*-head .(G ∣ ((Γ ∷ (A , 0)) , Δ)) T D (E-L G Γ Δ A pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (A , 0)) .Δ .T .D n m) =
    Propstep1*-head
      (G ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        Δ
        T
        D
        n
        m)
  Propstep1*-head .(G ∣ (Γ , (Δ ∷ (A , 0)))) T D (E-R G Γ Δ A pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (A , 0)) .T .D n m) = 
    Propstep1*-head
      (G ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        Δ
        T
        D
        n
        m)
  Propstep1*-head .(head ((Γ ∷ (A , 0)) , Δ)) T D (E-L-head Γ Δ A pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (A , 0)) .Δ .T .D n) = 
    Propstep1*-head
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        Δ
        T
        D
        n)
  Propstep1*-head .(head (Γ , (Δ ∷ (A , 0)))) T D (E-R-head Γ Δ A pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (A , 0)) .T .D n) = 
    Propstep1*-head
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        Δ
        T
        D
        n)
  Propstep1*-head .(G ∣ ((Γ ∷ (A +S B , n)) , Δ)) T D (plus-L G Γ Δ A B n pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (A +S B , n)) .Δ .T .D n₁ m) =
    Propstep1*-head
      (G ∣ (Γ ∷ (A , n) ∷ (B , n) , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        (Γ ∷ (A , n) ∷ (B , n))
        Δ
        T
        D
        n₁
        m)
  Propstep1*-head .(G ∣ (Γ , (Δ ∷ (A +S B , n)))) T D (plus-R G Γ Δ A B n pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (A +S B , n)) .T .D n₁ m) = 
    Propstep1*-head
      (G ∣ (Γ , Δ ∷ (A , n) ∷ (B , n)))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        (Δ ∷ (A , n) ∷ (B , n))
        T
        D
        n₁
        m)
  Propstep1*-head .(G ∣ ((Γ ∷ (A ⊔S B , n)) , Δ)) T D (max-L G Γ Δ A B n pG pG₁) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (A ⊔S B , n)) .Δ .T .D n₁ m) = 
    unionPropLeavesStep1*-head
      (Propstep1*-head
        (G ∣ (Γ ∷ (A , n) , Δ))
        T
        D
        pG
        pHTD
        n'
        (≤-trans
          (cong-≤-l
            {#◆* pG + 0}
            (+-comm
              (#◆* pG)
              zero)
            (a≤b=>c≤d=>a+c≤b+d
              (k≤k (#◆* pG))
              z≤n))
          ◆pG≤n)
        (consMerging G (Γ ∷ (A , n)) Δ T D n₁ m))
      (Propstep1*-head
        (G ∣ (Γ ∷ (B , n) , Δ))
        T
        D
        pG₁
        pHTD
        n'
        (≤-trans
          (a≤b=>c≤d=>a+c≤b+d
            z≤n
            (k≤k (#◆* pG₁)))
          ◆pG≤n)
        (consMerging G (Γ ∷ (B , n)) Δ T D n₁ m))
  Propstep1*-head .(G ∣ (Γ , (Δ ∷ (A ⊔S B , n)))) T D (max-R G Γ Δ A B n pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (A ⊔S B , n)) .T .D n₁ m) = 
    Propstep1*-head
      (G ∣ (Γ , Δ ∷ (A , n)) ∣ (Γ , Δ ∷ (B , n)))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        (G ∣ (Γ , Δ ∷ (A , n)))
        Γ
        (Δ ∷ (B , n))
        T
        D
        n₁
        (consMerging
          G
          Γ
          (Δ ∷ (A , n))
          T
          D
          n₁
          m))
  Propstep1*-head .(head ((Γ ∷ (A +S B , n)) , Δ)) T D (plus-L-head Γ Δ A B n pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (A +S B , n)) .Δ .T .D n₁) =
    Propstep1*-head
      (head (Γ ∷ (A , n) ∷ (B , n), Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging (Γ ∷ (A , n) ∷ (B , n)) Δ T D n₁)
  Propstep1*-head .(head (Γ , (Δ ∷ (A +S B , n)))) T D (plus-R-head Γ Δ A B n pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (A +S B , n)) .T .D n₁) = 
    Propstep1*-head
      (head (Γ , Δ ∷ (A , n) ∷ (B , n)))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging Γ (Δ ∷ (A , n) ∷ (B , n)) T D n₁)
  Propstep1*-head .(head ((Γ ∷ (A ⊔S B , n)) , Δ)) T D (max-L-head Γ Δ A B n pG pG₁) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (A ⊔S B , n)) .Δ .T .D n₁) =
    unionPropLeavesStep1*-head
      (Propstep1*-head
        (head (Γ ∷ (A , n) , Δ))
        T
        D
        pG
        pHTD
        n'
        (≤-trans
          (cong-≤-l
            {#◆* pG + 0}
            (+-comm
              (#◆* pG)
              zero)
            (a≤b=>c≤d=>a+c≤b+d
              (k≤k (#◆* pG))
              z≤n))
          ◆pG≤n)
        (headMerging (Γ ∷ (A , n)) Δ T D n₁))
      (Propstep1*-head
        (head (Γ ∷ (B , n) , Δ))
        T
        D
        pG₁
        pHTD
        n'
        (≤-trans
          (a≤b=>c≤d=>a+c≤b+d
            z≤n
            (k≤k (#◆* pG₁)))
          ◆pG≤n)
        (headMerging (Γ ∷ (B , n)) Δ T D n₁))
  Propstep1*-head .(head (Γ , (Δ ∷ (A ⊔S B , n)))) T D (max-R-head Γ Δ A B n pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (A ⊔S B , n)) .T .D n₁) = 
    Propstep1*-head
      (head (Γ , Δ ∷ (A , n)) ∣ (Γ , Δ ∷ (B , n)))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        (head (Γ , Δ ∷ (A , n)))
        Γ
        (Δ ∷ (B , n))
        T
        D
        n₁
        (headMerging
          Γ
          (Δ ∷ (A , n))
          T
          D
          n₁))
  Propstep1*-head .(head (Γ , (Δ ∷ (one , suc k)))) T D (◆1-rule Γ Δ ◆Γ ◆Δ refl refl k pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (one , suc k)) .T .D n) =
    consP1head
      Γ
      Δ
      T
      D
      ◆Γ
      ◆Δ
      k
      pG
      n
      n'
      ◆pG≤n
      ([]P1head T D n')
  Propstep1*-head .(head (Γ , Δ)) T D (◆-rule Γ Δ ◆Γ ◆Δ refl refl pG) pHTD n' ◆pG≤n (headMerging .Γ .Δ .T .D n) =
    consP1head'
      Γ
      Δ
      T
      D
      ◆Γ
      ◆Δ
      pG
      n
      n'
      ◆pG≤n
      ([]P1head T D n')
  Propstep1*-head .(G ∣ (Γ' , Δ')) T D (seq-exchange G Γ Γ' Δ Δ' x x₁ pG) pHTD n' ◆pG≤n (consMerging .G .Γ' .Δ' .T .D n m) =
    Propstep1*-head
      (G ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        Δ
        T
        D
        n
        m)
  Propstep1*-head .(head (Γ' , Δ')) T D (seq-exchange-head Γ Γ' Δ Δ' x x₁ pG) pHTD n' ◆pG≤n (headMerging .Γ' .Δ' .T .D n) = 
    Propstep1*-head
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        Δ
        T
        D
        n)
  Propstep1*-head G T D (hseq-exchange G₁ .G x pG) pHTD n' ◆pG≤n m =
    Propstep1*-head
      G₁
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (MergingExchange G G₁ T D m (LHSeqExchangeSym x))
  Propstep1*-head .(G ∣ ((Γ ∷ (-S A , n)) , Δ)) T D (minus-L G Γ Δ A n pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (-S A , n)) .Δ .T .D n₁ m) =
    Propstep1*-head
      (G ∣ (Γ , Δ ∷ (A , n)))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        (Δ ∷ (A , n))
        T
        D
        n₁
        m)
  Propstep1*-head .(G ∣ (Γ , (Δ ∷ (-S A , n)))) T D (minus-R G Γ Δ A n pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (-S A , n)) .T .D n₁ m) = 
    Propstep1*-head
      (G ∣ (Γ ∷ (A , n) , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        (Γ ∷ (A , n))
        Δ
        T
        D
        n₁
        m)
  Propstep1*-head .(G ∣ ((Γ ∷ (botAG , n)) , Δ)) T D (Z-L G Γ Δ n pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (botAG , n)) .Δ .T .D n₁ m) =
    Propstep1*-head
      (G ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        Δ
        T
        D
        n₁
        m)
  Propstep1*-head .(G ∣ (Γ , (Δ ∷ (botAG , n)))) T D (Z-R G Γ Δ n pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (botAG , n)) .T .D n₁ m) = 
    Propstep1*-head
      (G ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        G
        Γ
        Δ
        T
        D
        n₁
        m)
  Propstep1*-head .(G ∣ (Γ , (Δ ∷ (A ⊓S B , n)))) T D (min-R G Γ Δ A B n pG pG₁) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (A ⊓S B , n)) .T .D n₁ m) = 
    unionPropLeavesStep1*-head
      (Propstep1*-head
        (G ∣ (Γ , Δ ∷ (A , n)))
        T
        D
        pG
        pHTD
        n'
        (≤-trans
          (cong-≤-l
            {#◆* pG + 0}
            (+-comm
              (#◆* pG)
              zero)
            (a≤b=>c≤d=>a+c≤b+d
              (k≤k (#◆* pG))
              z≤n))
          ◆pG≤n)
        (consMerging G Γ (Δ ∷ (A , n)) T D n₁ m))
      (Propstep1*-head
        (G ∣ (Γ , Δ ∷ (B , n)))
        T
        D
        pG₁
        pHTD
        n'
        (≤-trans
          (a≤b=>c≤d=>a+c≤b+d
            z≤n
            (k≤k (#◆* pG₁)))
          ◆pG≤n)
        (consMerging G Γ (Δ ∷ (B , n)) T D n₁ m))
  Propstep1*-head .(G ∣ ((Γ ∷ (A ⊓S B , n)) , Δ)) T D (min-L G Γ Δ A B n pG) pHTD n' ◆pG≤n (consMerging .G .(Γ ∷ (A ⊓S B , n)) .Δ .T .D n₁ m) = 
    Propstep1*-head
      (G ∣ (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        (G ∣ (Γ ∷ (A , n) , Δ))
        (Γ ∷ (B , n))
        Δ
        T
        D
        n₁
        (consMerging
          G
          (Γ ∷ (A , n))
          Δ
          T
          D
          n₁
          m))
  Propstep1*-head .(head ((Γ ∷ (-S A , n)) , Δ)) T D (minus-L-head Γ Δ A n pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (-S A , n)) .Δ .T .D n₁) =
    Propstep1*-head
      (head (Γ , Δ ∷ (A , n)))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        (Δ ∷ (A , n))
        T
        D
        n₁)
  Propstep1*-head .(head (Γ , (Δ ∷ (-S A , n)))) T D (minus-R-head Γ Δ A n pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (-S A , n)) .T .D n₁) = 
    Propstep1*-head
      (head (Γ ∷ (A , n) , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        (Γ ∷ (A , n))
        Δ
        T
        D
        n₁)
  Propstep1*-head .(head ((Γ ∷ (botAG , n)) , Δ)) T D (Z-L-head Γ Δ n pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (botAG , n)) .Δ .T .D n₁) =
    Propstep1*-head
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        Δ
        T
        D
        n₁)
  Propstep1*-head .(head (Γ , (Δ ∷ (botAG , n)))) T D (Z-R-head Γ Δ n pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (botAG , n)) .T .D n₁) = 
    Propstep1*-head
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging
        Γ
        Δ
        T
        D
        n₁)
  Propstep1*-head .(head (Γ , (Δ ∷ (A ⊓S B , n)))) T D (min-R-head Γ Δ A B n pG pG₁) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (A ⊓S B , n)) .T .D n₁) = 
    unionPropLeavesStep1*-head
      (Propstep1*-head
        (head (Γ , Δ ∷ (A , n)))
        T
        D
        pG
        pHTD
        n'
        (≤-trans
          (cong-≤-l
            {#◆* pG + 0}
            (+-comm
              (#◆* pG)
              zero)
            (a≤b=>c≤d=>a+c≤b+d
              (k≤k (#◆* pG))
              z≤n))
          ◆pG≤n)
        (headMerging Γ (Δ ∷ (A , n)) T D n₁))
      (Propstep1*-head
        (head (Γ , Δ ∷ (B , n)))
        T
        D
        pG₁
        pHTD
        n'
        (≤-trans
          (a≤b=>c≤d=>a+c≤b+d
            z≤n
            (k≤k (#◆* pG₁)))
          ◆pG≤n)
        (headMerging Γ (Δ ∷ (B , n)) T D n₁))
  Propstep1*-head .(head ((Γ ∷ (A ⊓S B , n)) , Δ)) T D (min-L-head Γ Δ A B n pG) pHTD n' ◆pG≤n (headMerging .(Γ ∷ (A ⊓S B , n)) .Δ .T .D n₁) = 
    Propstep1*-head
      (head (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging
        (head (Γ ∷ (A , n) , Δ))
        (Γ ∷ (B , n))
        Δ
        T
        D
        n₁
        (headMerging
          (Γ ∷ (A , n))
          Δ
          T
          D
          n₁))
  Propstep1*-head .(G ∣ (Γ , Δ ∷ (one , k))) T D (1-rule G Γ Δ k pG) pHTD n' ◆pG≤n (consMerging .G .Γ .(Δ ∷ (one , k)) T D n m) =
    Propstep1*-head
      (G ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (consMerging G Γ Δ T D n m)
  Propstep1*-head .(head (Γ , Δ ∷ (one , k))) T D (1-rule-head Γ Δ k pG) pHTD n' ◆pG≤n (headMerging .Γ .(Δ ∷ (one , k)) T D n) =
    Propstep1*-head
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      n'
      ◆pG≤n
      (headMerging Γ Δ T D n)
--}}}
    
  Propstep1*-head-bis :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    (pG : MGA-SR†* G) ->
    (pHTD : MGA-SR†* (head (T , D))) ->
    (m : Merging G T D) ->
    propLeavesStep1*-head-bis T D (leaves* (step1*-head G T D pG pHTD m))
--{{{
  Propstep1*-head-bis .(head ([] , [])) T D ax pHTD  (headMerging .[] .[] .T .D n) =
    congPropLeavesStep1*-head-bis
      ([]P1head-bis T D)
      (sym
        (trans
          (congKeepLeaves*
            (proofToPreproof* (PumpingLemma-head (T , D) n pHTD))
            (cong₂
              (λ x y -> head (x , y))
              (sym (union[]T=T (copy T n)))
              (sym (union[]T=T (copy D n)))))
          (leavesMGA-SR†*
            (PumpingLemma-head (T , D) n pHTD))))
  Propstep1*-head-bis .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) T D (W G Γ1 Γ2 Δ1 Δ2 pG) pHTD  (consMerging .(G ∣ (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (consMerging .G .Γ1 .Δ1 .T .D n₁ m)) =
    Propstep1*-head-bis (G ∣ (Γ1 , Δ1)) T D pG pHTD  (consMerging G Γ1 Δ1 T D n₁ m)
  Propstep1*-head-bis .(G ∣ (Γ , Δ)) T D (C G Γ Δ pG) pHTD  (consMerging .G .Γ .Δ .T .D n m) =
    Propstep1*-head-bis (G ∣ (Γ , Δ) ∣ (Γ , Δ)) T D pG pHTD  (consMerging (G ∣ (Γ , Δ)) Γ Δ T D n (consMerging G Γ Δ T D n m))
  Propstep1*-head-bis .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) T D (S G Γ1 Γ2 Δ1 Δ2 refl refl pG) pHTD  (consMerging .(G ∣ (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (consMerging .G .Γ1 .Δ1 .T .D n₁ m)) =
    congPropLeavesStep1*-head-bis
      (Propstep1*-head-bis (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD  (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m))
      (sym
        (begin
          leaves* (unionCopy-L* (merge G T D m) (union Γ1 Γ2) T (union (union Δ1 Δ2) (union (copy D n₁) (copy D n))) n₁ n (unionCopy-R* (merge G T D m) (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1*-head (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m))))
            ≡⟨ unionCopy-L*KeepLeaves* {merge G T D m} {union Γ1 Γ2} {T} {union (union Δ1 Δ2) (union (copy D n₁) (copy D n))} {n₁} {n} (unionCopy-R* (merge G T D m) (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1*-head (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m))) ⟩
          leaves* (unionCopy-R* (merge G T D m) (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1*-head (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m)))
            ≡⟨ unionCopy-R*KeepLeaves* {merge G T D m} {union (union Γ1 Γ2) (copy T (n₁ + n))} {union Δ1 Δ2} {D} {n₁} {n} (step1*-head (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m)) ⟩
          leaves* (step1*-head (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (consMerging G (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n) m)) ∎))
  Propstep1*-head-bis .(G ∣ ((Γ ∷ A) , (Δ ∷ A))) T D (Id-rule G Γ Δ A pG) pHTD  (consMerging .G .(Γ ∷ A) .(Δ ∷ A) .T .D n m) =
    Propstep1*-head-bis (G ∣ (Γ , Δ)) T D pG pHTD  (consMerging G Γ Δ T D n m)
  Propstep1*-head-bis .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) T D (W-head Γ1 Γ2 Δ1 Δ2 pG) pHTD  (consMerging .(head (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (headMerging .Γ1 .Δ1 .T .D n₁)) =
    Propstep1*-head-bis (head (Γ1 , Δ1)) T D pG pHTD  (headMerging Γ1 Δ1 T D n₁)
  Propstep1*-head-bis .(head (Γ , Δ)) T D (C-head Γ Δ pG) pHTD  (headMerging .Γ .Δ .T .D n) =
    Propstep1*-head-bis
      (head (Γ , Δ) ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      (consMerging (head (Γ , Δ)) Γ Δ T D n (headMerging Γ Δ T D n))
  Propstep1*-head-bis .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) T D (S-head Γ1 Γ2 Δ1 Δ2 refl refl pG) pHTD  (consMerging .(head (Γ1 , Δ1)) .Γ2 .Δ2 .T .D n (headMerging .Γ1 .Δ1 .T .D n₁)) = congPropLeavesStep1*-head-bis
    (Propstep1*-head-bis
      (head (union Γ1 Γ2 , union Δ1 Δ2))
      T
      D
      pG
      pHTD
      (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n)))
    (sym
      (begin
        leaves* (unionCopy-L*-head (union Γ1 Γ2) T (union (union Δ1 Δ2) (union (copy D n₁) (copy D n))) n₁ n (unionCopy-R*-head (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1*-head (head (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n)))))
          ≡⟨ unionCopy-L*-headKeepLeaves* {union Γ1 Γ2} {T} {union (union Δ1 Δ2) (union (copy D n₁) (copy D n))} {n₁} {n} (unionCopy-R*-head (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1*-head (head (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n)))) ⟩
        leaves* (unionCopy-R*-head (union (union Γ1 Γ2) (copy T (n₁ + n))) (union Δ1 Δ2) D n₁ n (step1*-head (head (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n))))
          ≡⟨ unionCopy-R*-headKeepLeaves* {union (union Γ1 Γ2) (copy T (n₁ + n))} {union Δ1 Δ2} {D} {n₁} {n} (step1*-head (head (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n))) ⟩
        leaves* (step1*-head (head (union Γ1 Γ2 , union Δ1 Δ2)) T D pG pHTD (headMerging (union Γ1 Γ2) (union Δ1 Δ2) T D (n₁ + n))) ∎))
  Propstep1*-head-bis .(head ((Γ ∷ A) , (Δ ∷ A))) T D (Id-rule-head Γ Δ A pG) pHTD  (headMerging .(Γ ∷ A) .(Δ ∷ A) .T .D n) =
    Propstep1*-head-bis
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      (headMerging Γ Δ T D n)
  Propstep1*-head-bis .(G ∣ ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ)) T D (U-L G Γ Δ A n1 n2 refl pG) pHTD  (consMerging .G .(Γ ∷ (A , n1) ∷ (A , n2)) .Δ .T .D n m) =
    Propstep1*-head-bis
      (G ∣ (Γ ∷ (A , n1 + n2) , Δ))
      T
      D
      pG
      pHTD
      (consMerging
        G
        (Γ ∷ (A , n1 + n2))
        Δ
        T
        D
        n
        m)
  Propstep1*-head-bis .(G ∣ (Γ , (Δ ∷ (A , n1) ∷ (A , n2)))) T D (U-R G Γ Δ A n1 n2 refl pG) pHTD  (consMerging .G .Γ .(Δ ∷ (A , n1) ∷ (A , n2)) .T .D n m) = 
    Propstep1*-head-bis
      (G ∣ (Γ , Δ ∷ (A , n1 + n2)))
      T
      D
      pG
      pHTD
      (consMerging
        G
        Γ
        (Δ ∷ (A , n1 + n2))
        T
        D
        n
        m)
  Propstep1*-head-bis .(G ∣ ((Γ ∷ (A , n1 + n2)) , Δ)) T D (F-L G Γ Δ A n1 n2 refl pG) pHTD  (consMerging .G .(Γ ∷ (A , n1 + n2)) .Δ .T .D n m) =
    Propstep1*-head-bis
      (G ∣ (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
      T
      D
      pG
      pHTD
      (consMerging
        G
        (Γ ∷ (A , n1) ∷ (A , n2))
        Δ
        T
        D
        n
        m)
  Propstep1*-head-bis .(G ∣ (Γ , (Δ ∷ (A , n1 + n2)))) T D (F-R G Γ Δ A n1 n2 refl pG) pHTD  (consMerging .G .Γ .(Δ ∷ (A , n1 + n2)) .T .D n m) =
    Propstep1*-head-bis
      (G ∣ (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
      T
      D
      pG
      pHTD
      (consMerging
        G
        Γ
        (Δ ∷ (A , n1) ∷ (A , n2))
        T
        D
        n
        m)
  Propstep1*-head-bis .(head ((Γ ∷ (A , n1) ∷ (A , n2)) , Δ)) T D (U-L-head Γ Δ A n1 n2 refl pG) pHTD  (headMerging (Γ ∷ (A , n1) ∷ (A , n2)) Δ T D n) = 
    Propstep1*-head-bis
      (head (Γ ∷ (A , n1 + n2) , Δ))
      T
      D
      pG
      pHTD
      (headMerging
        (Γ ∷ (A , n1 + n2))
        Δ
        T
        D
        n)
  Propstep1*-head-bis .(head (Γ , (Δ ∷ (A , n1) ∷ (A , n2)))) T D (U-R-head Γ Δ A n1 n2 refl pG) pHTD  (headMerging .Γ .(Δ ∷ (A , n1) ∷ (A , n2)) .T .D n) = 
    Propstep1*-head-bis
      (head (Γ , Δ ∷ (A , n1 + n2)))
      T
      D
      pG
      pHTD
      (headMerging
        Γ
        (Δ ∷ (A , n1 + n2))
        T
        D
        n)
  Propstep1*-head-bis .(head ((Γ ∷ (A , n1 + n2)) , Δ)) T D (F-L-head Γ Δ A n1 n2 refl pG) pHTD  (headMerging .(Γ ∷ (A , n1 + n2)) .Δ .T .D n) =
    Propstep1*-head-bis
      (head (Γ ∷ (A , n1) ∷ (A , n2) , Δ))
      T
      D
      pG
      pHTD
      (headMerging
        (Γ ∷ (A , n1) ∷ (A , n2))
        Δ
        T
        D
        n)
  Propstep1*-head-bis .(head (Γ , (Δ ∷ (A , n1 + n2)))) T D (F-R-head Γ Δ A n1 n2 refl pG) pHTD  (headMerging .Γ .(Δ ∷ (A , n1 + n2)) .T .D n) =
    Propstep1*-head-bis
      (head (Γ , Δ ∷ (A , n1) ∷ (A , n2)))
      T
      D
      pG
      pHTD
      (headMerging
        Γ
        (Δ ∷ (A , n1) ∷ (A , n2))
        T
        D
        n)
  Propstep1*-head-bis .(G ∣ ((Γ ∷ (A , 0)) , Δ)) T D (E-L G Γ Δ A pG) pHTD  (consMerging .G .(Γ ∷ (A , 0)) .Δ .T .D n m) =
    Propstep1*-head-bis
      (G ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      (consMerging
        G
        Γ
        Δ
        T
        D
        n
        m)
  Propstep1*-head-bis .(G ∣ (Γ , (Δ ∷ (A , 0)))) T D (E-R G Γ Δ A pG) pHTD  (consMerging .G .Γ .(Δ ∷ (A , 0)) .T .D n m) = 
    Propstep1*-head-bis
      (G ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      (consMerging
        G
        Γ
        Δ
        T
        D
        n
        m)
  Propstep1*-head-bis .(head ((Γ ∷ (A , 0)) , Δ)) T D (E-L-head Γ Δ A pG) pHTD  (headMerging .(Γ ∷ (A , 0)) .Δ .T .D n) = 
    Propstep1*-head-bis
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      (headMerging
        Γ
        Δ
        T
        D
        n)
  Propstep1*-head-bis .(head (Γ , (Δ ∷ (A , 0)))) T D (E-R-head Γ Δ A pG) pHTD  (headMerging .Γ .(Δ ∷ (A , 0)) .T .D n) = 
    Propstep1*-head-bis
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      (headMerging
        Γ
        Δ
        T
        D
        n)
  Propstep1*-head-bis .(G ∣ ((Γ ∷ (A +S B , n)) , Δ)) T D (plus-L G Γ Δ A B n pG) pHTD  (consMerging .G .(Γ ∷ (A +S B , n)) .Δ .T .D n₁ m) =
    Propstep1*-head-bis
      (G ∣ (Γ ∷ (A , n) ∷ (B , n) , Δ))
      T
      D
      pG
      pHTD
      (consMerging
        G
        (Γ ∷ (A , n) ∷ (B , n))
        Δ
        T
        D
        n₁
        m)
  Propstep1*-head-bis .(G ∣ (Γ , (Δ ∷ (A +S B , n)))) T D (plus-R G Γ Δ A B n pG) pHTD  (consMerging .G .Γ .(Δ ∷ (A +S B , n)) .T .D n₁ m) = 
    Propstep1*-head-bis
      (G ∣ (Γ , Δ ∷ (A , n) ∷ (B , n)))
      T
      D
      pG
      pHTD
      (consMerging
        G
        Γ
        (Δ ∷ (A , n) ∷ (B , n))
        T
        D
        n₁
        m)
  Propstep1*-head-bis .(G ∣ ((Γ ∷ (A ⊔S B , n)) , Δ)) T D (max-L G Γ Δ A B n pG pG₁) pHTD  (consMerging .G .(Γ ∷ (A ⊔S B , n)) .Δ .T .D n₁ m) = 
    unionPropLeavesStep1*-head-bis
      (Propstep1*-head-bis
        (G ∣ (Γ ∷ (A , n) , Δ))
        T
        D
        pG
        pHTD
        (consMerging G (Γ ∷ (A , n)) Δ T D n₁ m))
      (Propstep1*-head-bis
        (G ∣ (Γ ∷ (B , n) , Δ))
        T
        D
        pG₁
        pHTD
        (consMerging G (Γ ∷ (B , n)) Δ T D n₁ m))
  Propstep1*-head-bis .(G ∣ (Γ , (Δ ∷ (A ⊔S B , n)))) T D (max-R G Γ Δ A B n pG) pHTD  (consMerging .G .Γ .(Δ ∷ (A ⊔S B , n)) .T .D n₁ m) = 
    Propstep1*-head-bis
      (G ∣ (Γ , Δ ∷ (A , n)) ∣ (Γ , Δ ∷ (B , n)))
      T
      D
      pG
      pHTD
      (consMerging
        (G ∣ (Γ , Δ ∷ (A , n)))
        Γ
        (Δ ∷ (B , n))
        T
        D
        n₁
        (consMerging
          G
          Γ
          (Δ ∷ (A , n))
          T
          D
          n₁
          m))
  Propstep1*-head-bis .(head ((Γ ∷ (A +S B , n)) , Δ)) T D (plus-L-head Γ Δ A B n pG) pHTD  (headMerging .(Γ ∷ (A +S B , n)) .Δ .T .D n₁) =
    Propstep1*-head-bis
      (head (Γ ∷ (A , n) ∷ (B , n), Δ))
      T
      D
      pG
      pHTD
      (headMerging (Γ ∷ (A , n) ∷ (B , n)) Δ T D n₁)
  Propstep1*-head-bis .(head (Γ , (Δ ∷ (A +S B , n)))) T D (plus-R-head Γ Δ A B n pG) pHTD  (headMerging .Γ .(Δ ∷ (A +S B , n)) .T .D n₁) = 
    Propstep1*-head-bis
      (head (Γ , Δ ∷ (A , n) ∷ (B , n)))
      T
      D
      pG
      pHTD
      (headMerging Γ (Δ ∷ (A , n) ∷ (B , n)) T D n₁)
  Propstep1*-head-bis .(head ((Γ ∷ (A ⊔S B , n)) , Δ)) T D (max-L-head Γ Δ A B n pG pG₁) pHTD  (headMerging .(Γ ∷ (A ⊔S B , n)) .Δ .T .D n₁) =
    unionPropLeavesStep1*-head-bis
      (Propstep1*-head-bis
        (head (Γ ∷ (A , n) , Δ))
        T
        D
        pG
        pHTD
        (headMerging (Γ ∷ (A , n)) Δ T D n₁))
      (Propstep1*-head-bis
        (head (Γ ∷ (B , n) , Δ))
        T
        D
        pG₁
        pHTD
        (headMerging (Γ ∷ (B , n)) Δ T D n₁))
  Propstep1*-head-bis .(head (Γ , (Δ ∷ (A ⊔S B , n)))) T D (max-R-head Γ Δ A B n pG) pHTD  (headMerging .Γ .(Δ ∷ (A ⊔S B , n)) .T .D n₁) = 
    Propstep1*-head-bis
      (head (Γ , Δ ∷ (A , n)) ∣ (Γ , Δ ∷ (B , n)))
      T
      D
      pG
      pHTD
      (consMerging
        (head (Γ , Δ ∷ (A , n)))
        Γ
        (Δ ∷ (B , n))
        T
        D
        n₁
        (headMerging
          Γ
          (Δ ∷ (A , n))
          T
          D
          n₁))
  Propstep1*-head-bis .(head (Γ , (Δ ∷ (one , suc k)))) T D (◆1-rule Γ Δ ◆Γ ◆Δ refl refl k pG) pHTD  (headMerging .Γ .(Δ ∷ (one , suc k)) .T .D n) =
    consP1head-bis
      Γ
      Δ
      T
      D
      ◆Γ
      ◆Δ
      k
      pG
      n
      ([]P1head-bis T D)
  Propstep1*-head-bis .(head (Γ , Δ)) T D (◆-rule Γ Δ ◆Γ ◆Δ refl refl pG) pHTD  (headMerging .Γ .Δ .T .D n) =
    consP1head-bis'
      Γ
      Δ
      T
      D
      ◆Γ
      ◆Δ
      pG
      n
      ([]P1head-bis T D)
  Propstep1*-head-bis .(G ∣ (Γ' , Δ')) T D (seq-exchange G Γ Γ' Δ Δ' x x₁ pG) pHTD  (consMerging .G .Γ' .Δ' .T .D n m) =
    Propstep1*-head-bis
      (G ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      (consMerging
        G
        Γ
        Δ
        T
        D
        n
        m)
  Propstep1*-head-bis .(head (Γ' , Δ')) T D (seq-exchange-head Γ Γ' Δ Δ' x x₁ pG) pHTD  (headMerging .Γ' .Δ' .T .D n) = 
    Propstep1*-head-bis
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      (headMerging
        Γ
        Δ
        T
        D
        n)
  Propstep1*-head-bis G T D (hseq-exchange G₁ .G x pG) pHTD m = 
    Propstep1*-head-bis
      G₁
      T
      D
      pG
      pHTD
      (MergingExchange G G₁ T D m (LHSeqExchangeSym x))
  Propstep1*-head-bis .(G ∣ ((Γ ∷ (-S A , n)) , Δ)) T D (minus-L G Γ Δ A n pG) pHTD (consMerging .G .(Γ ∷ (-S A , n)) .Δ .T .D n₁ m) =
    Propstep1*-head-bis
      (G ∣ (Γ , Δ ∷ (A , n)))
      T
      D
      pG
      pHTD
      (consMerging
        G
        Γ
        (Δ ∷ (A , n))
        T
        D
        n₁
        m)
  Propstep1*-head-bis .(G ∣ (Γ , (Δ ∷ (-S A , n)))) T D (minus-R G Γ Δ A n pG) pHTD (consMerging .G .Γ .(Δ ∷ (-S A , n)) .T .D n₁ m) = 
    Propstep1*-head-bis
      (G ∣ (Γ ∷ (A , n) , Δ))
      T
      D
      pG
      pHTD
      (consMerging
        G
        (Γ ∷ (A , n))
        Δ
        T
        D
        n₁
        m)
  Propstep1*-head-bis .(G ∣ ((Γ ∷ (botAG , n)) , Δ)) T D (Z-L G Γ Δ n pG) pHTD (consMerging .G .(Γ ∷ (botAG , n)) .Δ .T .D n₁ m) =
    Propstep1*-head-bis
      (G ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      (consMerging
        G
        Γ
        Δ
        T
        D
        n₁
        m)
  Propstep1*-head-bis .(G ∣ (Γ , (Δ ∷ (botAG , n)))) T D (Z-R G Γ Δ n pG) pHTD (consMerging .G .Γ .(Δ ∷ (botAG , n)) .T .D n₁ m) = 
    Propstep1*-head-bis
      (G ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      (consMerging
        G
        Γ
        Δ
        T
        D
        n₁
        m)
  Propstep1*-head-bis .(G ∣ (Γ , (Δ ∷ (A ⊓S B , n)))) T D (min-R G Γ Δ A B n pG pG₁) pHTD (consMerging .G .Γ .(Δ ∷ (A ⊓S B , n)) .T .D n₁ m) = 
    unionPropLeavesStep1*-head-bis
      (Propstep1*-head-bis
        (G ∣ (Γ , Δ ∷ (A , n)))
        T
        D
        pG
        pHTD
        (consMerging G Γ (Δ ∷ (A , n)) T D n₁ m))
      (Propstep1*-head-bis
        (G ∣ (Γ , Δ ∷ (B , n)))
        T
        D
        pG₁
        pHTD
        (consMerging G Γ (Δ ∷ (B , n)) T D n₁ m))
  Propstep1*-head-bis .(G ∣ ((Γ ∷ (A ⊓S B , n)) , Δ)) T D (min-L G Γ Δ A B n pG) pHTD (consMerging .G .(Γ ∷ (A ⊓S B , n)) .Δ .T .D n₁ m) = 
    Propstep1*-head-bis
      (G ∣ (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ))
      T
      D
      pG
      pHTD
      (consMerging
        (G ∣ (Γ ∷ (A , n) , Δ))
        (Γ ∷ (B , n))
        Δ
        T
        D
        n₁
        (consMerging
          G
          (Γ ∷ (A , n))
          Δ
          T
          D
          n₁
          m))
  Propstep1*-head-bis .(head ((Γ ∷ (-S A , n)) , Δ)) T D (minus-L-head Γ Δ A n pG) pHTD (headMerging .(Γ ∷ (-S A , n)) .Δ .T .D n₁) =
    Propstep1*-head-bis
      (head (Γ , Δ ∷ (A , n)))
      T
      D
      pG
      pHTD
      (headMerging
        Γ
        (Δ ∷ (A , n))
        T
        D
        n₁)
  Propstep1*-head-bis .(head (Γ , (Δ ∷ (-S A , n)))) T D (minus-R-head Γ Δ A n pG) pHTD (headMerging .Γ .(Δ ∷ (-S A , n)) .T .D n₁) = 
    Propstep1*-head-bis
      (head (Γ ∷ (A , n) , Δ))
      T
      D
      pG
      pHTD
      (headMerging
        (Γ ∷ (A , n))
        Δ
        T
        D
        n₁)
  Propstep1*-head-bis .(head ((Γ ∷ (botAG , n)) , Δ)) T D (Z-L-head Γ Δ n pG) pHTD (headMerging .(Γ ∷ (botAG , n)) .Δ .T .D n₁) =
    Propstep1*-head-bis
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      (headMerging
        Γ
        Δ
        T
        D
        n₁)
  Propstep1*-head-bis .(head (Γ , (Δ ∷ (botAG , n)))) T D (Z-R-head Γ Δ n pG) pHTD (headMerging .Γ .(Δ ∷ (botAG , n)) .T .D n₁) = 
    Propstep1*-head-bis
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      (headMerging
        Γ
        Δ
        T
        D
        n₁)
  Propstep1*-head-bis .(head (Γ , (Δ ∷ (A ⊓S B , n)))) T D (min-R-head Γ Δ A B n pG pG₁) pHTD (headMerging .Γ .(Δ ∷ (A ⊓S B , n)) .T .D n₁) = 
    unionPropLeavesStep1*-head-bis
      (Propstep1*-head-bis
        (head (Γ , Δ ∷ (A , n)))
        T
        D
        pG
        pHTD
        (headMerging Γ (Δ ∷ (A , n)) T D n₁))
      (Propstep1*-head-bis
        (head (Γ , Δ ∷ (B , n)))
        T
        D
        pG₁
        pHTD
        (headMerging Γ (Δ ∷ (B , n)) T D n₁))
  Propstep1*-head-bis .(head ((Γ ∷ (A ⊓S B , n)) , Δ)) T D (min-L-head Γ Δ A B n pG) pHTD (headMerging .(Γ ∷ (A ⊓S B , n)) .Δ .T .D n₁) = 
    Propstep1*-head-bis
      (head (Γ ∷ (A , n) , Δ) ∣ (Γ ∷ (B , n) , Δ))
      T
      D
      pG
      pHTD
      (consMerging
        (head (Γ ∷ (A , n) , Δ))
        (Γ ∷ (B , n))
        Δ
        T
        D
        n₁
        (headMerging
          (Γ ∷ (A , n))
          Δ
          T
          D
          n₁))
  Propstep1*-head-bis .(G ∣ (Γ , Δ ∷ (one , k))) T D (1-rule G Γ Δ k pG) pHTD (consMerging .G .Γ .(Δ ∷ (one , k)) T D n m) =
    Propstep1*-head-bis
      (G ∣ (Γ , Δ))
      T
      D
      pG
      pHTD
      (consMerging G Γ Δ T D n m)
  Propstep1*-head-bis .(head (Γ , Δ ∷ (one , k))) T D (1-rule-head Γ Δ k pG) pHTD (headMerging .Γ .(Δ ∷ (one , k)) T D n) =
    Propstep1*-head-bis
      (head (Γ , Δ))
      T
      D
      pG
      pHTD
      (headMerging Γ Δ T D n)
--}}}
