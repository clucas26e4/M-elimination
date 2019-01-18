module Syntax.MGA-SR-Can.Properties where
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
  open import Syntax.MGA-SR-Can

  MGA-SR†Cong :
    {G G' : LHSeq} ->
    MGA-SR† G ->
    G ≡ G' ->
    MGA-SR† G'
--{{{
  MGA-SR†Cong PG refl = PG
--}}}

  ΔGen :
    (G : LHSeq) ->
    MGA-SR† (G ∣ ([] , []))
--{{{
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
--}}}

  UnfoldMGA-SR†Copy-LGen :
    (G : LHSeq) ->
    (T T' D : ListLTerm) ->
    (n : ℕ) ->
    MGA-SR† (G ∣ (union (copy T (suc n)) T' , D)) ->
    MGA-SR† (G ∣ (union (union (copy T n) T) T' , D))
--{{{
  UnfoldMGA-SR†Copy-LGen G [] T' D zero p =
    p
  UnfoldMGA-SR†Copy-LGen G [] T' D (suc n) p =
    p
  UnfoldMGA-SR†Copy-LGen G (T ∷ (A , n1)) T' D zero p =
    MGA-SR†Cong
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
  UnfoldMGA-SR†Copy-LGen G (T ∷ (A , n1)) T' D (suc n) p =
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
            (UnfoldMGA-SR†Copy-LGen
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
                (MGA-SR†Cong
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
--}}}

  UnfoldMGA-SR†Copy-L :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    (n : ℕ) ->
    MGA-SR† (G ∣ (copy T (suc n) , D)) ->
    MGA-SR† (G ∣ (union (copy T n) T , D))
--{{{
  UnfoldMGA-SR†Copy-L G T D n = UnfoldMGA-SR†Copy-LGen G T [] D n
--}}}



  UnfoldMGA-SR†Copy-RGen :
    (G : LHSeq) ->
    (T D D' : ListLTerm) ->
    (n : ℕ) ->
    MGA-SR† (G ∣ (T , union (copy D (suc n)) D')) ->
    MGA-SR† (G ∣ (T , union (union (copy D n) D) D'))
--{{{
  UnfoldMGA-SR†Copy-RGen G T [] D' zero p =
    p
  UnfoldMGA-SR†Copy-RGen G T [] D' (suc n) p =
    p
  UnfoldMGA-SR†Copy-RGen G T (D ∷ (A , n1)) D' zero p =
    MGA-SR†Cong
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
  UnfoldMGA-SR†Copy-RGen G T (D ∷ (A , n1)) D' (suc n) p =
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
            (UnfoldMGA-SR†Copy-RGen
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
                (MGA-SR†Cong
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
--}}}

  UnfoldMGA-SR†Copy-R :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    (n : ℕ) ->
    MGA-SR† (G ∣ (T , copy D (suc n))) ->
    MGA-SR† (G ∣ (T , union (copy D n) D))
--{{{
  UnfoldMGA-SR†Copy-R G T D n = UnfoldMGA-SR†Copy-RGen G T D [] n
--}}}

  UnfoldMGA-SR†Copy-L-head-Gen :
    (T T' D : ListLTerm) ->
    (n : ℕ) ->
    MGA-SR† (head (union (copy T (suc n)) T' , D)) ->
    MGA-SR† (head (union (union (copy T n) T) T' , D))
--{{{
  UnfoldMGA-SR†Copy-L-head-Gen [] T' D zero p =
    p
  UnfoldMGA-SR†Copy-L-head-Gen [] T' D (suc n) p =
    p
  UnfoldMGA-SR†Copy-L-head-Gen (T ∷ (A , n1)) T' D zero p =
    MGA-SR†Cong
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
  UnfoldMGA-SR†Copy-L-head-Gen (T ∷ (A , n1)) T' D (suc n) p =
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
            (UnfoldMGA-SR†Copy-L-head-Gen
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
                (MGA-SR†Cong
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
--}}}

  UnfoldMGA-SR†Copy-L-head :
    (T D : ListLTerm) ->
    (n : ℕ) ->
    MGA-SR† (head (copy T (suc n) , D)) ->
    MGA-SR† (head (union (copy T n) T , D))
--{{{
  UnfoldMGA-SR†Copy-L-head T D n = UnfoldMGA-SR†Copy-L-head-Gen T [] D n
--}}}  

  UnfoldMGA-SR†Copy-R-head-Gen :
    (T D D' : ListLTerm) ->
    (n : ℕ) ->
    MGA-SR† (head (T , union (copy D (suc n)) D')) ->
    MGA-SR† (head (T , union (union (copy D n) D) D'))
--{{{
  UnfoldMGA-SR†Copy-R-head-Gen T [] D' zero p =
    p
  UnfoldMGA-SR†Copy-R-head-Gen T [] D' (suc n) p =
    p
  UnfoldMGA-SR†Copy-R-head-Gen T (D ∷ (A , n1)) D' zero p =
    MGA-SR†Cong
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
  UnfoldMGA-SR†Copy-R-head-Gen T (D ∷ (A , n1)) D' (suc n) p =
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
            (UnfoldMGA-SR†Copy-R-head-Gen
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
                (MGA-SR†Cong
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
--}}}

  UnfoldMGA-SR†Copy-R-head :
    (T D : ListLTerm) ->
    (n : ℕ) ->
    MGA-SR† (head (T , copy D (suc n))) ->
    MGA-SR† (head (T , union (copy D n) D))
--{{{
  UnfoldMGA-SR†Copy-R-head T D n = UnfoldMGA-SR†Copy-R-head-Gen T D [] n
--}}}

  MGA-SR†CongKeep#◆ :
    {G G' : LHSeq} ->
    (p : MGA-SR† G) ->
    (G=G' : G ≡ G') ->
    #◆ (MGA-SR†Cong p G=G') ≡ #◆ p
--{{{
  MGA-SR†CongKeep#◆ p refl =
    refl
--}}}


  ΔGenNo◆ :
    (G : LHSeq) ->
    #◆ (ΔGen G) ≡ 0
--{{{
  ΔGenNo◆ (head (T , D)) =
    refl
  ΔGenNo◆ (G ∣ (T , D)) =
    ΔGenNo◆ G
--}}}

  UnfoldMGA-SR†Copy-LGenKeep#◆ :
    (G : LHSeq) ->
    (T T' D : ListLTerm) ->
    (n : ℕ) ->
    (p : MGA-SR† (G ∣ (union (copy T (suc n)) T' , D))) ->
    #◆ (UnfoldMGA-SR†Copy-LGen G T T' D n p) ≡ #◆ p
--{{{
  UnfoldMGA-SR†Copy-LGenKeep#◆ G [] T' D zero p =
    refl
  UnfoldMGA-SR†Copy-LGenKeep#◆ G [] T' D (suc n) p =
    refl
  UnfoldMGA-SR†Copy-LGenKeep#◆ G (T ∷ (A , n')) T' D zero p =
    MGA-SR†CongKeep#◆
      p
      (cong₂
        (λ x y → G ∣ (union (x ∷ (A , y)) T' , D))
        (copy T 1 ≡⟨ idCopy T ⟩ T ≡⟨ sym (union[]T=T T) ⟩ refl)
        (sym a=a+0))
  UnfoldMGA-SR†Copy-LGenKeep#◆ G (T ∷ (A , n')) T' D (suc n) p =
    trans
      (UnfoldMGA-SR†Copy-LGenKeep#◆
        G
        T
        (T' ∷ (A , n' + n * n' + n'))
        D
        (suc n)
        (seq-exchange G
          (union (copy T (suc (suc n)) ∷ (A , n' + n * n' + n')) T')
          (union (copy T (suc (suc n))) T' ∷ (A , n' + n * n' + n')) D D
          (exchangeUnionLast (copy T (suc (suc n))) T'
          (A , n' + n * n' + n'))
          idLE
          (MGA-SR†Cong p
            (cong (λ x → G ∣ (union (copy T (suc (suc n)) ∷ (A , x)) T' , D))
              (n' + (n' + n * n')
                ≡⟨ cong
                     (_+_ n')
                     (+-comm n' (n * n')) ⟩
              n' + (n * n' + n')
                ≡⟨ sym (+-assoc n' (n * n') n') ⟩ refl)))))
      (MGA-SR†CongKeep#◆
        p
        (cong
          (λ x → G ∣ (union (copy T (suc (suc n)) ∷ (A , x)) T' , D))
          (n' + (n' + n * n') ≡⟨ cong (_+_ n') (+-comm n' (n * n')) ⟩ n' + (n * n' + n') ≡⟨ sym (+-assoc n' (n * n') n') ⟩ refl)))
--}}}

  UnfoldMGA-SR†Copy-LKeep#◆ :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    (n : ℕ) ->
    (p : MGA-SR† (G ∣ (copy T (suc n) , D))) ->
    #◆ (UnfoldMGA-SR†Copy-L G T D n p) ≡ #◆ p
--{{{
  UnfoldMGA-SR†Copy-LKeep#◆ G T D n p = UnfoldMGA-SR†Copy-LGenKeep#◆ G T [] D n p
--}}}  

  UnfoldMGA-SR†Copy-RGenKeep#◆ :
    (G : LHSeq) ->
    (T D D' : ListLTerm) ->
    (n : ℕ) ->
    (p : MGA-SR† (G ∣ ( T , union (copy D (suc n)) D'))) ->
    #◆ (UnfoldMGA-SR†Copy-RGen G T D D' n p) ≡ #◆ p
--{{{
  UnfoldMGA-SR†Copy-RGenKeep#◆ G T [] D' zero p =
    refl
  UnfoldMGA-SR†Copy-RGenKeep#◆ G T [] D' (suc n) p =
    refl
  UnfoldMGA-SR†Copy-RGenKeep#◆ G T (D ∷ (A , n')) D' zero p =
    MGA-SR†CongKeep#◆
      p
      (cong₂
        (λ x y → G ∣ (T , union (x ∷ (A , y)) D'))
        (copy D 1 ≡⟨ idCopy D ⟩ D ≡⟨ sym (union[]T=T D) ⟩ refl)
        (sym a=a+0))
  UnfoldMGA-SR†Copy-RGenKeep#◆ G T (D ∷ (A , n')) D' (suc n) p =
    trans
      (UnfoldMGA-SR†Copy-RGenKeep#◆
        G
        T
        D
        (D' ∷ (A , n' + n * n' + n'))
        (suc n)
        (seq-exchange
          G
          T
          T
          (union (copy D (suc (suc n)) ∷ (A , n' + n * n' + n')) D')
          (union (copy D (suc (suc n))) D' ∷ (A , n' + n * n' + n'))
          idLE
          (exchangeUnionLast (copy D (suc (suc n))) D'
          (A , n' + n * n' + n'))
          (MGA-SR†Cong p
            (cong (λ x → G ∣ (T , union (copy D (suc (suc n)) ∷ (A , x)) D'))
              (n' + (n' + n * n')
                ≡⟨ cong
                     (_+_ n')
                     (+-comm n' (n * n')) ⟩
              n' + (n * n' + n')
                ≡⟨ sym (+-assoc n' (n * n') n') ⟩ refl)))))
      (MGA-SR†CongKeep#◆
        p
        (cong
          (λ x → G ∣ (T , union (copy D (suc (suc n)) ∷ (A , x)) D'))
          (n' + (n' + n * n') ≡⟨ cong (_+_ n') (+-comm n' (n * n')) ⟩ n' + (n * n' + n') ≡⟨ sym (+-assoc n' (n * n') n') ⟩ refl)))
--}}}

  UnfoldMGA-SR†Copy-RKeep#◆ :
    (G : LHSeq) ->
    (T D : ListLTerm) ->
    (n : ℕ) ->
    (p : MGA-SR† (G ∣ (T , copy D (suc n)))) ->
    #◆ (UnfoldMGA-SR†Copy-R G T D n p) ≡ #◆ p
--{{{
  UnfoldMGA-SR†Copy-RKeep#◆ G T D n p = UnfoldMGA-SR†Copy-RGenKeep#◆ G T D [] n p
--}}}

  UnfoldMGA-SR†Copy-L-head-GenKeep#◆ :
    (T T' D : ListLTerm) ->
    (n : ℕ) ->
    (p : MGA-SR† (head (union (copy T (suc n)) T' , D))) ->
    #◆ (UnfoldMGA-SR†Copy-L-head-Gen T T' D n p) ≡ #◆ p
--{{{
  UnfoldMGA-SR†Copy-L-head-GenKeep#◆ [] T' D zero p =
    refl
  UnfoldMGA-SR†Copy-L-head-GenKeep#◆ [] T' D (suc n) p =
    refl
  UnfoldMGA-SR†Copy-L-head-GenKeep#◆ (T ∷ (A , n')) T' D zero p =
    MGA-SR†CongKeep#◆
      p
      (cong₂
        (λ x y → head (union (x ∷ (A , y)) T' , D))
        (copy T 1 ≡⟨ idCopy T ⟩ T ≡⟨ sym (union[]T=T T) ⟩ refl)
        (sym a=a+0))
  UnfoldMGA-SR†Copy-L-head-GenKeep#◆ (T ∷ (A , n')) T' D (suc n) p =
    trans
      (UnfoldMGA-SR†Copy-L-head-GenKeep#◆
        T
        (T' ∷ (A , n' + n * n' + n'))
        D
        (suc n)
        (seq-exchange-head
          (union (copy T (suc (suc n)) ∷ (A , n' + n * n' + n')) T')
          (union (copy T (suc (suc n))) T' ∷ (A , n' + n * n' + n')) D D
          (exchangeUnionLast (copy T (suc (suc n))) T'
          (A , n' + n * n' + n'))
          idLE
          (MGA-SR†Cong p
            (cong (λ x → head (union (copy T (suc (suc n)) ∷ (A , x)) T' , D))
              (n' + (n' + n * n')
                ≡⟨ cong
                     (_+_ n')
                     (+-comm n' (n * n')) ⟩
              n' + (n * n' + n')
                ≡⟨ sym (+-assoc n' (n * n') n') ⟩ refl)))))
      (MGA-SR†CongKeep#◆
        p
        (cong
          (λ x → head (union (copy T (suc (suc n)) ∷ (A , x)) T' , D))
          (n' + (n' + n * n') ≡⟨ cong (_+_ n') (+-comm n' (n * n')) ⟩ n' + (n * n' + n') ≡⟨ sym (+-assoc n' (n * n') n') ⟩ refl)))
--}}}

  UnfoldMGA-SR†Copy-L-head-Keep#◆ :
    (T D : ListLTerm) ->
    (n : ℕ) ->
    (p : MGA-SR† (head (copy T (suc n) , D))) ->
    #◆ (UnfoldMGA-SR†Copy-L-head T D n p) ≡ #◆ p
--{{{
  UnfoldMGA-SR†Copy-L-head-Keep#◆ T D n p = UnfoldMGA-SR†Copy-L-head-GenKeep#◆ T [] D n p
--}}}

  UnfoldMGA-SR†Copy-R-head-GenKeep#◆ :
    (T D D' : ListLTerm) ->
    (n : ℕ) ->
    (p : MGA-SR† (head ( T , union (copy D (suc n)) D'))) ->
    #◆ (UnfoldMGA-SR†Copy-R-head-Gen T D D' n p) ≡ #◆ p
--{{{
  UnfoldMGA-SR†Copy-R-head-GenKeep#◆ T [] D' zero p =
    refl
  UnfoldMGA-SR†Copy-R-head-GenKeep#◆ T [] D' (suc n) p =
    refl
  UnfoldMGA-SR†Copy-R-head-GenKeep#◆ T (D ∷ (A , n')) D' zero p =
    MGA-SR†CongKeep#◆
      p
      (cong₂
        (λ x y → head (T , union (x ∷ (A , y)) D'))
        (copy D 1 ≡⟨ idCopy D ⟩ D ≡⟨ sym (union[]T=T D) ⟩ refl)
        (sym a=a+0))
  UnfoldMGA-SR†Copy-R-head-GenKeep#◆ T (D ∷ (A , n')) D' (suc n) p =
    trans
      (UnfoldMGA-SR†Copy-R-head-GenKeep#◆
        T
        D
        (D' ∷ (A , n' + n * n' + n'))
        (suc n)
        (seq-exchange-head
          T
          T
          (union (copy D (suc (suc n)) ∷ (A , n' + n * n' + n')) D')
          (union (copy D (suc (suc n))) D' ∷ (A , n' + n * n' + n'))
          idLE
          (exchangeUnionLast (copy D (suc (suc n))) D'
          (A , n' + n * n' + n'))
          (MGA-SR†Cong p
            (cong (λ x → head (T , union (copy D (suc (suc n)) ∷ (A , x)) D'))
              (n' + (n' + n * n')
                ≡⟨ cong
                     (_+_ n')
                     (+-comm n' (n * n')) ⟩
              n' + (n * n' + n')
                ≡⟨ sym (+-assoc n' (n * n') n') ⟩ refl)))))
      (MGA-SR†CongKeep#◆
        p
        (cong
          (λ x → head (T , union (copy D (suc (suc n)) ∷ (A , x)) D'))
          (n' + (n' + n * n') ≡⟨ cong (_+_ n') (+-comm n' (n * n')) ⟩ n' + (n * n' + n') ≡⟨ sym (+-assoc n' (n * n') n') ⟩ refl)))
--}}}

  UnfoldMGA-SR†Copy-R-head-Keep#◆ :
    (T D : ListLTerm) ->
    (n : ℕ) ->
    (p : MGA-SR† (head (T , copy D (suc n)))) ->
    #◆ (UnfoldMGA-SR†Copy-R-head T D n p) ≡ #◆ p
--{{{
  UnfoldMGA-SR†Copy-R-head-Keep#◆ T D n p = UnfoldMGA-SR†Copy-R-head-GenKeep#◆ T D [] n p
--}}}
