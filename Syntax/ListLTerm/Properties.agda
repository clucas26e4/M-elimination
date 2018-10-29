module Syntax.ListLTerm.Properties where
  
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary
  open import Data.Product
  
  {- Syntax -}
  open import Syntax.LTerm
  open import Syntax.Term
  open import Syntax.ListLTerm

  ListExchangeSubst :
    {Γ Γ' : ListLTerm} ->
    (Γ=Γ' : Γ ≡ Γ') ->
    ListExchange Γ Γ'
--{{{
  ListExchangeSubst refl =
    idLE
--}}}
    
  ListExchangeCong :
    {Γ1 Γ2 Γ3 : ListLTerm} ->
    (Γ1=Γ2 : Γ1 ≡ Γ2) ->
    (LEΓ1Γ3 : ListExchange Γ1 Γ3) ->
    ListExchange Γ2 Γ3
--{{{
  ListExchangeCong refl LEΓ1Γ3 = LEΓ1Γ3
--}}}

  copyKeepExchange :
    (Γ Γ' : ListLTerm) ->
    (Γ=Γ' : ListExchange Γ Γ') ->
    (n : ℕ) ->
    ListExchange (copy Γ n) (copy Γ' n)
--{{{
  copyKeepExchange Γ Γ' Γ=Γ' zero =
    idLE
  copyKeepExchange Γ .Γ idLE (suc n) =
    idLE
  copyKeepExchange (Γ ∷ (A , n1) ∷ (B , n2)) (Γ' ∷ .(B , n2) ∷ .(A , n1)) (exLE Γ=Γ') (suc n) =
    exLE (copyKeepExchange Γ Γ' Γ=Γ' (suc n))
  copyKeepExchange Γ Γ' (transLE {Γ₂ = Γ₂} Γ=Γ' Γ=Γ'') (suc n) =
    transLE
      (copyKeepExchange Γ Γ₂ Γ=Γ' (suc n))
      (copyKeepExchange Γ₂ Γ' Γ=Γ'' (suc n))
  copyKeepExchange (Γ ∷ (A , n1)) (Γ' ∷ .(A , n1)) (indLE Γ=Γ') (suc n) =
    indLE
      (copyKeepExchange Γ Γ' Γ=Γ' (suc n))
--}}}

  copyUnion :
    (T T' : ListLTerm) ->
    (n : ℕ) ->
    copy (union T T') n ≡ union (copy T n) (copy T' n)
--{{{
  copyUnion T T' zero =
    refl
  copyUnion T [] (suc n) =
    refl
  copyUnion T (T' ∷ (A , n')) (suc n) =
    cong
      (λ x -> x ∷ (A , n' + n * n'))
      (copyUnion T T' (suc n))
--}}}

  exchangeUnionLast :
    (T T' : ListLTerm) ->
    (A : LTerm) ->
    ListExchange (union (T ∷ A) T') ((union T T') ∷ A)
--{{{
  exchangeUnionLast T [] A =
    idLE
  exchangeUnionLast T (T' ∷ A₁) A =
    transLE
      {Γ₂ = (union T T') ∷ A ∷ A₁}
      (indLE
        (exchangeUnionLast T T' A))
      (exLE
        idLE)
--}}}

  ListExchangeSym :
    {T T' : ListLTerm} ->
    (T=T : ListExchange T T') ->
    ListExchange T' T
--{{{
  ListExchangeSym idLE =
    idLE
  ListExchangeSym (exLE T=T') =
    exLE (ListExchangeSym T=T')
  ListExchangeSym (transLE T=T' T=T'') =
    transLE (ListExchangeSym T=T'') (ListExchangeSym T=T')
  ListExchangeSym (indLE T=T') =
    indLE (ListExchangeSym T=T')
--}}}

  union[]T=T :
    (T : ListLTerm) ->
    union [] T ≡ T
--{{{
  union[]T=T [] =
    refl
  union[]T=T (T ∷ A) =
    cong
      (λ x -> x ∷ A)
      (union[]T=T T)
--}}}

  ListExchangeUnion :
    (T T' : ListLTerm) ->
    ListExchange (union T T') (union T' T)
--{{{
  ListExchangeUnion [] [] =
    idLE
  ListExchangeUnion [] (T' ∷ A) = 
    ListExchangeCong
      (sym (union[]T=T (T' ∷ A)))
      idLE
  ListExchangeUnion (T ∷ A) [] =
    ListExchangeSym
      (ListExchangeCong
        (sym (union[]T=T (T ∷ A)))
        idLE)
  ListExchangeUnion (T ∷ A) (T' ∷ A₁) =
    transLE {Γ₂ = union T' T ∷ A ∷ A₁}
      (indLE
        (ListExchangeUnion (T ∷ A) T'))
      (transLE {Γ₂ = union T' T ∷ A₁ ∷ A}
        (exLE
          idLE)
        (indLE
          (ListExchangeSym (exchangeUnionLast T' T A₁))))
--}}}

  unionKeepExchangeRight :
    (T1 : ListLTerm) ->
    {T2 T3 : ListLTerm} ->
    (T2=T3 : ListExchange T2 T3) ->
    ListExchange (union T1 T2) (union T1 T3)
--{{{
  unionKeepExchangeRight T1 idLE =
    idLE
  unionKeepExchangeRight T1 (exLE T2=T3) =
    exLE (unionKeepExchangeRight T1 T2=T3)
  unionKeepExchangeRight T1 (transLE T2=T3 T2=T4) =
    transLE (unionKeepExchangeRight T1 T2=T3) (unionKeepExchangeRight T1 T2=T4)
  unionKeepExchangeRight T1 (indLE T2=T3) =
    indLE (unionKeepExchangeRight T1 T2=T3)
--}}}

  unionKeepExchangeLeft :
    {T1 T2 : ListLTerm} ->
    (T1=T2 : ListExchange T1 T2) ->
    (T3 : ListLTerm) ->
    ListExchange (union T1 T3) (union T2 T3)
--{{{
  unionKeepExchangeLeft {T1} {T2} T1=T2 T3 =
    transLE
      (ListExchangeUnion T1 T3)
      (transLE
        (unionKeepExchangeRight T3 T1=T2)
        (ListExchangeUnion T3 T2))
--}}}

  doubleCopy :
    (T : ListLTerm) ->
    (n1 n2 : ℕ) ->
    copy (copy T n1) n2 ≡ copy T (n1 * n2)
--{{{
  doubleCopy T n1 zero =
    cong
      (λ x -> copy T x)
      (sym (a*0=0 n1))
  doubleCopy T zero (suc n2) =
    refl
  doubleCopy [] (suc n1) (suc n2) =
    refl
  doubleCopy (T ∷ (A , n)) (suc n1) (suc n2) =
    begin
      copy (copy T (suc n1)) (suc n2) ∷ (A , n + n1 * n + n2 * (n + n1 * n))
        ≡⟨ cong
             (λ x -> copy (copy T (suc n1)) (suc n2) ∷ (A , x))
             (begin
                n + n1 * n + n2 * (n + n1 * n)
                  ≡⟨ +-assoc n (n1 * n) (n2 * (n + n1 * n)) ⟩
                n + (n1 * n + n2 * (n + n1 * n))
                  ≡⟨ cong
                       (λ x -> n + (n1 * n + x))
                       (c*a+b=c*a+c*b n (n1 * n) n2) ⟩
                n + (n1 * n + (n2 * n + n2 * (n1 * n)))
                  ≡⟨ cong
                       (λ x -> n + x)
                       (sym (+-assoc (n1 * n) (n2 * n) (n2 * (n1 * n)))) ⟩
                n + (n1 * n + n2 * n + n2 * (n1 * n))
                  ≡⟨ cong
                       (λ x -> n + (x + n2 * (n1 * n)))
                       (+-comm (n1 * n) (n2 * n)) ⟩
                n + (n2 * n + n1 * n + n2 * (n1 * n))
                  ≡⟨ cong
                       (λ x -> n + x)
                       (+-assoc (n2 * n) (n1 * n) (n2 * (n1 * n))) ⟩
                n + (n2 * n + (n1 * n + n2 * (n1 * n)))
                  ≡⟨ refl ⟩
                n + (n2 * n + ((suc n2) * (n1 * n)))
                  ≡⟨ cong
                       (λ x -> n + (n2 * n + x))
                       (sym (*-assoc (suc n2) n1 n)) ⟩
                n + (n2 * n + ((suc n2) * n1 * n))
                  ≡⟨ cong
                       (λ x -> n + x)
                       (sym (a+b*c=a*c+b*c n2 ((suc n2) * n1) n)) ⟩
                n + (n2 + ((suc n2) * n1 )) * n
                  ≡⟨ cong
                       (λ x -> n + (n2 + x) * n)
                       (*-comm (suc n2) n1) ⟩
                n + (n2 + (n1 * (suc n2))) * n ∎) ⟩
      copy (copy T (suc n1)) (suc n2) ∷ (A , n + (n2 + n1 * suc n2) * n)
        ≡⟨ cong
             (λ x -> x ∷ (A , n + (n2 + n1 * suc n2) * n))
             (doubleCopy T (suc n1) (suc n2)) ⟩
      copy T ((suc n1) * (suc n2)) ∷ (A , n + (n2 + n1 * suc n2) * n) ∎
--}}}

  copyKeep◆ :
    {Γ : ListLTerm} ->
    ◆List Γ ->
    (n : ℕ) ->
    ◆List (copy Γ n)
--{{{
  copyKeep◆ ◆Γ zero =
    ◆[]
  copyKeep◆ ◆[] (suc n) =
    ◆[]
  copyKeep◆ (◆∷ Γ A n₁ ◆Γ) (suc n) =
    ◆∷ (copy Γ (suc n)) A ((suc n) * n₁)
      (copyKeep◆ ◆Γ (suc n))
--}}}
  
  unionKeep◆ :
    {Γ Γ' : ListLTerm} ->
    (◆Γ : ◆List Γ) ->
    (◆Γ' : ◆List Γ') ->
    ◆List (union Γ Γ')
--{{{
  unionKeep◆ ◆Γ ◆[] =
    ◆Γ
  unionKeep◆ {Γ₁} ◆Γ (◆∷ Γ A n ◆Γ') =
    ◆∷ (union Γ₁ Γ) A n (unionKeep◆ ◆Γ ◆Γ')
--}}}

  copyRemove :
    {Γ : ListLTerm} ->
    (◆Γ : ◆List Γ) ->
    (n : ℕ) ->
    copy (remove◆ ◆Γ) n ≡ remove◆ (copyKeep◆ ◆Γ n)
--{{{
  copyRemove ◆Γ zero =
    refl
  copyRemove ◆[] (suc n) =
    refl
  copyRemove (◆∷ Γ A n₁ ◆Γ) (suc n) =
    cong (λ x -> x ∷ (A , n₁ + n * n₁)) (copyRemove ◆Γ (suc n))
--}}}

  union-assoc :
    (T1 T2 T3 : ListLTerm) ->
    ListExchange (union (union T1 T2) T3) (union T1 (union T2 T3))
--{{{
  union-assoc T1 T2 [] =
    idLE
  union-assoc T1 T2 (T3 ∷ A) =
    indLE
      (union-assoc T1 T2 T3)
--}}}

  remove◆Union :
    {T1 T2 : ListLTerm} ->
    (◆T1 : ◆List T1) ->
    (◆T2 : ◆List T2) ->
    remove◆ (unionKeep◆ ◆T1 ◆T2) ≡ union (remove◆ ◆T1) (remove◆ ◆T2)
--{{{
  remove◆Union ◆T1 ◆[] =
    refl
  remove◆Union ◆T1 (◆∷ Γ A n ◆T2) =
    cong
      (λ x -> x ∷ (A , n))
      (remove◆Union ◆T1 ◆T2)
--}}}

  remove◆Copy :
    {T : ListLTerm} ->
    (◆T : ◆List T) ->
    (n : ℕ) ->
    remove◆ (copyKeep◆ ◆T n) ≡ copy (remove◆ ◆T) n
--{{{
  remove◆Copy ◆T zero =
    refl
  remove◆Copy ◆[] (suc n) =
    refl
  remove◆Copy (◆∷ Γ A n₁ ◆T) (suc n) =
    cong
      (λ x -> x ∷ (A , n₁ + n * n₁))
      (remove◆Copy ◆T (suc n))
--}}}

  ¬ListExchange[]T∷A :
    (T : ListLTerm) ->
    (A : LTerm) ->
    ¬ (ListExchange [] (T ∷ A))
  ¬ListExchange[]T∷A T A (transLE {Γ₂ = []} []=T∷A []=T∷A₁) =
    ¬ListExchange[]T∷A T A []=T∷A₁
  ¬ListExchange[]T∷A T A (transLE {Γ₂ = Γ₂ ∷ A₁} []=T∷A []=T∷A₁) =
    ¬ListExchange[]T∷A Γ₂ A₁ []=T∷A

  ¬unionT∷A=[] :
    (T T' : ListLTerm) ->
    (A : LTerm) ->
    ¬ (union (T ∷ A) T') ≡ []
  ¬unionT∷A=[] T [] A ()
  ¬unionT∷A=[] T (T' ∷ A₁) A ()

  unfoldListCorrect :
    (T : ListLTerm) ->
    unfoldedList (unfoldList T)
  unfoldListCorrect [] =
    []UL
  unfoldListCorrect (T ∷ (A , zero)) =
    unfoldListCorrect T
  unfoldListCorrect (T ∷ (A , suc n)) =
    ∷UL (unfoldListCorrect (T ∷ (A , n))) A

  unfoldedListUnique :
    {T : ListLTerm} ->
    (uT : unfoldedList T) ->
    (uT' : unfoldedList T) ->
    uT ≡ uT'
  unfoldedListUnique []UL []UL =
    refl
  unfoldedListUnique (∷UL uT A) (∷UL uT' .A) =
    cong
      (λ x -> ∷UL x A)
      (unfoldedListUnique uT uT')

  ListExchangeKeepUnfolded :
    {T T' : ListLTerm} ->
    (uT : unfoldedList T) ->
    (T=T' : ListExchange T T') ->
    unfoldedList T'
  ListExchangeKeepUnfolded uT idLE =
    uT
  ListExchangeKeepUnfolded (∷UL (∷UL uT A₁) A) (exLE T=T') =
    ∷UL (∷UL (ListExchangeKeepUnfolded uT T=T') A) A₁
  ListExchangeKeepUnfolded uT (transLE T=T' T=T'') =
    ListExchangeKeepUnfolded (ListExchangeKeepUnfolded uT T=T') T=T''
  ListExchangeKeepUnfolded (∷UL uT A) (indLE T=T') =
    ∷UL (ListExchangeKeepUnfolded uT T=T') A
