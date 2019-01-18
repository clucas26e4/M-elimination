module Syntax.ListTerm.Properties where
  
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary
  
  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  
  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties
  open import Semantic.Interpretation

  ListExchangeSubst :
    {Γ Γ' : ListTerm} ->
    (Γ=Γ' : Γ ≡ Γ') ->
    ListExchange Γ Γ'
  ListExchangeSubst refl =
    idLE
  ListExchangeCong :
    {Γ1 Γ2 Γ3 : ListTerm} ->
    (Γ1=Γ2 : Γ1 ≡ Γ2) ->
    (LEΓ1Γ3 : ListExchange Γ1 Γ3) ->
    ListExchange Γ2 Γ3
  ListExchangeCong refl LEΓ1Γ3 = LEΓ1Γ3

  ¬ListExchange[]T∷A :
    (T : ListTerm) ->
    (A : Term) ->
    ¬ (ListExchange [] (T ∷ A))
  ¬ListExchange[]T∷A T A (transLE {Γ₂ = []} []=T∷A []=T∷A₁) =
    ¬ListExchange[]T∷A T A []=T∷A₁
  ¬ListExchange[]T∷A T A (transLE {Γ₂ = Γ₂ ∷ A₁} []=T∷A []=T∷A₁) =
    ¬ListExchange[]T∷A Γ₂ A₁ []=T∷A


  sem-union-eq-plus :
    {Γ Γ' : ListTerm} ->
    ⟦ union Γ Γ' ⟧L ≡ₛ ⟦ Γ ⟧L +S ⟦ Γ' ⟧L
  sem-union-eq-plus {Γ} {[]} =
    symₛ neutral-+S
  sem-union-eq-plus {[]} {[] ∷ A} =
    transₛ
      (symₛ neutral-+S)
      commu-+S
  sem-union-eq-plus {Γ ∷ A₁} {[] ∷ A} =
    ctxtₛ
      ((CC (⟦ Γ ⟧L +S A₁)) +C ●)
      (symₛ
        (transₛ
          commu-+S
          neutral-+S))
  sem-union-eq-plus {[]} {Γ' ∷ A₁ ∷ A} =
    beginₛ
      ⟦ union [] Γ' ∷ A₁ ⟧L +S A
        ≡ₛ⟨ ctxtₛ
              (● +C (CC A))
              (sem-union-eq-plus {[]} {Γ' ∷ A₁}) ⟩
      (botAG +S ⟦ Γ' ∷ A₁ ⟧L) +S A
        ≡ₛ⟨ symₛ asso-+S ⟩
      botAG +S (⟦ Γ' ∷ A₁ ⟧L +S A) ∎ₛ
  sem-union-eq-plus {Γ ∷ A₂} {Γ' ∷ A₁ ∷ A} = 
    beginₛ
      ⟦ union (Γ ∷ A₂) Γ' ∷ A₁ ⟧L +S A
        ≡ₛ⟨ ctxtₛ
              (● +C (CC A))
              (sem-union-eq-plus {Γ ∷ A₂} {Γ' ∷ A₁}) ⟩
      (⟦ Γ ∷ A₂ ⟧L +S ⟦ Γ' ∷ A₁ ⟧L) +S A
        ≡ₛ⟨ symₛ asso-+S ⟩
      ⟦ Γ ∷ A₂ ⟧L +S (⟦ Γ' ∷ A₁ ⟧L +S A) ∎ₛ

  ListExchangeSem :
    {Γ Γ' : ListTerm} ->
    (Γ=Γ' : ListExchange Γ Γ') ->
    ⟦ Γ ⟧L ≡ₛ ⟦ Γ' ⟧L
  ListExchangeSem {Γ} {.Γ} idLE =
    reflₛ
  ListExchangeSem {(Γ ∷ A ∷ B)} {(Γ' ∷ .B ∷ .A)} (exLE Γ=Γ') =
    beginₛ
      (⟦ Γ ⟧L +S A) +S B
        ≡ₛ⟨ ctxtₛ
              ((● +C (CC A)) +C (CC B))
              (ListExchangeSem Γ=Γ') ⟩
      (⟦ Γ' ⟧L +S A) +S B
        ≡ₛ⟨ symₛ asso-+S ⟩
      ⟦ Γ' ⟧L +S (A +S B)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ Γ' ⟧L)) +C ●)
              commu-+S ⟩
      ⟦ Γ' ⟧L +S (B +S A)
        ≡ₛ⟨ asso-+S ⟩
      (⟦ Γ' ⟧L +S B) +S A ∎ₛ
  ListExchangeSem {Γ} {Γ'} (transLE Γ=Γ' Γ=Γ'') =
    transₛ (ListExchangeSem Γ=Γ') (ListExchangeSem (Γ=Γ''))
  ListExchangeSem {Γ ∷ F} {Γ' ∷ .F} (indLE Γ=Γ') =
    ctxtₛ
      (● +C (CC F))
      (ListExchangeSem Γ=Γ')

  ListExchangeSym :
    {Γ Γ' : ListTerm} ->
    (Γ=Γ' : ListExchange Γ Γ') ->
    ListExchange Γ' Γ
  ListExchangeSym idLE =
    idLE
  ListExchangeSym (exLE Γ=Γ') =
    exLE (ListExchangeSym Γ=Γ')
  ListExchangeSym (transLE Γ=Γ' Γ=Γ'') =
    transLE (ListExchangeSym Γ=Γ'') (ListExchangeSym Γ=Γ')
  ListExchangeSym (indLE Γ=Γ') =
    indLE (ListExchangeSym Γ=Γ')

  unionAsso :
    (Γ Γ' Γ'' : ListTerm) ->
    union (union Γ Γ') Γ'' ≡ union Γ (union Γ' Γ'')
  unionAsso Γ Γ' [] =
    refl
  unionAsso Γ Γ' (Γ'' ∷ A) =
    cong
      (λ x -> x ∷ A)
      (unionAsso Γ Γ' Γ'')

  union[]T=T :
    (T : ListTerm) ->
    union [] T ≡ T
  union[]T=T [] =
    refl
  union[]T=T (T ∷ A) =
    cong
      (λ x -> x ∷ A)
      (union[]T=T T)

  unionKeepListExchange :
    {A B C D : ListTerm} ->
    (A=B : ListExchange A B) ->
    (C=D : ListExchange C D) ->
    ListExchange (union A C) (union B D)
  unionKeepListExchange {A} {B} {[]} {.[]} A=B idLE =
    A=B
  unionKeepListExchange {A} {B} {C ∷ A₁} {.(C ∷ A₁)} A=B idLE =
    indLE (unionKeepListExchange A=B (idLE {C}))
  unionKeepListExchange {A} {B} {(C ∷ H ∷ H')} {(D ∷ .H' ∷ .H)} A=B (exLE C=D) =
    exLE (unionKeepListExchange A=B C=D)
  unionKeepListExchange {A} {B} {[]} {D} A=B (transLE C=D C=D₁) =
    transLE
      (unionKeepListExchange A=B C=D)
      (unionKeepListExchange (idLE {B}) C=D₁)
  unionKeepListExchange {A} {B} {C ∷ A₁} {D} A=B (transLE {Γ₂ = Γ₂} C=D C=D₁) = 
    transLE
      (unionKeepListExchange A=B C=D)
      (unionKeepListExchange (idLE {B}) C=D₁)
  unionKeepListExchange {A} {B} {(C ∷ H)} {(D ∷ .H)} A=B (indLE C=D) =
    indLE (unionKeepListExchange A=B C=D)

  unionSymExchange :
    (Γ Γ' : ListTerm) ->
    ListExchange (union Γ Γ') (union Γ' Γ)
  unionSymExchange [] [] =
    idLE
  unionSymExchange [] (Γ' ∷ A) =
    ListExchangeCong
      {Γ' ∷ A}
      (sym (union[]T=T (Γ' ∷ A)))
      idLE
  unionSymExchange (Γ ∷ A) [] =
    ListExchangeSym
      (ListExchangeCong
        {Γ ∷ A}
        (sym (union[]T=T (Γ ∷ A)))
        idLE)
  unionSymExchange (Γ ∷ A) (Γ' ∷ A₁) =
    transLE
      {Γ₂ = (union Γ' Γ) ∷ A ∷ A₁}
      (indLE
        (unionSymExchange (Γ ∷ A) Γ'))
      (transLE
        {Γ₂ = union Γ' Γ ∷ A₁ ∷ A}
        (exLE idLE)
        (transLE
          {Γ₂ = union Γ Γ' ∷ A₁ ∷ A}
          (indLE
            (indLE
              (unionSymExchange Γ' Γ)))
          (indLE
            (unionSymExchange Γ (Γ' ∷ A₁)))))

  unionOp :
    (T T' : ListTerm) ->
    nbOpListFor (union T T') ≡ nbOpListFor T + nbOpListFor T'
  unionOp T [] =
    +-comm 0 (nbOpListFor T)
  unionOp T (T' ∷ A) = 
    begin
      (nbOpFor A + nbOpListFor (union T T'))
        ≡⟨ cong
             (λ x -> nbOpFor A + x)
             (unionOp T T') ⟩
      nbOpFor A + (nbOpListFor T + nbOpListFor T')
        ≡⟨ sym
             (+-assoc (nbOpFor A) (nbOpListFor T) (nbOpListFor T')) ⟩
      nbOpFor A + nbOpListFor T + nbOpListFor T'
        ≡⟨ cong
             (λ x -> x + nbOpListFor T')
             (+-comm (nbOpFor A) (nbOpListFor T)) ⟩
      nbOpListFor T + nbOpFor A + nbOpListFor T'
        ≡⟨ +-assoc (nbOpListFor T) (nbOpFor A) (nbOpListFor T') ⟩
      nbOpListFor T + (nbOpFor A + nbOpListFor T') ∎

  unionKeep◆ :
    {T D : ListTerm} ->
    ◆List T ->
    ◆List D ->
    ◆List (union T D)
  unionKeep◆ ◆T ◆[] = 
    ◆T
  unionKeep◆ {T} ◆T (◆∷ Γ A ◆D) = 
    ◆∷ (union T Γ) A (unionKeep◆ ◆T ◆D)

  remove◆Union :
    {T D : ListTerm} ->
    (◆T : ◆List T) ->
    (◆D : ◆List D) ->
    remove◆ (unionKeep◆ ◆T ◆D) ≡ union (remove◆ ◆T) (remove◆ ◆D)
  remove◆Union ◆T ◆[] =
    refl
  remove◆Union ◆T (◆∷ Γ A ◆D) =
    cong
      (λ x -> x ∷ A)
      (remove◆Union ◆T ◆D)

  constant◆A :
    (A : Term) ->
    (n : ℕ) ->
    ◆List (constantList (◆ A) n)
  constant◆A A zero =
    ◆[]
  constant◆A A (suc n) = 
    ◆∷ (constantList (◆ A) n) A (constant◆A A n)

  remove◆Constant◆A :
    (A : Term) ->
    (n : ℕ) ->
    remove◆ (constant◆A A n) ≡ constantList A n
  remove◆Constant◆A A zero =
    refl
  remove◆Constant◆A A (suc n) =
    cong
      (λ x -> x ∷ A)
      (remove◆Constant◆A A n)

  exchangeUnionLast :
    (T T' : ListTerm) ->
    (A : Term) ->
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

  ListExchangeUnion :
    (T T' : ListTerm) ->
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
    (T1 : ListTerm) ->
    {T2 T3 : ListTerm} ->
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
    {T1 T2 : ListTerm} ->
    (T1=T2 : ListExchange T1 T2) ->
    (T3 : ListTerm) ->
    ListExchange (union T1 T3) (union T2 T3)
--{{{
  unionKeepExchangeLeft {T1} {T2} T1=T2 T3 =
    transLE
      (ListExchangeUnion T1 T3)
      (transLE
        (unionKeepExchangeRight T3 T1=T2)
        (ListExchangeUnion T3 T2))
--}}}
