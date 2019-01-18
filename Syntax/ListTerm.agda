{-                                                  -
 -                                                  -
 -     Module of definition of a list of formulas   -
 -                                                  -
 -                                                  -}

module Syntax.ListTerm where
  
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary
  
  {- Syntax -}
  open import Syntax.Term
  
  {- Semantic -}
  open import Semantic.SemEquality
  
  {- Definition of a list of forumla (Γ or Δ) -}
  data ListTerm : Set where
    [] :
      ListTerm
    _∷_ :
      (Γ : ListTerm) ->
      (A : Term) ->
      ListTerm

  constantList :
    (A : Term) ->
    (k : ℕ) ->
    ListTerm
  constantList A zero =
    []
  constantList A (suc k) =
    constantList A k ∷ A
  
  infixl 30 _∷_

  union :
    ListTerm ->
    ListTerm ->
    ListTerm
  union Γ [] =
    Γ
  union Γ (Γ' ∷ A) =
    (union Γ Γ') ∷ A
  
  {- Function to count operators -}
  nbOpListFor :
    (L : ListTerm) ->
    ℕ
  nbOpListFor [] =
    0
  nbOpListFor (l ∷ F) =
    (nbOpFor F) + (nbOpListFor l)
  
  topNbOpList :
    (Γ : ListTerm) ->
    ℕ
  topNbOpList [] =
    0
  topNbOpList (Γ ∷ A) =
    nbOpFor A
  
  {- ListExchange definition and properties -}
  data ListExchange : (Γ Γ' : ListTerm) -> Set where
    idLE :
      {Γ : ListTerm} ->
      ListExchange Γ Γ
    exLE :
      {Γ Γ' : ListTerm}{A B : Term} ->
      (Γ=Γ' : ListExchange Γ Γ') ->
      ListExchange (Γ ∷ A ∷ B) (Γ' ∷ B ∷ A)
    transLE :
      {Γ₁ Γ₂ Γ₃ : ListTerm} ->
      (Γ₁=Γ₂ : ListExchange Γ₁ Γ₂) ->
      (Γ₂=Γ₃ : ListExchange Γ₂ Γ₃) ->
      ListExchange Γ₁ Γ₃
    indLE :
      {Γ Γ' : ListTerm} ->
      {F : Term} ->
      (Γ=Γ' : ListExchange Γ Γ') ->
      ListExchange (Γ ∷ F) (Γ' ∷ F)
      
  data ◆List : ListTerm -> Set where
    ◆[] :
      ◆List []
    ◆∷ :
      (Γ : ListTerm) ->
      (A : Term) ->
      ◆List Γ ->
      ◆List (Γ ∷ ◆ A)

  remove◆ :
    {Γ : ListTerm} ->
    ◆List Γ ->
    ListTerm
  remove◆ ◆[] =
    []
  remove◆ (◆∷ Γ A ◆Γ) =
    remove◆ ◆Γ ∷ A

  substList :
    (T : ListTerm) ->
    (k : ℕ) ->
    (A : Term) ->
    ListTerm
  substList [] k A = 
    []
  substList (T ∷ A₁) k A = 
    (substList T k A) ∷ (A₁ s[ A / k ])
