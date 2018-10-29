{-                                                  -
 -                                                  -
 -     Module of definition of a list of formulas   -
 -                                                  -
 -                                                  -}

module Syntax.ListLTerm where
  
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary
  open import Data.Product
  
  {- Syntax -}
  open import Syntax.LTerm
  open import Syntax.Term
  
  {- Semantic -}
  
  {- Definition of a list of forumla (Γ or Δ) -}
  data ListLTerm : Set where
    [] :
      ListLTerm
    _∷_ :
      (Γ : ListLTerm) ->
      (A : LTerm) ->
      ListLTerm
  
  infixl 30 _∷_

  union :
    ListLTerm ->
    ListLTerm ->
    ListLTerm
  union Γ [] =
    Γ
  union Γ (Γ' ∷ A) =
    (union Γ Γ') ∷ A
  
  {- Function to count operators -}
  nbOpListLTerm :
    (L : ListLTerm) ->
    
    ℕ
  nbOpListLTerm [] =
    0
  nbOpListLTerm (l ∷ F) =
    (nbOpLTerm F) + (nbOpListLTerm l)
  
  topNbOpList :
    (Γ : ListLTerm) ->
    ℕ
  topNbOpList [] =
    0
  topNbOpList (Γ ∷ A) =
    nbOpLTerm A

  copy :
    (L : ListLTerm) ->
    (n : ℕ) ->
    ListLTerm
  copy L zero =
    []
  copy [] (suc n) =
    []
  copy (L ∷ (A , n1)) (suc n) =
    copy L (suc n) ∷ (A , (suc n) * n1)

  idCopy :
    (Γ : ListLTerm) ->
    copy Γ 1 ≡ Γ
  idCopy [] =
    refl
  idCopy (Γ ∷ (A , n)) =
    begin
      copy Γ 1 ∷ (A , n + zero)
        ≡⟨ cong (λ x -> x ∷ (A , n + zero))
             (idCopy Γ) ⟩
      Γ ∷ (A , n + zero)
        ≡⟨ cong (λ x -> Γ ∷ (A , x))
             (sym a=a+0) ⟩
      Γ ∷ (A , n) ∎
  
  {- ListExchange definition and properties -}
  data ListExchange : (Γ Γ' : ListLTerm) -> Set where
    idLE :
      {Γ : ListLTerm} ->
      ListExchange Γ Γ
    exLE :
      {Γ Γ' : ListLTerm}{A B : LTerm} ->
      (Γ=Γ' : ListExchange Γ Γ') ->
      ListExchange (Γ ∷ A ∷ B) (Γ' ∷ B ∷ A)
    transLE :
      {Γ₁ Γ₂ Γ₃ : ListLTerm} ->
      (Γ₁=Γ₂ : ListExchange Γ₁ Γ₂) ->
      (Γ₂=Γ₃ : ListExchange Γ₂ Γ₃) ->
      ListExchange Γ₁ Γ₃
    indLE :
      {Γ Γ' : ListLTerm} ->
      {F : LTerm} ->
      (Γ=Γ' : ListExchange Γ Γ') ->
      ListExchange (Γ ∷ F) (Γ' ∷ F)

  data ◆List : ListLTerm -> Set where
    ◆[] :
      ◆List []
    ◆∷ :
      (Γ : ListLTerm) ->
      (A : Term) ->
      (n : ℕ) ->
      (◆Γ : ◆List Γ) ->
      ◆List (Γ ∷ (◆ A , n))

  remove◆ :
    {Γ : ListLTerm} ->
    ◆List Γ ->
    ListLTerm
  remove◆ ◆[] =
    []
  remove◆ (◆∷ Γ A n ◆Γ) =
    (remove◆ ◆Γ) ∷ (A , n)

  --
  --
  -- Unfold
  --
  --
  unfoldList :
    (T : ListLTerm) ->
    ListLTerm
  unfoldList [] =
    []
  unfoldList (T ∷ (A , zero)) =
    unfoldList T
  unfoldList (T ∷ (A , suc n)) =
    unfoldList (T ∷ (A , n)) ∷ (A , 1)

  data unfoldedList : ListLTerm -> Set where
    []UL :
      unfoldedList []
    ∷UL :
      {T : ListLTerm} ->
      unfoldedList T ->
      (A : Term) ->
      unfoldedList (T ∷ (A , 1))

  unionKeepUnfolded :
    {T D : ListLTerm} ->
    (uT : unfoldedList T) ->
    (uD : unfoldedList D) ->
    unfoldedList (union T D)
  unionKeepUnfolded uT []UL =
    uT
  unionKeepUnfolded uT (∷UL uD A) =
    ∷UL (unionKeepUnfolded uT uD) A

  remove◆KeepUnfolded :
    {T : ListLTerm} ->
    (uT : unfoldedList T) ->
    (◆T : ◆List T) ->
    unfoldedList (remove◆ ◆T)
  remove◆KeepUnfolded uT ◆[] =
    []UL
  remove◆KeepUnfolded (∷UL uT .(◆ A)) (◆∷ Γ A .1 ◆T) =
    ∷UL (remove◆KeepUnfolded uT ◆T) A
  
