module ex where

  open import Nat

  data ListExample : Set where
    [] : ListExample
    _∷_ : ℕ -> ListExample -> ListExample

  data ManipExample : ListExample -> Set where
    EV : (l : ListExample) -> ManipExample l
    E : (l : ListExample) -> ManipExample l -> ManipExample (0 ∷ l)
    F : (n1 n2 : ℕ) -> (l : ListExample) -> ManipExample (n1 ∷ (n2 ∷ l)) -> ManipExample ((n1 + n2) ∷ l)

  E-inv :
    (l : ListExample) ->
    ManipExample (0 ∷ l) ->
    ManipExample l
  E-inv l m = {!!}
