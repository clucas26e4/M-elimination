{-                                                  -
 -                                                  -
 -     Module of definition of a λ-formula            -
 -                                                  -
 -                                                  -}

module Syntax.LTerm where

  {- STDLIB -}
  open import Data.Nat
  open import Data.Product

  {- Syntax -}
  open import Syntax.Term

  {- Semantic -}

  LTerm = Term × ℕ

  nbOpLTerm :
    LTerm ->
    ℕ
  nbOpLTerm (A , 0) =
    0
  nbOpLTerm (A , suc n) =
    nbOpFor A + nbOpLTerm (A , n)
