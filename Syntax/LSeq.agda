{-                                                  -
 -                                                  -
 -     Module of definition of an ƛ-sequent           -
 -                                                  -
 -                                                  -}

module Syntax.LSeq where

  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Product

  {- Syntax -}
  open import Syntax.LTerm
  open import Syntax.ListLTerm

  {- Semantic -}

  data LSeq : Set where
    _,_ :
      (T : ListLTerm) ->
      (D : ListLTerm) ->
      LSeq

  nbOpLSeq :
    (H : LSeq) ->
    ℕ
  nbOpLSeq (l1 , l2) =
    nbOpListLTerm l1 + nbOpListLTerm l2

  nbOpLSeqTop :
    (H : LSeq) ->
    ℕ
  nbOpLSeqTop (l1 , l2) =
    topNbOpList l1 + topNbOpList l2

  unionLSeq :
    LSeq ->
    LSeq ->
    LSeq
  unionLSeq (T , D) (T' , D') =
    (union T T' , union D D')

  copyLSeq :
    (H : LSeq) ->
    ℕ ->
    LSeq
  copyLSeq (T , D) n =
    (copy T n , copy D n)

  idCopyLSeq :
    (H : LSeq) ->
    copyLSeq H 1 ≡ H
  idCopyLSeq (T , D) =
    begin
      (copy T 1 , copy D 1)
        ≡⟨ cong (λ x -> x , copy D 1)
             (idCopy T) ⟩
      (T , copy D 1)
        ≡⟨ cong (λ x -> T , x)
             (idCopy D) ⟩
      (T , D) ∎
