{-                                                  -
 -                                                  -
 -     Module of definition of an ƛ-hypersequent      -
 -                                                  -
 -                                                  -}

module Syntax.LHSeq where

  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary

  {- Syntax -}
  open import Syntax.LTerm
  open import Syntax.ListLTerm
  open import Syntax.LSeq


  {- Semantic -}

  {- Definition of an hypersequent -}
  data LHSeq : Set where
    head :
      (H : LSeq) ->
      LHSeq
    _∣_ :
      (G : LHSeq) ->
      (H : LSeq) ->
      LHSeq

  infixl 50 _∣_

  maxOp :
    (G : LHSeq) ->
    ℕ
  maxOp (head H) =
    nbOpLSeq H
  maxOp (G ∣ H) =
    maxOp G ⊔ nbOpLSeq H

  size :
    (G : LHSeq) ->
    ℕ
  size (head H) =
    1
  size (G ∣ H) =
    suc (size G)

  --
  --
  -- Exchange
  --
  --
  data LHSeqExchange : (G G' : LHSeq) -> Set where
    idHE :
      {G : LHSeq} ->
      LHSeqExchange G G
    exHE :
      {G G' : LHSeq}{H H' : LSeq} ->
      (G=G' : LHSeqExchange G G') ->
      LHSeqExchange (G ∣ H ∣ H') (G' ∣ H' ∣ H)
    exHE-head :
      {H H' : LSeq} ->
      LHSeqExchange (head H ∣ H') (head H' ∣ H)
    transHE :
      {G₁ G₂ G₃ : LHSeq} ->
      (G₁=G₂ : LHSeqExchange G₁ G₂) ->
      (G₂=G₃ : LHSeqExchange G₂ G₃) ->
      LHSeqExchange G₁ G₃
    indHE :
      (G G' : LHSeq) ->
      {H : LSeq} ->
      (G=G' : LHSeqExchange G G') ->
      LHSeqExchange (G ∣ H) (G' ∣ H)

  push-front :
    (G : LHSeq) ->
    (H : LSeq) ->
    LHSeq
  push-front (head H') H =
    head H ∣ H'
  push-front (G ∣ H') H =
    (push-front G H) ∣ H'

  unionLHSeq :
    (G G' : LHSeq) ->
    LHSeq
  unionLHSeq G (head H) =
    G ∣ H
  unionLHSeq G (G' ∣ H) =
    (unionLHSeq G G') ∣ H

  --
  --
  -- Unfold
  --
  --
  unfold :
    (G : LHSeq) ->
    LHSeq
  unfold (head (T , D)) =
    head (unfoldList T , unfoldList D)
  unfold (G ∣ (T , D)) =
    (unfold G) ∣ (unfoldList T , unfoldList D)

  data unfolded : LHSeq -> Set where
    headU :
      {T D : ListLTerm} ->
      unfoldedList T ->
      unfoldedList D ->
      unfolded (head (T , D))
    consU :
      {G : LHSeq} ->
      {T D : ListLTerm} ->
      unfolded G ->
      unfoldedList T ->
      unfoldedList D ->
      unfolded (G ∣ (T , D))
