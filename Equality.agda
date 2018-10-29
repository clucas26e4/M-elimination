module Equality where

  open import Relation.Binary.PropositionalEquality public
  open Relation.Binary.PropositionalEquality.≡-Reasoning public

  cong₃ :
    {A B C D : Set} ->
    (f : A -> B -> C -> D) ->
    {x1 x2 : A} ->
    {y1 y2 : B} ->
    {z1 z2 : C} ->
    x1 ≡ x2 ->
    y1 ≡ y2 ->
    z1 ≡ z2 ->
    f x1 y1 z1 ≡ f x2 y2 z2
  cong₃ f refl refl refl = refl
