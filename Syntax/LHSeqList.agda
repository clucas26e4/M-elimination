{-                                                  -
 -                                                  -
 -   Module of definition of a list of hypersequent -
 -                                                  -
 -                                                  -}

module Syntax.LHSeqList where

  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Product

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.LTerm
  open import Syntax.ListLTerm
  open import Syntax.LSeq
  open import Syntax.LHSeq
  open import Syntax.MGA-SR-Can
  open import Syntax.MGA-SR

  {- Semantic -}
  -- open import Semantic.SemEquality
  -- open import Semantic.Interpretation

  data LHSeqList : Set where
    []H :
      LHSeqList
    _∷H_ :
      LHSeq ->
      LHSeqList ->
      LHSeqList

  unionHL : (l1 l2 : LHSeqList) -> LHSeqList
  unionHL []H l2 = l2
  unionHL (x ∷H l1) l2 = x ∷H (unionHL l1 l2)

  --
  --
  -- Proof of a list of hypersequent
  --
  --

  data Prooflist* : LHSeqList -> Set where
    []P :
      Prooflist* []H
    consP :
      {l : LHSeqList} ->
      {G : LHSeq} ->
      (pl : Prooflist* l) ->
      (pG : MGA-SR†* G) ->
      Prooflist* (G ∷H l)

  Prooflist*-L :
    (l1 l2 : LHSeqList) ->
    (pl : Prooflist* (unionHL l1 l2)) ->
    Prooflist* l1
  Prooflist*-L []H l2 pl =
    []P
  Prooflist*-L (x ∷H l1) l2 (consP pl pG) =
    consP (Prooflist*-L l1 l2 pl) pG

  Prooflist*-R :
    (l1 l2 : LHSeqList) ->
    (pl : Prooflist* (unionHL l1 l2)) ->
    Prooflist* l2
  Prooflist*-R []H l2 pl =
    pl
  Prooflist*-R (x ∷H l1) l2 (consP pl pG) =
    Prooflist*-R l1 l2 pl

  data propLeavesStep1* : LHSeq -> ListLTerm -> ListLTerm -> ℕ -> LHSeqList -> Set where
    []P1 :
      (H : LHSeq) ->
      (T D : ListLTerm) ->
      (n : ℕ) ->
      propLeavesStep1* H T D n []H
    consP1 :
      {l : LHSeqList} ->
      (H : LHSeq) ->
      (T D T' D' : ListLTerm) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (k : ℕ) ->
      (p : MGA-SR†*(head (remove◆ ◆T , remove◆ ◆D ∷ (one , suc k)))) ->
      (n n' : ℕ) ->
      #◆* p < n' -> 
      (p1L : propLeavesStep1* H T' D' n' l) ->
      propLeavesStep1* H T' D' n' ((H ∣ (union T (copy T' n) , union (D ∷ (one , suc k)) (copy D' n))) ∷H l)
    consP1' :
      {l : LHSeqList} ->
      (H : LHSeq) ->
      (T D T' D' : ListLTerm) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (p : MGA-SR†*(head (remove◆ ◆T , remove◆ ◆D))) ->
      (n n' : ℕ) ->
      #◆* p < n' -> 
      (p1L : propLeavesStep1* H T' D' n' l) ->
      propLeavesStep1* H T' D' n' ((H ∣ (union T (copy T' n) , union D (copy D' n))) ∷H l)

  data propLeavesStep1*-head : ListLTerm -> ListLTerm -> ℕ -> LHSeqList -> Set where
    []P1head :
      (T D : ListLTerm) ->
      (n : ℕ) ->
      propLeavesStep1*-head T D n []H
    consP1head :
      {l : LHSeqList} ->
      (T D T' D' : ListLTerm) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (k : ℕ) ->
      (p : MGA-SR†* (head (remove◆ ◆T , remove◆ ◆D ∷ (one , suc k)))) ->
      (n n' : ℕ) ->
      #◆* p < n' -> 
      (p1L : propLeavesStep1*-head T' D' n' l) ->
      propLeavesStep1*-head T' D' n' ((head (union T (copy T' n) , union (D ∷ (one , suc k)) (copy D' n))) ∷H l)
    consP1head' :
      {l : LHSeqList} ->
      (T D T' D' : ListLTerm) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (p : MGA-SR†* (head (remove◆ ◆T , remove◆ ◆D))) ->
      (n n' : ℕ) ->
      #◆* p < n' -> 
      (p1L : propLeavesStep1*-head T' D' n' l) ->
      propLeavesStep1*-head T' D' n' ((head (union T (copy T' n) , union D (copy D' n))) ∷H l)

  data propLeavesStep1*-head-bis : ListLTerm -> ListLTerm -> LHSeqList -> Set where
    []P1head-bis :
      (T D : ListLTerm) ->
      propLeavesStep1*-head-bis T D  []H
    consP1head-bis :
      {l : LHSeqList} ->
      (T D T' D' : ListLTerm) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (k : ℕ) ->
      (p : MGA-SR†* (head (remove◆ ◆T , remove◆ ◆D ∷ (one , suc k)))) ->
      (n : ℕ) ->
      (p1L : propLeavesStep1*-head-bis T' D' l) ->
      propLeavesStep1*-head-bis T' D' ((head (union T (copy T' n) , union (D ∷ (one , suc k)) (copy D' n))) ∷H l)
    consP1head-bis' :
      {l : LHSeqList} ->
      (T D T' D' : ListLTerm) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (p : MGA-SR†* (head (remove◆ ◆T , remove◆ ◆D))) ->
      (n : ℕ) ->
      (p1L : propLeavesStep1*-head-bis T' D' l) ->
      propLeavesStep1*-head-bis T' D' ((head (union T (copy T' n) , union D (copy D' n))) ∷H l)

  unionPropLeavesStep1* :
    {H : LHSeq} ->
    {T D : ListLTerm} ->
    {n : ℕ} ->
    {l1 l2 : LHSeqList} ->
    propLeavesStep1* H T D n l1 ->
    propLeavesStep1* H T D n l2 ->
    propLeavesStep1* H T D n (unionHL l1 l2)
  unionPropLeavesStep1* ([]P1 H T D n) pL2 =
    pL2
  unionPropLeavesStep1* (consP1 H T D T' D' ◆T ◆D k p n n' x pL1) pL2 =
    consP1 H T D T' D' ◆T ◆D k p n n' x (unionPropLeavesStep1* pL1 pL2)
  unionPropLeavesStep1* (consP1' H T D T' D' ◆T ◆D p n n' x pL1) pL2 =
    consP1' H T D T' D' ◆T ◆D p n n' x (unionPropLeavesStep1* pL1 pL2)

  congPropLeavesStep1* :
    {H : LHSeq} ->
    {T D : ListLTerm} ->
    {n : ℕ} ->
    {l1 l2 : LHSeqList} ->
    propLeavesStep1* H T D n l1 ->
    l1 ≡ l2 ->
    propLeavesStep1* H T D n l2
  congPropLeavesStep1* pL1 refl = pL1

  unionPropLeavesStep1*-head :
    {T D : ListLTerm} ->
    {n : ℕ} ->
    {l1 l2 : LHSeqList} ->
    propLeavesStep1*-head T D n l1 ->
    propLeavesStep1*-head T D n l2 ->
    propLeavesStep1*-head T D n (unionHL l1 l2)
  unionPropLeavesStep1*-head ([]P1head T D n) pL2 =
    pL2
  unionPropLeavesStep1*-head (consP1head T D T' D' ◆T ◆D k p n n' x pL1) pL2 =
    consP1head T D T' D' ◆T ◆D k p n n' x (unionPropLeavesStep1*-head pL1 pL2)
  unionPropLeavesStep1*-head (consP1head' T D T' D' ◆T ◆D p n n' x pL1) pL2 =
    consP1head' T D T' D' ◆T ◆D p n n' x (unionPropLeavesStep1*-head pL1 pL2)

  congPropLeavesStep1*-head :
    {T D : ListLTerm} ->
    {n : ℕ} ->
    {l1 l2 : LHSeqList} ->
    propLeavesStep1*-head T D n l1 ->
    l1 ≡ l2 ->
    propLeavesStep1*-head T D n l2
  congPropLeavesStep1*-head pL1 refl = pL1

  unionPropLeavesStep1*-head-bis :
    {T D : ListLTerm} ->
    {l1 l2 : LHSeqList} ->
    propLeavesStep1*-head-bis T D l1 ->
    propLeavesStep1*-head-bis T D l2 ->
    propLeavesStep1*-head-bis T D (unionHL l1 l2)
  unionPropLeavesStep1*-head-bis ([]P1head-bis T D) pL2 =
    pL2
  unionPropLeavesStep1*-head-bis (consP1head-bis T D T' D' ◆T ◆D k p x pL1) pL2 =
    consP1head-bis T D T' D' ◆T ◆D k p x (unionPropLeavesStep1*-head-bis pL1 pL2)
  unionPropLeavesStep1*-head-bis (consP1head-bis' T D T' D' ◆T ◆D p x pL1) pL2 =
    consP1head-bis' T D T' D' ◆T ◆D p x (unionPropLeavesStep1*-head-bis pL1 pL2)

  congPropLeavesStep1*-head-bis :
    {T D : ListLTerm} ->
    {l1 l2 : LHSeqList} ->
    propLeavesStep1*-head-bis T D l1 ->
    l1 ≡ l2 ->
    propLeavesStep1*-head-bis T D l2
  congPropLeavesStep1*-head-bis pL1 refl = pL1

  --
  --
  -- With can rule
  --
  --

  data Prooflist : LHSeqList -> Set where
    []P :
      Prooflist []H
    consP :
      {l : LHSeqList} ->
      {G : LHSeq} ->
      (pl : Prooflist l) ->
      (pG : MGA-SR† G) ->
      Prooflist (G ∷H l)

  Prooflist-L :
    (l1 l2 : LHSeqList) ->
    (pl : Prooflist (unionHL l1 l2)) ->
    Prooflist l1
  Prooflist-L []H l2 pl =
    []P
  Prooflist-L (x ∷H l1) l2 (consP pl pG) =
    consP (Prooflist-L l1 l2 pl) pG

  Prooflist-R :
    (l1 l2 : LHSeqList) ->
    (pl : Prooflist (unionHL l1 l2)) ->
    Prooflist l2
  Prooflist-R []H l2 pl =
    pl
  Prooflist-R (x ∷H l1) l2 (consP pl pG) =
    Prooflist-R l1 l2 pl

  data propLeavesStep1 : LHSeq -> ListLTerm -> ListLTerm -> ℕ -> LHSeqList -> Set where
    []P1 :
      (H : LHSeq) ->
      (T D : ListLTerm) ->
      (n : ℕ) ->
      propLeavesStep1 H T D n []H
    consP1 :
      {l : LHSeqList} ->
      (H : LHSeq) ->
      (T D T' D' : ListLTerm) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (k : ℕ) ->
      (p : MGA-SR† (head (remove◆ ◆T , remove◆ ◆D ∷ (one , suc k)))) ->
      (n n' : ℕ) ->
      #◆ p < n' -> 
      (p1L : propLeavesStep1 H T' D' n' l) ->
      propLeavesStep1 H T' D' n' ((H ∣ (union T (copy T' n) , union (D ∷ (one , suc k)) (copy D' n))) ∷H l)
    consP1' :
      {l : LHSeqList} ->
      (H : LHSeq) ->
      (T D T' D' : ListLTerm) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (p : MGA-SR† (head (remove◆ ◆T , remove◆ ◆D))) ->
      (n n' : ℕ) ->
      #◆ p < n' -> 
      (p1L : propLeavesStep1 H T' D' n' l) ->
      propLeavesStep1 H T' D' n' ((H ∣ (union T (copy T' n) , union D (copy D' n))) ∷H l)

  data propLeavesStep1-head : ListLTerm -> ListLTerm -> ℕ -> LHSeqList -> Set where
    []P1head :
      (T D : ListLTerm) ->
      (n : ℕ) ->
      propLeavesStep1-head T D n []H
    consP1head :
      {l : LHSeqList} ->
      (T D T' D' : ListLTerm) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (k : ℕ) ->
      (p : MGA-SR† (head (remove◆ ◆T , remove◆ ◆D ∷ (one , suc k)))) ->
      (n n' : ℕ) ->
      #◆ p < n' -> 
      (p1L : propLeavesStep1-head T' D' n' l) ->
      propLeavesStep1-head T' D' n' ((head (union T (copy T' n) , union (D ∷ (one , suc k)) (copy D' n))) ∷H l)
    consP1head' :
      {l : LHSeqList} ->
      (T D T' D' : ListLTerm) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (p : MGA-SR† (head (remove◆ ◆T , remove◆ ◆D))) ->
      (n n' : ℕ) ->
      #◆ p < n' -> 
      (p1L : propLeavesStep1-head T' D' n' l) ->
      propLeavesStep1-head T' D' n' ((head (union T (copy T' n) , union D (copy D' n))) ∷H l)

  data propLeavesStep1-head-bis : ListLTerm -> ListLTerm -> LHSeqList -> Set where
    []P1head-bis :
      (T D : ListLTerm) ->
      propLeavesStep1-head-bis T D  []H
    consP1head-bis :
      {l : LHSeqList} ->
      (T D T' D' : ListLTerm) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (k : ℕ) ->
      (p : MGA-SR† (head (remove◆ ◆T , remove◆ ◆D ∷ (one , suc k)))) ->
      (n : ℕ) ->
      (p1L : propLeavesStep1-head-bis T' D' l) ->
      propLeavesStep1-head-bis T' D' ((head (union T (copy T' n) , union (D ∷ (one , suc k)) (copy D' n))) ∷H l)
    consP1head-bis' :
      {l : LHSeqList} ->
      (T D T' D' : ListLTerm) ->
      (◆T : ◆List T) ->
      (◆D : ◆List D) ->
      (p : MGA-SR† (head (remove◆ ◆T , remove◆ ◆D))) ->
      (n : ℕ) ->
      (p1L : propLeavesStep1-head-bis T' D' l) ->
      propLeavesStep1-head-bis T' D' ((head (union T (copy T' n) , union D (copy D' n))) ∷H l)

  unionPropLeavesStep1 :
    {H : LHSeq} ->
    {T D : ListLTerm} ->
    {n : ℕ} ->
    {l1 l2 : LHSeqList} ->
    propLeavesStep1 H T D n l1 ->
    propLeavesStep1 H T D n l2 ->
    propLeavesStep1 H T D n (unionHL l1 l2)
  unionPropLeavesStep1 ([]P1 H T D n) pL2 =
    pL2
  unionPropLeavesStep1 (consP1 H T D T' D' ◆T ◆D k p n n' x pL1) pL2 =
    consP1 H T D T' D' ◆T ◆D k p n n' x (unionPropLeavesStep1 pL1 pL2)
  unionPropLeavesStep1 (consP1' H T D T' D' ◆T ◆D p n n' x pL1) pL2 =
    consP1' H T D T' D' ◆T ◆D p n n' x (unionPropLeavesStep1 pL1 pL2)

  congPropLeavesStep1 :
    {H : LHSeq} ->
    {T D : ListLTerm} ->
    {n : ℕ} ->
    {l1 l2 : LHSeqList} ->
    propLeavesStep1 H T D n l1 ->
    l1 ≡ l2 ->
    propLeavesStep1 H T D n l2
  congPropLeavesStep1 pL1 refl = pL1

  unionPropLeavesStep1-head :
    {T D : ListLTerm} ->
    {n : ℕ} ->
    {l1 l2 : LHSeqList} ->
    propLeavesStep1-head T D n l1 ->
    propLeavesStep1-head T D n l2 ->
    propLeavesStep1-head T D n (unionHL l1 l2)
  unionPropLeavesStep1-head ([]P1head T D n) pL2 =
    pL2
  unionPropLeavesStep1-head (consP1head T D T' D' ◆T ◆D k p n n' x pL1) pL2 =
    consP1head T D T' D' ◆T ◆D k p n n' x (unionPropLeavesStep1-head pL1 pL2)
  unionPropLeavesStep1-head (consP1head' T D T' D' ◆T ◆D p n n' x pL1) pL2 =
    consP1head' T D T' D' ◆T ◆D p n n' x (unionPropLeavesStep1-head pL1 pL2)

  congPropLeavesStep1-head :
    {T D : ListLTerm} ->
    {n : ℕ} ->
    {l1 l2 : LHSeqList} ->
    propLeavesStep1-head T D n l1 ->
    l1 ≡ l2 ->
    propLeavesStep1-head T D n l2
  congPropLeavesStep1-head pL1 refl = pL1

  unionPropLeavesStep1-head-bis :
    {T D : ListLTerm} ->
    {l1 l2 : LHSeqList} ->
    propLeavesStep1-head-bis T D l1 ->
    propLeavesStep1-head-bis T D l2 ->
    propLeavesStep1-head-bis T D (unionHL l1 l2)
  unionPropLeavesStep1-head-bis ([]P1head-bis T D) pL2 =
    pL2
  unionPropLeavesStep1-head-bis (consP1head-bis T D T' D' ◆T ◆D k p x pL1) pL2 =
    consP1head-bis T D T' D' ◆T ◆D k p x (unionPropLeavesStep1-head-bis pL1 pL2)
  unionPropLeavesStep1-head-bis (consP1head-bis' T D T' D' ◆T ◆D p x pL1) pL2 =
    consP1head-bis' T D T' D' ◆T ◆D p x (unionPropLeavesStep1-head-bis pL1 pL2)

  congPropLeavesStep1-head-bis :
    {T D : ListLTerm} ->
    {l1 l2 : LHSeqList} ->
    propLeavesStep1-head-bis T D l1 ->
    l1 ≡ l2 ->
    propLeavesStep1-head-bis T D l2
  congPropLeavesStep1-head-bis pL1 refl = pL1
