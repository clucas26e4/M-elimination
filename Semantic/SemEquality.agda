module Semantic.SemEquality where

  {- STDLIB -}
  open import Nat

  {- Syntax -}
  open import Syntax.Term

  {- Semantic -}

  -- Definition of context
  data Context : Set where
    ● :
      Context
    CC :
      Term ->
      Context
    varC :
      ℕ ->
      Context
    botC :
      Context
    _⊔C_ :
      (A : Context) ->
      (B : Context) ->
      Context
    _+C_ :
      (A : Context) ->
      (B : Context) ->
      Context
    _⊓C_ :
      (A : Context) ->
      (B : Context) ->
      Context
    -C_ :
      (A : Context) ->
      Context
    ◆C :
      (A : Context) ->
      Context
    oneC :
      Context

  _#[_]# :
    (C : Context) ->
    (A : Term) ->
    Term
  ● #[ A ]# =
    A
  (CC B) #[ A ]# =
    B
  varC x #[ A ]# =
    varAG x
  botC #[ A ]# =
    botAG
  (C ⊔C C₁) #[ A ]# =
    (C #[ A ]#) ⊔S (C₁ #[ A ]#)
  (C +C C₁) #[ A ]# =
    (C #[ A ]#) +S (C₁ #[ A ]#)
  (C ⊓C C₁) #[ A ]# =
    (C #[ A ]#) ⊓S (C₁ #[ A ]#)
  (-C C) #[ A ]# =
    -S (C #[ A ]#)
  (◆C C) #[ A ]# =
    ◆ (C #[ A ]#)
  oneC #[ A ]# =
    one

  _*C_ :
    (k : ℕ) ->
    (Ctxt : Context) ->
    Context
  zero *C Ctxt = botC
  suc zero *C Ctxt = Ctxt
  suc (suc k) *C Ctxt = Ctxt +C ((suc k) *C Ctxt)

  -- Definition of substitution
  _s[_/_] :
    Term ->
    Term ->
    ℕ ->
    Term
  varAG zero s[ B / zero ] =
    B
  varAG zero s[ B / suc k ] =
    varAG zero
  varAG (suc x) s[ B / zero ] =
    varAG (suc x)
  varAG (suc x) s[ B / suc k ] =
    (varAG x) s[ B / k ]
  botAG s[ B / k ] =
    botAG
  (A ⊔S A₁) s[ B / k ] =
    (A s[ B / k ]) ⊔S (A₁ s[ B / k ])
  (A +S A₁) s[ B / k ] =
    (A s[ B / k ]) +S (A₁ s[ B / k ])
  (A ⊓S A₁) s[ B / k ] =
    (A s[ B / k ]) ⊓S (A₁ s[ B / k ])
  (-S A) s[ B / k ] =
    -S (A s[ B / k ])
  (◆ A) s[ B / k ] =
    ◆ (A s[ B / k ])
  one s[ B / k ] =
    one

  -- Definition of semantic equality
  data _≡ₛ_ : Term -> Term -> Set where
    -- equational rules
    reflₛ :
      {A : Term} ->
      A ≡ₛ A
    transₛ :
      {A B C : Term} ->
      (A=B : A ≡ₛ B) ->
      (B=C : B ≡ₛ C) ->
      A ≡ₛ C
    symₛ :
      {A B : Term} ->
      (A=B : A ≡ₛ B) ->
      B ≡ₛ A
    ctxtₛ :
      {A B : Term} ->
      (Ctxt : Context) ->
      (A=B : A ≡ₛ B) ->
      (Ctxt #[ A ]#) ≡ₛ (Ctxt #[ B ]#)
    substₛ :
      {A B B' : Term} ->
      {k : ℕ} ->
      (B=C : B ≡ₛ B') ->
      (B s[ A / k ]) ≡ₛ (B' s[ A / k ])
    -- Axioms
    -- group axioms
    asso-+S :
      {A B C : Term} ->
      (A +S (B +S C)) ≡ₛ ((A +S B) +S C)
    commu-+S :
      {A B : Term} ->
      (A +S B) ≡ₛ (B +S A)
    neutral-+S :
      {A : Term} ->
      (A +S botAG) ≡ₛ A
    opp-+S :
      {A : Term} ->
      (A +S (-S A)) ≡ₛ botAG
    -- lattice axioms
    asso-⊔S :
      {A B C : Term} ->
      (A ⊔S (B ⊔S C)) ≡ₛ ((A ⊔S B) ⊔S C)
    commu-⊔S :
      {A B : Term} ->
      (A ⊔S B) ≡ₛ (B ⊔S A)
    abso-⊔S :
      {A B : Term} ->
      (A ⊔S (A ⊓S B)) ≡ₛ A
    asso-⊓S :
      {A B C : Term} ->
      (A ⊓S (B ⊓S C)) ≡ₛ ((A ⊓S B) ⊓S C)
    commu-⊓S :
      {A B : Term} ->
      (A ⊓S B) ≡ₛ (B ⊓S A)
    abso-⊓S :
      {A B : Term} ->
      (A ⊓S (A ⊔S B)) ≡ₛ A
    -- compatibility axioms
    compa-+S :
      {A B C : Term} ->
      (((A ⊓S B) +S C) ⊓S (B +S C)) ≡ₛ ((A ⊓S B) +S C)
    -- 1 Axioms
    0≤1 :
      botAG ⊓S one ≡ₛ botAG
    -- diamond axioms
    ◆Zero :
      ◆ botAG ≡ₛ botAG
    ◆1≤1 :
      (◆ one) ⊓S one ≡ₛ ◆ one
    ◆Linear :
      (A B : Term) ->
      ◆ (A +S B) ≡ₛ (◆ A) +S (◆ B)
    ◆Monotony :
      (A B : Term) -> 
      (◆ (A ⊓S B)) ⊓S (◆ A) ≡ₛ ◆ (A ⊓S B)

  infix 10 _≡ₛ_

  _≤S_ :
    Term ->
    Term ->
    Set
  A ≤S B =
    (A ⊓S B) ≡ₛ A

  _*S_ :
    ℕ ->
    Term ->
    Term 
  zero *S A =
    botAG
  suc zero *S A =
    A
  suc (suc k) *S A =
    A +S ((suc k) *S A)

  _-S_ :
    Term ->
    Term ->
    Term
  A -S B =
    A +S (-S B)

  _-C_ :
    Context ->
    Context ->
    Context
  C -C C' =
    C +C (-C C')

  infix 10 _≤S_
  infix 30 _-S_
  infix 30 _-C_

  -- Definition of positive part, negative part and absolute value
  _⁺ :
    Term ->
    Term
  A ⁺ =
    A ⊔S botAG
  _⁻ :
    Term ->
    Term
  A ⁻ =
    (-S A) ⊔S botAG

  abs :
    Term ->
    Term
  abs A =
    A ⊔S (-S A)


  -- helpful tools to handle transitivity
  
  infix  3 _∎ₛ
  infixr 2 _≡ₛ⟨⟩_ _≡ₛ⟨_⟩_
  infix  1 beginₛ_

  beginₛ_ : ∀{x y : Term} → x ≡ₛ y → x ≡ₛ y
  beginₛ_ x≡y = x≡y

  _≡ₛ⟨⟩_ : ∀ (x {y} : Term) → x ≡ₛ y → x ≡ₛ y
  _ ≡ₛ⟨⟩ x≡y = x≡y
  
  _≡ₛ⟨_⟩_ : ∀ (x {y z} : Term) → x ≡ₛ y → y ≡ₛ z → x ≡ₛ z
  _ ≡ₛ⟨ x≡y ⟩ y≡z = transₛ x≡y y≡z

  _∎ₛ : ∀ (x : Term) → x ≡ₛ x
  _∎ₛ _ = reflₛ
  
