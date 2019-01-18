module Syntax.MGA-Cut.Soundness where
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.ListTerm.Properties
  open import Syntax.Seq
  open import Syntax.HSeq
  open import Syntax.MGA-Cut

  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties
  open import Semantic.Interpretation
  
  ax-sound :
    {A : Term} ->
    botAG ≤S ⟦ head ([] ∷ A , [] ∷ A) ⟧
  ax-sound {A} =
    ≤S-cong-r
      {B = botAG}
      (symₛ opp-+S)
      ≤S-refl

  Δ-ax-sound :
    botAG ≤S ⟦ head ([] , []) ⟧
  Δ-ax-sound =
    ≤S-cong-r
      {B = botAG}
      (symₛ opp-+S)
      ≤S-refl

  W-sound :
    {G : HSeq} ->
    {Γ1 Γ2 Δ1 Δ2 : ListTerm} ->
    botAG ≤S ⟦ G ∣ (Γ1 , Δ1) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2) ⟧
  W-sound {G} {Γ1} {Γ2} {Δ1} {Δ2} hyp =
    ≤S-trans
      hyp
      ≤S-⊔S

  W-sound-head :
    {Γ1 Γ2 Δ1 Δ2 : ListTerm} ->
    botAG ≤S ⟦ head (Γ1 , Δ1) ⟧ ->
    botAG ≤S ⟦ head (Γ1 , Δ1) ∣ (Γ2 , Δ2) ⟧
  W-sound-head {Γ1} {Γ2} {Δ1} {Δ2} hyp =
    ≤S-trans
      hyp
      ≤S-⊔S

  C-sound :
    {G : HSeq} ->
    {Γ Δ : ListTerm} ->
    botAG ≤S ⟦ G ∣ (Γ , Δ) ∣ (Γ , Δ) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ) ⟧
  C-sound {G} {Γ} {Δ} hyp =
    ≤S-cong-r
      {B = (⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S ⟦ Γ ⟧L)) ⊔S (⟦ Δ ⟧L -S ⟦ Γ ⟧L)}
      (beginₛ
        (⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S ⟦ Γ ⟧L)) ⊔S (⟦ Δ ⟧L -S ⟦ Γ ⟧L)
          ≡ₛ⟨ symₛ asso-⊔S ⟩
        ⟦ G ⟧ ⊔S ((⟦ Δ ⟧L -S ⟦ Γ ⟧L) ⊔S (⟦ Δ ⟧L -S ⟦ Γ ⟧L))
          ≡ₛ⟨ ctxtₛ
                ((CC (⟦ G ⟧)) ⊔C ●)
                (⊓S-⊔S
                  ≤S-refl) ⟩
        ⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S ⟦ Γ ⟧L) ∎ₛ)
      hyp

  C-sound-head :
    {Γ Δ : ListTerm} ->
    botAG ≤S ⟦ head (Γ , Δ) ∣ (Γ , Δ) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ) ⟧
  C-sound-head {Γ} {Δ} hyp =
    ≤S-cong-r
      {B = ((⟦ Δ ⟧L -S ⟦ Γ ⟧L)) ⊔S (⟦ Δ ⟧L -S ⟦ Γ ⟧L)}
      (⊓S-⊔S
        ≤S-refl)
      hyp

  S-sound :
    {G : HSeq} ->
    {Γ1 Γ2 Δ1 Δ2 : ListTerm} ->
    botAG ≤S ⟦ G ∣ (union Γ1 Γ2 , union Δ1 Δ2) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2) ⟧
  S-sound {G} {Γ1} {Γ2} {Δ1} {Δ2} hyp =
    2A≤2B=>A≤B
      (≤S-cong-l
        {A = botAG}
        (symₛ neutral-+S)
        (≤S-cong-r
          {B = 2 *S (⟦ G ⟧ ⊔S ((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) ⊔S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L)))}
          (ctxtₛ
            (2 *C ●)
            asso-⊔S)
          (≤S-trans
            {B = (2 *S ⟦ G ⟧) ⊔S ((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L))}
            (cond-0≤A⊔B-2
              (beginₛ
                ((2 *S ⟦ G ⟧) ⁻) ⊓S (((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L)) ⁻)
                  ≡ₛ⟨ ctxtₛ
                        (● ⊓C (CC (((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L)) ⁻)))
                        (beginₛ
                          (-S (⟦ G ⟧ +S ⟦ G ⟧)) ⊔S botAG
                            ≡ₛ⟨ ctxtₛ
                                  ((CC (-S (⟦ G ⟧ +S ⟦ G ⟧))) ⊔C ●)
                                  (symₛ neutral-+S) ⟩
                          (-S (⟦ G ⟧ +S ⟦ G ⟧)) ⊔S (2 *S botAG)
                            ≡ₛ⟨ ctxtₛ
                                  (● ⊔C (2 *C botC))
                                  -S-distri ⟩
                          ((-S ⟦ G ⟧) +S (-S ⟦ G ⟧)) ⊔S (2 *S botAG)
                            ≡ₛ⟨ symₛ *S-distri-⊔S ⟩
                          2 *S (⟦ G ⟧ ⁻) ∎ₛ) ⟩
                (2 *S ((⟦ G ⟧) ⁻)) ⊓S (((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L)) ⁻)
                  ≡ₛ⟨ lemmaS
                        (cond-A⁻⊓B⁻=0
                          (≤S-cong-r
                            {B = ⟦ G ⟧ ⊔S (⟦ union Δ1 Δ2 ⟧L -S ⟦ union Γ1 Γ2 ⟧L)}
                            (ctxtₛ
                              ((CC (⟦ G ⟧)) ⊔C ●)
                              (beginₛ
                                ⟦ union Δ1 Δ2 ⟧L +S (-S ⟦ union Γ1 Γ2 ⟧L)
                                  ≡ₛ⟨ ctxtₛ
                                        (● +C (CC (-S ⟦ union Γ1 Γ2 ⟧L)))
                                        (sem-union-eq-plus {Δ1} {Δ2}) ⟩
                                (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L) +S (-S ⟦ union Γ1 Γ2 ⟧L)
                                  ≡ₛ⟨ ctxtₛ
                                        ((CC (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L)) -C ●)
                                        ((sem-union-eq-plus {Γ1} {Γ2})) ⟩
                                (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L) +S (-S (⟦ Γ1 ⟧L +S ⟦ Γ2 ⟧L))
                                  ≡ₛ⟨ ctxtₛ
                                        ((CC (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L)) +C ●)
                                        -S-distri ⟩
                                (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L) +S ((-S ⟦ Γ1 ⟧L) -S ⟦ Γ2 ⟧L)
                                  ≡ₛ⟨ symₛ asso-+S ⟩
                                ⟦ Δ1 ⟧L +S (⟦ Δ2 ⟧L +S ((-S ⟦ Γ1 ⟧L) -S ⟦ Γ2 ⟧L))
                                  ≡ₛ⟨ ctxtₛ
                                        ((CC (⟦ Δ1 ⟧L)) +C ((CC ⟦ Δ2 ⟧L) +C ●))
                                        commu-+S ⟩
                                ⟦ Δ1 ⟧L +S (⟦ Δ2 ⟧L +S ((-S ⟦ Γ2 ⟧L) -S ⟦ Γ1 ⟧L))
                                  ≡ₛ⟨  ctxtₛ
                                        ((CC (⟦ Δ1 ⟧L)) +C ●)
                                        asso-+S ⟩
                                ⟦ Δ1 ⟧L +S ((⟦ Δ2 ⟧L +S (-S ⟦ Γ2 ⟧L)) -S ⟦ Γ1 ⟧L)
                                  ≡ₛ⟨ ctxtₛ
                                        ((CC (⟦ Δ1 ⟧L)) +C ●)
                                        commu-+S ⟩
                                ⟦ Δ1 ⟧L +S ((-S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L +S (-S ⟦ Γ2 ⟧L)))
                                  ≡ₛ⟨ asso-+S ⟩
                                (⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L) ∎ₛ))
                            hyp)) ⟩
                botAG ∎ₛ))
            (⊔S-≤S
              (≤S-trans
                {B = ⟦ G ⟧ +S ⟦ G ⟧ ⊔S ((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) ⊔S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L))}
                (A≤B=>C≤D=>A+C≤B+D
                  ≤S-refl
                  ≤S-⊔S)
                (A≤B=>C≤D=>A+C≤B+D
                  ≤S-⊔S
                  ≤S-refl))
              (≤S-trans
                {B = 2 *S ((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) ⊔S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L))}
                mean-≤S-⊔S
                (≤S-trans
                  {B = (⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) ⊔S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L) +S (⟦ G ⟧ ⊔S ((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) ⊔S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L)))}
                  (A≤B=>C≤D=>A+C≤B+D
                  ≤S-refl
                  (≤S-cong-r
                    commu-⊔S
                    ≤S-⊔S))
                  (A≤B=>C≤D=>A+C≤B+D
                  (≤S-cong-r
                    commu-⊔S
                    ≤S-⊔S)
                  ≤S-refl)))))))
    where
    lemmaS :
      {A B : Term} ->
      (A⁻⊓B⁻=0 : (A ⁻) ⊓S (B ⁻) ≡ₛ botAG) ->
      (2 *S (A ⁻)) ⊓S (B ⁻) ≡ₛ botAG
    lemmaS {A} {B} A⁻⊓B⁻=0 =
      ≤S-antisym
        (≤S-trans
          {B = (2 *S (A ⁻)) ⊓S (2 *S (B ⁻))}
          (≤S-⊓S
            ⊓S-≤S
            (≤S-trans
              {B = B ⁻}
              (≤S-cong-l
                {A = (B ⁻) ⊓S ((A ⁻) +S (A ⁻))}
                commu-⊓S
                ⊓S-≤S)
              (≤S-cong-l
                {A = (B ⁻) +S botAG}
                neutral-+S
                (A≤B=>C≤D=>A+C≤B+D
                  ≤S-refl
                  (≤S-cong-r
                    {B = botAG ⊔S (-S B)}
                    commu-⊔S
                    ≤S-⊔S)))))
          (≤S-cong-l
            {A = 2 *S ((A ⁻) ⊓S (B ⁻))}
            *S-distri-⊓S
            (≤S-cong-r
              {B = 2 *S botAG}
              neutral-+S
              (≤S-cong-l
                {A = 2 *S botAG}
                (ctxtₛ
                  (● +C ●)
                  (symₛ A⁻⊓B⁻=0))
                ≤S-refl)
              )))
        (≤S-⊓S
          (≤S-cong-l
            {A = botAG +S botAG}
            neutral-+S
            (≤S-compa-*S
              2
              (≤S-cong-r
                {B = botAG ⊔S (-S A)}
                commu-⊔S
                ≤S-⊔S)))
          ((≤S-cong-r
            {B = botAG ⊔S (-S B)}
            commu-⊔S
            ≤S-⊔S)))

  S-head-sound :
    {Γ1 Γ2 Δ1 Δ2 : ListTerm} ->
    botAG ≤S ⟦ head (union Γ1 Γ2 , union Δ1 Δ2) ⟧ ->
    botAG ≤S ⟦ head (Γ1 , Δ1) ∣ (Γ2 , Δ2) ⟧
  S-head-sound {Γ1} {Γ2} {Δ1} {Δ2} hyp =
    2A≤2B=>A≤B
      (≤S-cong-l
        {A = botAG}
        (symₛ neutral-+S)
        (≤S-trans
          {B = ((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L))}
          (≤S-cong-r
            {B = ⟦ union Δ1 Δ2 ⟧L -S ⟦ union Γ1 Γ2 ⟧L}
            (beginₛ
              ⟦ union Δ1 Δ2 ⟧L +S (-S ⟦ union Γ1 Γ2 ⟧L)
                ≡ₛ⟨ ctxtₛ
                      (● +C (CC (-S ⟦ union Γ1 Γ2 ⟧L)))
                      (sem-union-eq-plus {Δ1} {Δ2}) ⟩
              (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L) +S (-S ⟦ union Γ1 Γ2 ⟧L)
                ≡ₛ⟨ ctxtₛ
                      ((CC (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L)) -C ●)
                      ((sem-union-eq-plus {Γ1} {Γ2})) ⟩
              (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L) +S (-S (⟦ Γ1 ⟧L +S ⟦ Γ2 ⟧L))
                ≡ₛ⟨ ctxtₛ
                      ((CC (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L)) +C ●)
                      -S-distri ⟩
              (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L) +S ((-S ⟦ Γ1 ⟧L) -S ⟦ Γ2 ⟧L)
                ≡ₛ⟨ symₛ asso-+S ⟩
              ⟦ Δ1 ⟧L +S (⟦ Δ2 ⟧L +S ((-S ⟦ Γ1 ⟧L) -S ⟦ Γ2 ⟧L))
                ≡ₛ⟨ ctxtₛ
                      ((CC (⟦ Δ1 ⟧L)) +C ((CC ⟦ Δ2 ⟧L) +C ●))
                      commu-+S ⟩
              ⟦ Δ1 ⟧L +S (⟦ Δ2 ⟧L +S ((-S ⟦ Γ2 ⟧L) -S ⟦ Γ1 ⟧L))
                ≡ₛ⟨  ctxtₛ
                       ((CC (⟦ Δ1 ⟧L)) +C ●)
                       asso-+S ⟩
              ⟦ Δ1 ⟧L +S ((⟦ Δ2 ⟧L +S (-S ⟦ Γ2 ⟧L)) -S ⟦ Γ1 ⟧L)
                ≡ₛ⟨ ctxtₛ
                      ((CC (⟦ Δ1 ⟧L)) +C ●)
                      commu-+S ⟩
              ⟦ Δ1 ⟧L +S ((-S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L +S (-S ⟦ Γ2 ⟧L)))
                ≡ₛ⟨ asso-+S ⟩
              (⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L) ∎ₛ)
            hyp)
          mean-≤S-⊔S))

  M-sound :
    {G : HSeq} ->
    {Γ1 Γ2 Δ1 Δ2 : ListTerm} ->
    (hyp1 : botAG ≤S ⟦ G ∣ (Γ1 , Δ1) ⟧) ->
    (hyp2 : botAG ≤S ⟦ G ∣ (Γ2 , Δ2) ⟧) ->
    botAG ≤S ⟦ G ∣ (union Γ1 Γ2 , union Δ1 Δ2) ⟧
  M-sound {G} {Γ1} {Γ2} {Δ1} {Δ2} hyp1 hyp2 =
    ≤S-cong-r
      {B = ⟦ G ⟧ ⊔S ((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L))}
      (ctxtₛ
        ((CC (⟦ G ⟧)) ⊔C ●)
        (symₛ
          (beginₛ
              ⟦ union Δ1 Δ2 ⟧L +S (-S ⟦ union Γ1 Γ2 ⟧L)
                ≡ₛ⟨ ctxtₛ
                      (● +C (CC (-S ⟦ union Γ1 Γ2 ⟧L)))
                      (sem-union-eq-plus {Δ1} {Δ2}) ⟩
              (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L) +S (-S ⟦ union Γ1 Γ2 ⟧L)
                ≡ₛ⟨ ctxtₛ
                      ((CC (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L)) -C ●)
                      ((sem-union-eq-plus {Γ1} {Γ2})) ⟩
              (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L) +S (-S (⟦ Γ1 ⟧L +S ⟦ Γ2 ⟧L))
                ≡ₛ⟨ ctxtₛ
                      ((CC (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L)) +C ●)
                      -S-distri ⟩
              (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L) +S ((-S ⟦ Γ1 ⟧L) -S ⟦ Γ2 ⟧L)
                ≡ₛ⟨ symₛ asso-+S ⟩
              ⟦ Δ1 ⟧L +S (⟦ Δ2 ⟧L +S ((-S ⟦ Γ1 ⟧L) -S ⟦ Γ2 ⟧L))
                ≡ₛ⟨ ctxtₛ
                      ((CC (⟦ Δ1 ⟧L)) +C ((CC ⟦ Δ2 ⟧L) +C ●))
                      commu-+S ⟩
              ⟦ Δ1 ⟧L +S (⟦ Δ2 ⟧L +S ((-S ⟦ Γ2 ⟧L) -S ⟦ Γ1 ⟧L))
                ≡ₛ⟨  ctxtₛ
                       ((CC (⟦ Δ1 ⟧L)) +C ●)
                       asso-+S ⟩
              ⟦ Δ1 ⟧L +S ((⟦ Δ2 ⟧L +S (-S ⟦ Γ2 ⟧L)) -S ⟦ Γ1 ⟧L)
                ≡ₛ⟨ ctxtₛ
                      ((CC (⟦ Δ1 ⟧L)) +C ●)
                      commu-+S ⟩
              ⟦ Δ1 ⟧L +S ((-S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L +S (-S ⟦ Γ2 ⟧L)))
                ≡ₛ⟨ asso-+S ⟩
              (⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L) ∎ₛ)))
      (cond-0≤A⊔B-2
        (≤S-antisym
          (≤S-trans
            {B = ((⟦ G ⟧ ⁻) ⊓S ((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L)⁻)) +S ((⟦ G ⟧ ⁻) ⊓S ((⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L) ⁻))}
            (≤S-trans
              {B = (⟦ G ⟧ ⁻) ⊓S (((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) ⁻) +S ((⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L)⁻))}
              (≤S-⊓S
                ⊓S-≤S
                (≤S-cong-l
                  commu-⊓S
                  (≤S-trans
                    ⊓S-≤S
                    A+B⁻≤A⁻+B⁻)))
              (lemmaM (⟦ G ⟧) (⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L)))
            (≤S-cong-r
              {B = 2 *S botAG}
              neutral-+S
              (A≤B=>C≤D=>A+C≤B+D
                (≤S-cong-l
                  {A = botAG}
                  (symₛ
                    (cond-A⁻⊓B⁻=0
                      hyp1))
                  ≤S-refl)
                ((≤S-cong-l
                  {A = botAG}
                  (symₛ
                    (cond-A⁻⊓B⁻=0
                      hyp2))
                  ≤S-refl)))))
          (≤S-⊓S
            bot-≤S-⁻
            bot-≤S-⁻)))
    where
    lemmaM :
      (A B C : Term) ->
      (A ⁻) ⊓S ((B ⁻) +S (C ⁻)) ≤S (A ⁻) ⊓S (B ⁻) +S (A ⁻) ⊓S (C ⁻)
    lemmaM A B D =
      A-C≤B=>A≤B+C
        (≤S-⊓S
          (≤S-trans
            {B = (A ⁻) ⊓S ((B ⁻) +S (D ⁻))}
            (≤S-cong-r
              neutral-+S
              (A≤B=>C≤D=>A+C≤B+D
                ≤S-refl
                (≤S-cong-r
                  (symₛ -S-botAG)
                  (≤S--S
                    (≤S-⊓S
                      bot-≤S-⁻
                      bot-≤S-⁻)))))
            ⊓S-≤S)
          (A≤B-C=>A+C≤B
            (≤S-cong-r
              {B = ((A ⁻) ⊓S (D ⁻)) +S (B ⁻)}
              (transₛ
                commu-+S
                (ctxtₛ
                  ((CC (B ⁻)) +C ●)
                  (symₛ -S--S)))
              (A-C≤B=>A≤B+C
                (≤S-⊓S
                  (A≤B+C=>A-C≤B
                    (≤S-trans
                      ⊓S-≤S
                      (≤S-cong-l
                        neutral-+S
                        (A≤B=>C≤D=>A+C≤B+D
                          ≤S-refl
                          bot-≤S-⁻))))
                  (A≤B+C=>A-C≤B
                    (≤S-cong-l
                      commu-⊓S
                      (≤S-cong-r
                        commu-+S
                        ⊓S-≤S))))))))

  M-head-sound :
    {Γ1 Γ2 Δ1 Δ2 : ListTerm} ->
    (hyp1 : botAG ≤S ⟦ head (Γ1 , Δ1) ⟧) ->
    (hyp2 : botAG ≤S ⟦ head (Γ2 , Δ2) ⟧) ->
    botAG ≤S ⟦ head (union Γ1 Γ2 , union Δ1 Δ2) ⟧
  M-head-sound {Γ1} {Γ2} {Δ1} {Δ2} hyp1 hyp2 =
    ≤S-cong-r
      {B = ((⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L))}
      (symₛ
        (beginₛ
          ⟦ union Δ1 Δ2 ⟧L +S (-S ⟦ union Γ1 Γ2 ⟧L)
            ≡ₛ⟨ ctxtₛ
                  (● +C (CC (-S ⟦ union Γ1 Γ2 ⟧L)))
                  (sem-union-eq-plus {Δ1} {Δ2}) ⟩
            (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L) +S (-S ⟦ union Γ1 Γ2 ⟧L)
               ≡ₛ⟨ ctxtₛ
                     ((CC (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L)) -C ●)
                     ((sem-union-eq-plus {Γ1} {Γ2})) ⟩
            (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L) +S (-S (⟦ Γ1 ⟧L +S ⟦ Γ2 ⟧L))
               ≡ₛ⟨ ctxtₛ
                     ((CC (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L)) +C ●)
                     -S-distri ⟩
            (⟦ Δ1 ⟧L +S ⟦ Δ2 ⟧L) +S ((-S ⟦ Γ1 ⟧L) -S ⟦ Γ2 ⟧L)
               ≡ₛ⟨ symₛ asso-+S ⟩
            ⟦ Δ1 ⟧L +S (⟦ Δ2 ⟧L +S ((-S ⟦ Γ1 ⟧L) -S ⟦ Γ2 ⟧L))
              ≡ₛ⟨ ctxtₛ
                    ((CC (⟦ Δ1 ⟧L)) +C ((CC ⟦ Δ2 ⟧L) +C ●))
                    commu-+S ⟩
            ⟦ Δ1 ⟧L +S (⟦ Δ2 ⟧L +S ((-S ⟦ Γ2 ⟧L) -S ⟦ Γ1 ⟧L))
              ≡ₛ⟨  ctxtₛ
                     ((CC (⟦ Δ1 ⟧L)) +C ●)
                     asso-+S ⟩
            ⟦ Δ1 ⟧L +S ((⟦ Δ2 ⟧L +S (-S ⟦ Γ2 ⟧L)) -S ⟦ Γ1 ⟧L)
              ≡ₛ⟨ ctxtₛ
                    ((CC (⟦ Δ1 ⟧L)) +C ●)
                    commu-+S ⟩
            ⟦ Δ1 ⟧L +S ((-S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L +S (-S ⟦ Γ2 ⟧L)))
              ≡ₛ⟨ asso-+S ⟩
            (⟦ Δ1 ⟧L -S ⟦ Γ1 ⟧L) +S (⟦ Δ2 ⟧L -S ⟦ Γ2 ⟧L) ∎ₛ))
      (≤S-cong-l
        neutral-+S
        (A≤B=>C≤D=>A+C≤B+D
          hyp1
          hyp2))

  Z-L-sound :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      botAG ≤S ⟦ G ∣ (Γ , Δ) ⟧ ->
      botAG ≤S ⟦ G ∣ (Γ ∷ botAG , Δ) ⟧
  Z-L-sound G Γ Δ hyp =
    ≤S-cong-r
      (ctxtₛ
        ((CC (⟦ G ⟧)) ⊔C ((CC ⟦ Δ ⟧L) -C ●))
        (symₛ neutral-+S))
      hyp
  
  Z-R-sound :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    botAG ≤S ⟦ G ∣ (Γ , Δ) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ botAG) ⟧
  Z-R-sound G Γ Δ hyp = 
    ≤S-cong-r
      (ctxtₛ
        ((CC (⟦ G ⟧)) ⊔C (● -C (CC ⟦ Γ ⟧L)))
        (symₛ neutral-+S))
      hyp

  minus-L-sound :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A : Term) ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ A) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ ∷ (-S A) , Δ) ⟧
  minus-L-sound G Γ Δ A hyp =
    ≤S-cong-r
      (ctxtₛ
        ((CC ⟦ G ⟧) ⊔C ●)
        (beginₛ
          (⟦ Δ ⟧L +S A) +S (-S ⟦ Γ ⟧L)
            ≡ₛ⟨ symₛ asso-+S ⟩
          ⟦ Δ ⟧L +S (A +S (-S ⟦ Γ ⟧L))
            ≡ₛ⟨ ctxtₛ
                  ((CC (⟦ Δ ⟧L)) +C (● -C (CC (⟦ Γ ⟧L))))
                  (symₛ -S--S) ⟩
          ⟦ Δ ⟧L +S ((-S (-S A)) +S (-S ⟦ Γ ⟧L))
            ≡ₛ⟨ ctxtₛ
                  ((CC (⟦ Δ ⟧L)) +C ●)
                  commu-+S ⟩
          ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S (-S A))
            ≡ₛ⟨ ctxtₛ
                  ((CC (⟦ Δ ⟧L)) +C ●)
                  (symₛ -S-distri) ⟩
          ⟦ Δ ⟧L -S (⟦ Γ ⟧L -S A) ∎ₛ))
      hyp

  minus-R-sound :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A : Term) ->
    botAG ≤S ⟦ G ∣ (Γ ∷ A , Δ) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ (-S A)) ⟧
  minus-R-sound G Γ Δ A hyp = 
    ≤S-cong-r
    (beginₛ
      ⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A))
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ G ⟧)) ⊔C ((CC (⟦ Δ ⟧L)) -C ●))
              commu-+S ⟩
      ⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S (A +S ⟦ Γ ⟧L))
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ G ⟧)) ⊔C ((CC (⟦ Δ ⟧L)) +C ●))
              -S-distri ⟩
      ⟦ G ⟧ ⊔S (⟦ Δ ⟧L +S ((-S A) -S ⟦ Γ ⟧L))
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ G ⟧)) ⊔C ●)
              asso-+S ⟩
      ⟦ G ⟧ ⊔S ((⟦ Δ ⟧L +S (-S A)) -S ⟦ Γ ⟧L)∎ₛ)
    hyp
    
  plus-L-sound :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣(Γ ∷ A ∷ B , Δ) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ ∷ (A +S B), Δ) ⟧
  plus-L-sound G Γ Δ A B hyp =
    ≤S-cong-r
      (ctxtₛ
        ((CC ⟦ G ⟧) ⊔C ((CC ⟦ Δ ⟧L) -C ●))
        (symₛ asso-+S))
      hyp
    
  plus-R-sound :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ A ∷ B) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ (A +S B)) ⟧
  plus-R-sound G Γ Δ A B hyp = 
    ≤S-cong-r
      (ctxtₛ
        ((CC ⟦ G ⟧) ⊔C (● -C (CC ⟦ Γ ⟧L)))
        (symₛ asso-+S))
      hyp

  max-L-sound :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣(Γ ∷ A , Δ) ⟧ ->
    botAG ≤S ⟦ G ∣(Γ ∷ B , Δ) ⟧ ->
    botAG ≤S ⟦ G ∣(Γ ∷ (A ⊔S B), Δ) ⟧
  max-L-sound G Γ Δ A B hyp1 hyp2 =
    ≤S-cong-r
      {B = (⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A))) ⊓S (⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B)))}
      (beginₛ
        ⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A)) ⊓S ⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))
          ≡ₛ⟨ ctxtₛ
                (● ⊓C ( CC (⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B)))))
                commu-⊔S ⟩
        (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A)) ⊔S ⟦ G ⟧ ⊓S ⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))
          ≡ₛ⟨ ctxtₛ
               (CC ((⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A)) ⊔S ⟦ G ⟧) ⊓C ●)
               commu-⊔S ⟩
        (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A)) ⊔S ⟦ G ⟧ ⊓S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B)) ⊔S ⟦ G ⟧
          ≡ₛ⟨ symₛ ⊔S-distri-⊓S ⟩
        ((⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A)) ⊓S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))) ⊔S ⟦ G ⟧
          ≡ₛ⟨ commu-⊔S ⟩
        ⟦ G ⟧ ⊔S ((⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A)) ⊓S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B)))
          ≡ₛ⟨ ctxtₛ
                ((CC ⟦ G ⟧) ⊔C ●)
                  (beginₛ
                    (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A)) ⊓S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))
                      ≡ₛ⟨ ctxtₛ
                            (((CC ⟦ Δ ⟧L) +C ●) ⊓C (CC (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))))
                            -S-distri ⟩
                    (⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S A)) ⊓S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))
                      ≡ₛ⟨ ctxtₛ
                            ((CC (⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S A))) ⊓C ((CC (⟦ Δ ⟧L)) +C ●))
                            -S-distri ⟩
                    (⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S A)) ⊓S (⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S B))
                      ≡ₛ⟨ ctxtₛ
                            (● ⊓C (CC (⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S B))))
                            asso-+S ⟩
                    ((⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S A) ⊓S (⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S B))
                      ≡ₛ⟨ ctxtₛ
                            ((CC ((⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S A)) ⊓C ●)
                            asso-+S ⟩
                    ((⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S A) ⊓S ((⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S B)
                      ≡ₛ⟨ ctxtₛ
                            (● ⊓C (CC ((⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S B)))
                            commu-+S ⟩
                    ((-S A) +S (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L))) ⊓S ((⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S B)
                      ≡ₛ⟨ ctxtₛ
                            ((CC ((-S A) +S (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)))) ⊓C ●)
                            commu-+S ⟩
                    ((-S A) +S (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L))) ⊓S ((-S B) +S (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)))
                      ≡ₛ⟨ ⊓S-+S ⟩
                    ((-S A) ⊓S (-S B)) +S (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L))
                      ≡ₛ⟨ commu-+S ⟩
                    (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) +S ((-S A) ⊓S (-S B))
                      ≡ₛ⟨ ctxtₛ
                            ((CC (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L))) +C ●)
                            (symₛ -S-⊔S-⊓S) ⟩
                    (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S (A ⊔S B)
                      ≡ₛ⟨ symₛ asso-+S ⟩
                    ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S (A ⊔S B))
                      ≡ₛ⟨ ctxtₛ
                            ((CC ⟦ Δ ⟧L) +C ●)
                            (symₛ -S-distri) ⟩
                    ⟦ Δ ⟧L -S (⟦ Γ ⟧L +S (A ⊔S B)) ∎ₛ) ⟩
        ⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A ⊔S B)) ∎ₛ)
      (≤S-⊓S
        hyp1
        hyp2)
  
  max-R-sound :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣(Γ , Δ ∷ A)∣(Γ , Δ ∷ B) ⟧ ->
    botAG ≤S ⟦ G ∣(Γ , Δ ∷ (A ⊔S B)) ⟧
  max-R-sound G Γ Δ A B hyp =
    ≤S-cong-r
      (transₛ
        (symₛ asso-⊔S)
        (ctxtₛ
          ((CC ⟦ G ⟧) ⊔C ●)
          (beginₛ
            ((⟦ Δ ⟧L +S A) -S ⟦ Γ ⟧L) ⊔S ((⟦ Δ ⟧L +S B) -S ⟦ Γ ⟧L)
              ≡ₛ⟨ symₛ ⊔S-+S ⟩
            ((⟦ Δ ⟧L +S A) ⊔S (⟦ Δ ⟧L +S B)) -S ⟦ Γ ⟧L
              ≡ₛ⟨ ctxtₛ
                    ((● ⊔C (CC (⟦ Δ ⟧L +S B))) -C (CC (⟦ Γ ⟧L)))
                    commu-+S ⟩
            ((A +S ⟦ Δ ⟧L) ⊔S (⟦ Δ ⟧L +S B)) -S ⟦ Γ ⟧L
              ≡ₛ⟨ ctxtₛ
                    (((CC (A +S ⟦ Δ ⟧L)) ⊔C ●) -C (CC ⟦ Γ ⟧L))
                    commu-+S ⟩
            ((A +S ⟦ Δ ⟧L) ⊔S (B +S ⟦ Δ ⟧L)) -S ⟦ Γ ⟧L
              ≡ₛ⟨ ctxtₛ
                    (● -C (CC ⟦ Γ ⟧L))
                    (symₛ ⊔S-+S) ⟩
            ((A ⊔S B) +S ⟦ Δ ⟧L) -S ⟦ Γ ⟧L
              ≡ₛ⟨ ctxtₛ
                    (● -C (CC ⟦ Γ ⟧L))
                    commu-+S ⟩
            (⟦ Δ ⟧L +S (A ⊔S B)) -S ⟦ Γ ⟧L ∎ₛ)))
      hyp

  min-L-sound :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣ (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ ∷ (A ⊓S B), Δ) ⟧
  min-L-sound G Γ Δ A B hyp =
    ≤S-cong-r
      {B = ⟦ G ⟧ ⊔S ((⟦ Δ ⟧L +S ((-S A) ⊔S (-S B))) -S ⟦ Γ ⟧L)}
      (ctxtₛ
        ((CC ⟦ G ⟧) ⊔C ●)
        (beginₛ
          (⟦ Δ ⟧L +S (-S A) ⊔S (-S B)) +S (-S ⟦ Γ ⟧L)
            ≡ₛ⟨ ctxtₛ
                  (((CC ⟦ Δ ⟧L) +C ●) +C (CC (-S ⟦ Γ ⟧L)))
                  (symₛ -S-⊓S-⊔S) ⟩
          (⟦ Δ ⟧L -S (A ⊓S B)) +S (-S ⟦ Γ ⟧L)
            ≡ₛ⟨ symₛ asso-+S ⟩
          ⟦ Δ ⟧L +S ((-S (A ⊓S B)) +S (-S ⟦ Γ ⟧L))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ●)
                  commu-+S ⟩
          ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S (A ⊓S B)))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ●)
                  (symₛ -S-distri) ⟩
          ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S (A ⊓S B))) ∎ₛ))
      (max-R-sound
        G
        Γ
        Δ
        (-S A)
        (-S B)
        (≤S-cong-r
          {B = (⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A))) ⊔S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))}
          (transₛ
            (ctxtₛ
              (((CC ⟦ G ⟧) ⊔C ●) ⊔C (CC (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))))
              (beginₛ
                ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S A))
                  ≡ₛ⟨ ctxtₛ
                        ((CC ⟦ Δ ⟧L) +C ●)
                        -S-distri ⟩
                ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S A))
                  ≡ₛ⟨ ctxtₛ
                        ((CC ⟦ Δ ⟧L) +C ●)
                        commu-+S ⟩
                ⟦ Δ ⟧L +S ((-S A) +S (-S ⟦ Γ ⟧L))
                  ≡ₛ⟨ asso-+S ⟩
                (⟦ Δ ⟧L +S (-S A)) +S (-S ⟦ Γ ⟧L) ∎ₛ))
            (ctxtₛ
              (((CC ⟦ G ⟧) ⊔C (CC ((⟦ Δ ⟧L +S (-S A)) -S ⟦ Γ ⟧L))) ⊔C ●)
              (beginₛ
                ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S B))
                  ≡ₛ⟨ ctxtₛ
                        ((CC ⟦ Δ ⟧L) +C ●)
                        -S-distri ⟩
                ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S B))
                  ≡ₛ⟨ ctxtₛ
                        ((CC ⟦ Δ ⟧L) +C ●)
                        commu-+S ⟩
                ⟦ Δ ⟧L +S ((-S B) +S (-S ⟦ Γ ⟧L))
                  ≡ₛ⟨ asso-+S ⟩
                (⟦ Δ ⟧L +S (-S B)) +S (-S ⟦ Γ ⟧L) ∎ₛ)))
          hyp))
  
  min-R-sound :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ A) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ B) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ (A ⊓S B)) ⟧
  min-R-sound G Γ Δ A B hyp1 hyp2 =
    ≤S-cong-r
      (ctxtₛ
        ((CC ⟦ G ⟧) ⊔C ●)
        (beginₛ
          ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S (-S A) ⊔S (-S B)))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ●)
                  -S-distri ⟩
          ⟦ Δ ⟧L +S (((-S (⟦ Γ ⟧L)) +S (-S ((-S A) ⊔S (-S B)))))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ((CC (-S (⟦ Γ ⟧L))) +C (-C ●)))
                  (symₛ -S-⊓S-⊔S) ⟩
          ⟦ Δ ⟧L +S (((-S (⟦ Γ ⟧L)) +S (-S (-S (A ⊓S B)))))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ((CC (-S (⟦ Γ ⟧L))) +C ●))
                  -S--S ⟩
          ⟦ Δ ⟧L +S (((-S (⟦ Γ ⟧L)) +S (A ⊓S B)))
            ≡ₛ⟨ ctxtₛ
                  ((CC (⟦ Δ ⟧L)) +C ●)
                  commu-+S ⟩
          ⟦ Δ ⟧L +S ((A ⊓S B) +S (-S (⟦ Γ ⟧L)))
            ≡ₛ⟨ asso-+S ⟩
          (⟦ Δ ⟧L +S A ⊓S B) +S (-S ⟦ Γ ⟧L) ∎ₛ))
      (max-L-sound
        G
        Γ
        Δ
        (-S A)
        (-S B)
        (≤S-cong-r
          (ctxtₛ
              ((CC ⟦ G ⟧) ⊔C ●)
              (symₛ
                (beginₛ
                  ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S (-S A)))
                    ≡ₛ⟨ ctxtₛ
                          ((CC ⟦ Δ ⟧L) +C ●)
                          -S-distri ⟩
                  ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S (-S A)))
                    ≡ₛ⟨ ctxtₛ
                          ((CC ⟦ Δ ⟧L) +C ((CC (-S (⟦ Γ ⟧L))) +C ●))
                          -S--S ⟩
                  ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S A)
                    ≡ₛ⟨ ctxtₛ
                          ((CC ⟦ Δ ⟧L) +C ●)
                          commu-+S ⟩
                  ⟦ Δ ⟧L +S (A +S (-S ⟦ Γ ⟧L))
                    ≡ₛ⟨ asso-+S ⟩
                  (⟦ Δ ⟧L +S A) +S (-S ⟦ Γ ⟧L) ∎ₛ)))
          hyp1)
        (≤S-cong-r
          ((ctxtₛ
              ((CC ⟦ G ⟧) ⊔C ●)
              (symₛ
                (beginₛ
                  ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S (-S B)))
                    ≡ₛ⟨ ctxtₛ
                          ((CC ⟦ Δ ⟧L) +C ●)
                          -S-distri ⟩
                  ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S (-S B)))
                    ≡ₛ⟨ ctxtₛ
                          ((CC ⟦ Δ ⟧L) +C ((CC (-S (⟦ Γ ⟧L))) +C ●))
                          -S--S ⟩
                  ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S B)
                    ≡ₛ⟨ ctxtₛ
                          ((CC ⟦ Δ ⟧L) +C ●)
                          commu-+S ⟩
                  ⟦ Δ ⟧L +S (B +S (-S ⟦ Γ ⟧L))
                    ≡ₛ⟨ asso-+S ⟩
                  (⟦ Δ ⟧L +S B) +S (-S ⟦ Γ ⟧L) ∎ₛ))))
          hyp2))


  Z-L-head-sound :
      (Γ Δ : ListTerm) ->
      botAG ≤S ⟦ head (Γ , Δ) ⟧ ->
      botAG ≤S ⟦ head (Γ ∷ botAG , Δ) ⟧
  Z-L-head-sound Γ Δ hyp =
    ≤S-cong-r
      (ctxtₛ
        (((CC ⟦ Δ ⟧L) -C ●))
        (symₛ neutral-+S))
      hyp
  
  Z-R-head-sound :
    (Γ Δ : ListTerm) ->
    botAG ≤S ⟦ head (Γ , Δ) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ ∷ botAG) ⟧
  Z-R-head-sound Γ Δ hyp = 
    ≤S-cong-r
      (ctxtₛ
        ((● -C (CC ⟦ Γ ⟧L)))
        (symₛ neutral-+S))
      hyp

  minus-L-head-sound :
    (Γ Δ : ListTerm) ->
    (A : Term) ->
    botAG ≤S ⟦ head (Γ , Δ ∷ A) ⟧ ->
    botAG ≤S ⟦ head (Γ ∷ (-S A) , Δ) ⟧
  minus-L-head-sound Γ Δ A hyp =
    ≤S-cong-r
        (beginₛ
          (⟦ Δ ⟧L +S A) +S (-S ⟦ Γ ⟧L)
            ≡ₛ⟨ symₛ asso-+S ⟩
          ⟦ Δ ⟧L +S (A +S (-S ⟦ Γ ⟧L))
            ≡ₛ⟨ ctxtₛ
                  ((CC (⟦ Δ ⟧L)) +C (● -C (CC (⟦ Γ ⟧L))))
                  (symₛ -S--S) ⟩
          ⟦ Δ ⟧L +S ((-S (-S A)) +S (-S ⟦ Γ ⟧L))
            ≡ₛ⟨ ctxtₛ
                  ((CC (⟦ Δ ⟧L)) +C ●)
                  commu-+S ⟩
          ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S (-S A))
            ≡ₛ⟨ ctxtₛ
                  ((CC (⟦ Δ ⟧L)) +C ●)
                  (symₛ -S-distri) ⟩
          ⟦ Δ ⟧L -S (⟦ Γ ⟧L -S A) ∎ₛ)
      hyp

  minus-R-head-sound :
    (Γ Δ : ListTerm) ->
    (A : Term) ->
    botAG ≤S ⟦ head (Γ ∷ A , Δ) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ ∷ (-S A)) ⟧
  minus-R-head-sound Γ Δ A hyp = 
    ≤S-cong-r
    (beginₛ
      (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A))
        ≡ₛ⟨ ctxtₛ
              (((CC (⟦ Δ ⟧L)) -C ●))
              commu-+S ⟩
      (⟦ Δ ⟧L -S (A +S ⟦ Γ ⟧L))
        ≡ₛ⟨ ctxtₛ
              (((CC (⟦ Δ ⟧L)) +C ●))
              -S-distri ⟩
      (⟦ Δ ⟧L +S ((-S A) -S ⟦ Γ ⟧L))
        ≡ₛ⟨ asso-+S ⟩
      ((⟦ Δ ⟧L +S (-S A)) -S ⟦ Γ ⟧L)∎ₛ)
    hyp
    
  plus-L-head-sound :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ ∷ A ∷ B , Δ) ⟧ ->
    botAG ≤S ⟦ head (Γ ∷ (A +S B), Δ) ⟧
  plus-L-head-sound Γ Δ A B hyp =
    ≤S-cong-r
      (ctxtₛ
        (((CC ⟦ Δ ⟧L) -C ●))
        (symₛ asso-+S))
      hyp
    
  plus-R-head-sound :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ , Δ ∷ A ∷ B) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ ∷ (A +S B)) ⟧
  plus-R-head-sound Γ Δ A B hyp = 
    ≤S-cong-r
      (ctxtₛ
        ((● -C (CC ⟦ Γ ⟧L)))
        (symₛ asso-+S))
      hyp
      
  max-L-head-sound :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head(Γ ∷ A , Δ) ⟧ ->
    botAG ≤S ⟦ head(Γ ∷ B , Δ) ⟧ ->
    botAG ≤S ⟦ head(Γ ∷ (A ⊔S B), Δ) ⟧
  max-L-head-sound Γ Δ A B hyp1 hyp2 =
    ≤S-cong-r
      (beginₛ
        (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A)) ⊓S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))
          ≡ₛ⟨ ctxtₛ
                (((CC ⟦ Δ ⟧L) +C ●) ⊓C (CC (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))))
                -S-distri ⟩
        (⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S A)) ⊓S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))
          ≡ₛ⟨ ctxtₛ
                ((CC (⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S A))) ⊓C ((CC (⟦ Δ ⟧L)) +C ●))
                -S-distri ⟩
        (⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S A)) ⊓S (⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S B))
          ≡ₛ⟨ ctxtₛ
                (● ⊓C (CC (⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S B))))
                asso-+S ⟩
        ((⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S A) ⊓S (⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S B))
          ≡ₛ⟨ ctxtₛ
                ((CC ((⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S A)) ⊓C ●)
                asso-+S ⟩
        ((⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S A) ⊓S ((⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S B)
          ≡ₛ⟨ ctxtₛ
                (● ⊓C (CC ((⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S B)))
                commu-+S ⟩
        ((-S A) +S (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L))) ⊓S ((⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S B)
          ≡ₛ⟨ ctxtₛ
                ((CC ((-S A) +S (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)))) ⊓C ●)
                commu-+S ⟩
        ((-S A) +S (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L))) ⊓S ((-S B) +S (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)))
          ≡ₛ⟨ ⊓S-+S ⟩
        ((-S A) ⊓S (-S B)) +S (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L))
          ≡ₛ⟨ commu-+S ⟩
        (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) +S ((-S A) ⊓S (-S B))
          ≡ₛ⟨ ctxtₛ
                ((CC (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L))) +C ●)
                (symₛ -S-⊔S-⊓S) ⟩
        (⟦ Δ ⟧L +S (-S ⟦ Γ ⟧L)) -S (A ⊔S B)
          ≡ₛ⟨ symₛ asso-+S ⟩
        ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) -S (A ⊔S B))
          ≡ₛ⟨ ctxtₛ
                ((CC ⟦ Δ ⟧L) +C ●)
                (symₛ -S-distri) ⟩
        ⟦ Δ ⟧L -S (⟦ Γ ⟧L +S (A ⊔S B)) ∎ₛ)
      (≤S-⊓S
        hyp1
        hyp2)

  max-R-head-sound :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ , Δ ∷ A)∣(Γ , Δ ∷ B) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ ∷ (A ⊔S B)) ⟧
  max-R-head-sound Γ Δ A B hyp =
    ≤S-cong-r
      (beginₛ
        ((⟦ Δ ⟧L +S A) -S ⟦ Γ ⟧L) ⊔S ((⟦ Δ ⟧L +S B) -S ⟦ Γ ⟧L)
          ≡ₛ⟨ symₛ ⊔S-+S ⟩
        ((⟦ Δ ⟧L +S A) ⊔S (⟦ Δ ⟧L +S B)) -S ⟦ Γ ⟧L
          ≡ₛ⟨ ctxtₛ
                ((● ⊔C (CC (⟦ Δ ⟧L +S B))) -C (CC (⟦ Γ ⟧L)))
                commu-+S ⟩
        ((A +S ⟦ Δ ⟧L) ⊔S (⟦ Δ ⟧L +S B)) -S ⟦ Γ ⟧L
          ≡ₛ⟨ ctxtₛ
                (((CC (A +S ⟦ Δ ⟧L)) ⊔C ●) -C (CC ⟦ Γ ⟧L))
                commu-+S ⟩
        ((A +S ⟦ Δ ⟧L) ⊔S (B +S ⟦ Δ ⟧L)) -S ⟦ Γ ⟧L
          ≡ₛ⟨ ctxtₛ
                (● -C (CC ⟦ Γ ⟧L))
                (symₛ ⊔S-+S) ⟩
        ((A ⊔S B) +S ⟦ Δ ⟧L) -S ⟦ Γ ⟧L
          ≡ₛ⟨ ctxtₛ
                (● -C (CC ⟦ Γ ⟧L))
                commu-+S ⟩
        (⟦ Δ ⟧L +S (A ⊔S B)) -S ⟦ Γ ⟧L ∎ₛ)
      hyp

  min-L-head-sound :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ) ⟧ ->
    botAG ≤S ⟦ head (Γ ∷ (A ⊓S B), Δ) ⟧
  min-L-head-sound Γ Δ A B hyp =
    ≤S-cong-r
      {B = ((⟦ Δ ⟧L +S ((-S A) ⊔S (-S B))) -S ⟦ Γ ⟧L)}
        (beginₛ
          (⟦ Δ ⟧L +S (-S A) ⊔S (-S B)) +S (-S ⟦ Γ ⟧L)
            ≡ₛ⟨ ctxtₛ
                  (((CC ⟦ Δ ⟧L) +C ●) +C (CC (-S ⟦ Γ ⟧L)))
                  (symₛ -S-⊓S-⊔S) ⟩
          (⟦ Δ ⟧L -S (A ⊓S B)) +S (-S ⟦ Γ ⟧L)
            ≡ₛ⟨ symₛ asso-+S ⟩
          ⟦ Δ ⟧L +S ((-S (A ⊓S B)) +S (-S ⟦ Γ ⟧L))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ●)
                  commu-+S ⟩
          ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S (A ⊓S B)))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ●)
                  (symₛ -S-distri) ⟩
          ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S (A ⊓S B))) ∎ₛ)
      (max-R-head-sound
        Γ
        Δ
        (-S A)
        (-S B)
        (≤S-cong-r
          {B = (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A)) ⊔S (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))}
          (transₛ
            (ctxtₛ
              (● ⊔C (CC (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))))
              (beginₛ
                ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S A))
                  ≡ₛ⟨ ctxtₛ
                        ((CC ⟦ Δ ⟧L) +C ●)
                        -S-distri ⟩
                ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S A))
                  ≡ₛ⟨ ctxtₛ
                        ((CC ⟦ Δ ⟧L) +C ●)
                        commu-+S ⟩
                ⟦ Δ ⟧L +S ((-S A) +S (-S ⟦ Γ ⟧L))
                  ≡ₛ⟨ asso-+S ⟩
                (⟦ Δ ⟧L +S (-S A)) +S (-S ⟦ Γ ⟧L) ∎ₛ))
            (ctxtₛ
              ((CC ((⟦ Δ ⟧L +S (-S A)) -S ⟦ Γ ⟧L)) ⊔C ●)
              (beginₛ
                ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S B))
                  ≡ₛ⟨ ctxtₛ
                        ((CC ⟦ Δ ⟧L) +C ●)
                        -S-distri ⟩
                ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S B))
                  ≡ₛ⟨ ctxtₛ
                        ((CC ⟦ Δ ⟧L) +C ●)
                        commu-+S ⟩
                ⟦ Δ ⟧L +S ((-S B) +S (-S ⟦ Γ ⟧L))
                  ≡ₛ⟨ asso-+S ⟩
                (⟦ Δ ⟧L +S (-S B)) +S (-S ⟦ Γ ⟧L) ∎ₛ)))
          hyp))
  
  min-R-head-sound :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ , Δ ∷ A) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ ∷ B) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ ∷ (A ⊓S B)) ⟧
  min-R-head-sound Γ Δ A B hyp1 hyp2 =
    ≤S-cong-r
        (beginₛ
          ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S (-S A) ⊔S (-S B)))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ●)
                  -S-distri ⟩
          ⟦ Δ ⟧L +S (((-S (⟦ Γ ⟧L)) +S (-S ((-S A) ⊔S (-S B)))))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ((CC (-S (⟦ Γ ⟧L))) +C (-C ●)))
                  (symₛ -S-⊓S-⊔S) ⟩
          ⟦ Δ ⟧L +S (((-S (⟦ Γ ⟧L)) +S (-S (-S (A ⊓S B)))))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ((CC (-S (⟦ Γ ⟧L))) +C ●))
                  -S--S ⟩
          ⟦ Δ ⟧L +S (((-S (⟦ Γ ⟧L)) +S (A ⊓S B)))
            ≡ₛ⟨ ctxtₛ
                  ((CC (⟦ Δ ⟧L)) +C ●)
                  commu-+S ⟩
          ⟦ Δ ⟧L +S ((A ⊓S B) +S (-S (⟦ Γ ⟧L)))
            ≡ₛ⟨ asso-+S ⟩
          (⟦ Δ ⟧L +S A ⊓S B) +S (-S ⟦ Γ ⟧L) ∎ₛ)
      (max-L-head-sound
        Γ
        Δ
        (-S A)
        (-S B)
        (≤S-cong-r
          (symₛ
            (beginₛ
              ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S (-S A)))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      -S-distri ⟩
              ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S (-S A)))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ((CC (-S (⟦ Γ ⟧L))) +C ●))
                      -S--S ⟩
              ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S A)
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      commu-+S ⟩
              ⟦ Δ ⟧L +S (A +S (-S ⟦ Γ ⟧L))
                ≡ₛ⟨ asso-+S ⟩
              (⟦ Δ ⟧L +S A) +S (-S ⟦ Γ ⟧L) ∎ₛ))
          hyp1)
        (≤S-cong-r
              (symₛ
                (beginₛ
                  ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S (-S B)))
                    ≡ₛ⟨ ctxtₛ
                          ((CC ⟦ Δ ⟧L) +C ●)
                          -S-distri ⟩
                  ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S (-S B)))
                    ≡ₛ⟨ ctxtₛ
                          ((CC ⟦ Δ ⟧L) +C ((CC (-S (⟦ Γ ⟧L))) +C ●))
                          -S--S ⟩
                  ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S B)
                    ≡ₛ⟨ ctxtₛ
                          ((CC ⟦ Δ ⟧L) +C ●)
                          commu-+S ⟩
                  ⟦ Δ ⟧L +S (B +S (-S ⟦ Γ ⟧L))
                    ≡ₛ⟨ asso-+S ⟩
                  (⟦ Δ ⟧L +S B) +S (-S ⟦ Γ ⟧L) ∎ₛ))
          hyp2))

  seq-exchange-sound :
    (G : HSeq) ->
    (Γ Γ' Δ Δ' : ListTerm) ->
    ListExchange Γ Γ' ->
    ListExchange Δ Δ' ->
    botAG ≤S ⟦ G ∣ (Γ , Δ) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ' , Δ') ⟧
  seq-exchange-sound G Γ Γ' Δ Δ' Γ=Γ' Δ=Δ' hyp =
    ≤S-cong-r
      (beginₛ
        ⟦ G ⟧ ⊔S (⟦ Δ ⟧L -S ⟦ Γ ⟧L)
          ≡ₛ⟨ ctxtₛ
                ((CC ⟦ G ⟧) ⊔C (● -C (CC ⟦ Γ ⟧L)))
                (ListExchangeSem Δ=Δ') ⟩
        ⟦ G ⟧ ⊔S (⟦ Δ' ⟧L -S ⟦ Γ ⟧L)
          ≡ₛ⟨ ctxtₛ
                ((CC ⟦ G ⟧) ⊔C ((CC ⟦ Δ' ⟧L) -C ●))
                (ListExchangeSem Γ=Γ') ⟩
        ⟦ G ⟧ ⊔S (⟦ Δ' ⟧L -S ⟦ Γ' ⟧L) ∎ₛ)
      hyp
    
  seq-exchange-head-sound :
    (Γ Γ' Δ Δ' : ListTerm) ->
    ListExchange Γ Γ' ->
    ListExchange Δ Δ' ->
    botAG ≤S ⟦ head (Γ , Δ) ⟧ ->
    botAG ≤S ⟦ head (Γ' , Δ') ⟧
  seq-exchange-head-sound Γ Γ' Δ Δ' Γ=Γ' Δ=Δ' hyp =
    ≤S-cong-r
      (beginₛ
        (⟦ Δ ⟧L -S ⟦ Γ ⟧L)
          ≡ₛ⟨ ctxtₛ
                ((● -C (CC ⟦ Γ ⟧L)))
                (ListExchangeSem Δ=Δ') ⟩
        (⟦ Δ' ⟧L -S ⟦ Γ ⟧L)
          ≡ₛ⟨ ctxtₛ
                (((CC ⟦ Δ' ⟧L) -C ●))
                (ListExchangeSem Γ=Γ') ⟩
        (⟦ Δ' ⟧L -S ⟦ Γ' ⟧L) ∎ₛ)
      hyp

  HSeqExchangeSem :
    {G G' : HSeq} ->
    (G=G' : HSeqExchange G G') ->
    ⟦ G ⟧ ≡ₛ ⟦ G' ⟧
  HSeqExchangeSem idHE =
    reflₛ
  HSeqExchangeSem {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') =
    beginₛ
      (⟦ G ⟧ ⊔S ⟦ H ⟧S) ⊔S ⟦ H' ⟧S
        ≡ₛ⟨ ctxtₛ
              ((● ⊔C (CC ⟦ H ⟧S)) ⊔C (CC ⟦ H' ⟧S))
              (HSeqExchangeSem G=G') ⟩
      (⟦ G' ⟧ ⊔S ⟦ H ⟧S) ⊔S ⟦ H' ⟧S
        ≡ₛ⟨ symₛ asso-⊔S ⟩
      ⟦ G' ⟧ ⊔S (⟦ H ⟧S ⊔S ⟦ H' ⟧S)
        ≡ₛ⟨ ctxtₛ
              ((CC ⟦ G' ⟧) ⊔C ●)
              commu-⊔S ⟩
      ⟦ G' ⟧ ⊔S (⟦ H' ⟧S ⊔S ⟦ H ⟧S)
        ≡ₛ⟨ asso-⊔S ⟩
      (⟦ G' ⟧ ⊔S ⟦ H' ⟧S) ⊔S ⟦ H ⟧S ∎ₛ
  HSeqExchangeSem {G ∣ H} {G' ∣ .H} (indHE .G .G' G=G') =
    ctxtₛ
      (● ⊔C (CC ⟦ H ⟧S))
      (HSeqExchangeSem G=G')
  HSeqExchangeSem exHE-head =
    commu-⊔S
  HSeqExchangeSem (transHE G=G' G=G'') =
    transₛ (HSeqExchangeSem G=G') (HSeqExchangeSem G=G'')

  hseq-exchange-sound :
    (G G' : HSeq) ->
    HSeqExchange G G' ->
    botAG ≤S ⟦ G ⟧ ->
    botAG ≤S ⟦ G' ⟧
  hseq-exchange-sound G G' G=G' hyp =
    ≤S-cong-r
      (HSeqExchangeSem G=G')
      hyp

  1-ax-sound :
    botAG ≤S (botAG +S one) -S botAG
  1-ax-sound =
    ≤S-cong-r
      (symₛ
        (beginₛ
          (botAG +S one) -S botAG
            ≡ₛ⟨ ctxtₛ
                  ((CC (botAG +S one)) +C ●)
                  (symₛ -S-botAG) ⟩
          (botAG +S one) +S botAG
            ≡ₛ⟨ neutral-+S ⟩
          botAG +S one
            ≡ₛ⟨ commu-+S ⟩
          one +S botAG
            ≡ₛ⟨ neutral-+S ⟩
          one ∎ₛ))
      0≤1

  ◆-linear :
    {T : ListTerm} ->
    (◆T : ◆List T) ->
    ◆ (⟦ remove◆ ◆T ⟧L) ≡ₛ ⟦ T ⟧L
  ◆-linear ◆[] =
    ◆Zero
  ◆-linear (◆∷ Γ A ◆T) =
    beginₛ
      ◆ (⟦ remove◆ ◆T ⟧L +S A)
        ≡ₛ⟨ ◆Linear
              (⟦ remove◆ ◆T ⟧L)
              A ⟩
      (◆ (⟦ remove◆ ◆T ⟧L)) +S (◆ A)
        ≡ₛ⟨ ctxtₛ
              (● +C (CC (◆ A)))
              (◆-linear ◆T) ⟩
      ⟦ Γ ⟧L +S (◆ A) ∎ₛ

  constantListInterpretation :
    (A : Term) ->
    (k : ℕ) ->
    ⟦ constantList A k ⟧L ≡ₛ k *S A
  constantListInterpretation A zero =
    reflₛ
  constantListInterpretation A (suc zero) = 
    transₛ
      commu-+S
      neutral-+S
  constantListInterpretation A (suc (suc k)) =
    transₛ
      commu-+S
      (ctxtₛ
        ((CC A) +C ●)
        (constantListInterpretation A (suc k)))

  ◆-rule-sound :
    {T D : ListTerm} ->
    (◆T : ◆List T) ->
    (◆D : ◆List D) ->
    (k : ℕ) ->
    botAG ≤S ⟦ head (remove◆ ◆T , union (remove◆ ◆D) (constantList one k)) ⟧ ->
    botAG ≤S ⟦ union D (constantList one k) ⟧L -S ⟦ T ⟧L
  ◆-rule-sound {T} {D} ◆T ◆D k ind =
    ≤S-cong-r
      {B = (◆ (⟦ remove◆ ◆D ⟧L) +S (k *S one)) -S (◆ (⟦ remove◆ ◆T ⟧L))}
      (beginₛ
        (◆ ⟦ remove◆ ◆D ⟧L +S (k *S one)) -S ◆ ⟦ remove◆ ◆T ⟧L
          ≡ₛ⟨ ctxtₛ
                (CC (◆ ⟦ remove◆ ◆D ⟧L +S (k *S one)) -C ●)
                (◆-linear ◆T) ⟩
        (◆ ⟦ remove◆ ◆D ⟧L +S (k *S one)) -S ⟦ T ⟧L
          ≡ₛ⟨ ctxtₛ
                ((◆C (CC (⟦ remove◆ ◆D ⟧L)) +C ●) -C (CC (⟦ T ⟧L)))
                (symₛ (constantListInterpretation one k)) ⟩
        (◆ ⟦ remove◆ ◆D ⟧L +S ⟦ constantList one k ⟧L) -S ⟦ T ⟧L
          ≡ₛ⟨ ctxtₛ
                ((● +C (CC ⟦ constantList one k ⟧L)) -C (CC ⟦ T ⟧L))
                (◆-linear ◆D) ⟩
        (⟦ D ⟧L +S ⟦ constantList one k ⟧L) -S ⟦ T ⟧L
          ≡ₛ⟨ ctxtₛ
                (● -C (CC ⟦ T ⟧L))
                (symₛ sem-union-eq-plus) ⟩
        ⟦ union D (constantList one k) ⟧L -S ⟦ T ⟧L ∎ₛ)
      (≤S-trans
        {B = (◆ ⟦ remove◆ ◆D ⟧L +S (◆ (k *S one))) -S ◆ ⟦ remove◆ ◆T ⟧L}
        (≤S-cong-r
          {B = ◆ (⟦ union (remove◆ ◆D) (constantList one k) ⟧L -S ⟦ remove◆ ◆T ⟧L)}
          (symₛ
            (transₛ
              (ctxtₛ
                (● -C (◆C (CC ⟦ remove◆ ◆T ⟧L)))
                (symₛ
                  (◆Linear
                    (⟦ remove◆ ◆D ⟧L)
                    (k *S one))))
              (transₛ
                (ctxtₛ
                  ((CC ( ◆ (⟦ remove◆ ◆D ⟧L +S (k *S one)))) +C ●)
                  (symₛ
                    (◆-A=-◆A (⟦ remove◆ ◆T ⟧L))))
                (transₛ
                  (symₛ (◆Linear (⟦ remove◆ ◆D ⟧L +S (k *S one)) (-S ⟦ remove◆ ◆T ⟧L)))
                  (ctxtₛ
                    (◆C (● -C (CC (⟦ remove◆ ◆T ⟧L))))
                    (transₛ
                      (ctxtₛ
                        ((CC (⟦ remove◆ ◆D ⟧L)) +C ●)
                        (symₛ (constantListInterpretation one k)))
                      (symₛ sem-union-eq-plus)))))))
          (≤S-cong-l
            {A = ◆ botAG}
            ◆Zero
            (beginₛ
              (◆ botAG) ⊓S (◆ (⟦ union (remove◆ ◆D) (constantList one k) ⟧L -S ⟦ remove◆ ◆T ⟧L))
                ≡ₛ⟨ ctxtₛ
                      ((◆C ●) ⊓C (CC (◆ (⟦ union (remove◆ ◆D) (constantList one k) ⟧L -S ⟦ remove◆ ◆T ⟧L))))
                      (symₛ ind) ⟩
              (◆ (botAG ⊓S (⟦ union (remove◆ ◆D) (constantList one k) ⟧L -S ⟦ remove◆ ◆T ⟧L))) ⊓S (◆ (⟦ union (remove◆ ◆D) (constantList one k) ⟧L -S ⟦ remove◆ ◆T ⟧L))
                ≡ₛ⟨ ctxtₛ
                    ((◆C ●) ⊓C (CC (◆ (⟦ union (remove◆ ◆D) (constantList one k) ⟧L -S ⟦ remove◆ ◆T ⟧L))))
                    commu-⊓S ⟩
              (◆ ((⟦ union (remove◆ ◆D) (constantList one k) ⟧L -S ⟦ remove◆ ◆T ⟧L) ⊓S botAG)) ⊓S (◆ (⟦ union (remove◆ ◆D) (constantList one k) ⟧L -S ⟦ remove◆ ◆T ⟧L))
                ≡ₛ⟨ ◆Monotony
                      (⟦ union (remove◆ ◆D) (constantList one k) ⟧L -S ⟦ remove◆ ◆T ⟧L)
                      botAG ⟩
              ◆ ((⟦ union (remove◆ ◆D) (constantList one k) ⟧L -S ⟦ remove◆ ◆T ⟧L) ⊓S botAG)
                ≡ₛ⟨ ctxtₛ
                      (◆C ●)
                      commu-⊓S ⟩
              ◆ (botAG ⊓S (⟦ union (remove◆ ◆D) (constantList one k) ⟧L -S ⟦ remove◆ ◆T ⟧L))
                ≡ₛ⟨ ctxtₛ
                      (◆C ●)
                      ind ⟩
              ◆ botAG ∎ₛ)))
        (A≤B=>C≤D=>A+C≤B+D
          {◆ ⟦ remove◆ ◆D ⟧L +S ◆ (k *S one)}
          {◆ ⟦ remove◆ ◆D ⟧L +S (k *S one)}
          (A≤B=>C≤D=>A+C≤B+D
            {◆ ⟦ remove◆ ◆D ⟧L}
            ≤S-refl
            (◆k*1≤k*1 k))
          ≤S-refl))

  can-sound :
    (G : HSeq) ->
    (T D : ListTerm) ->
    (A : Term) ->
    botAG ≤S ⟦ G ∣ (T ∷ A , D ∷ A) ⟧ ->
    botAG ≤S ⟦ G ∣ (T , D) ⟧
  can-sound G T D A ind =
    ≤S-cong-r
      (ctxtₛ
        ((CC (⟦ G ⟧)) ⊔C ●)
        (beginₛ
          (⟦ D ⟧L +S A) +S (-S (⟦ T ⟧L +S A))
            ≡ₛ⟨ ctxtₛ
                  ((CC (⟦ D ⟧L +S A)) +C ●)
                  -S-distri ⟩
          (⟦ D ⟧L +S A) +S ((-S (⟦ T ⟧L)) -S A)
            ≡ₛ⟨ ctxtₛ
                  ((CC (⟦ D ⟧L +S A)) +C ●)
                  commu-+S ⟩
          (⟦ D ⟧L +S A) +S ((-S A) -S (⟦ T ⟧L))
            ≡ₛ⟨ asso-+S ⟩
          ((⟦ D ⟧L +S A) -S A) -S (⟦ T ⟧L)
            ≡ₛ⟨ ctxtₛ
                  (● -C (CC (⟦ T ⟧L)))
                  (symₛ asso-+S) ⟩
          (⟦ D ⟧L +S (A -S A)) -S (⟦ T ⟧L)
            ≡ₛ⟨ ctxtₛ
                  (((CC (⟦ D ⟧L)) +C ●) -C (CC (⟦ T ⟧L)))
                  opp-+S ⟩
          (⟦ D ⟧L +S botAG) -S (⟦ T ⟧L)
            ≡ₛ⟨ ctxtₛ
                  (● -C (CC (⟦ T ⟧L)))
                  neutral-+S ⟩
          ⟦ D ⟧L -S (⟦ T ⟧L) ∎ₛ))
      ind

  can-head-sound :
    (T D : ListTerm) ->
    (A : Term) ->
    botAG ≤S ⟦ head (T ∷ A , D ∷ A) ⟧ ->
    botAG ≤S ⟦ head (T , D) ⟧
  can-head-sound T D A ind =
    ≤S-cong-r
      (beginₛ
        (⟦ D ⟧L +S A) +S (-S (⟦ T ⟧L +S A))
          ≡ₛ⟨ ctxtₛ
                ((CC (⟦ D ⟧L +S A)) +C ●)
                -S-distri ⟩
        (⟦ D ⟧L +S A) +S ((-S (⟦ T ⟧L)) -S A)
          ≡ₛ⟨ ctxtₛ
                ((CC (⟦ D ⟧L +S A)) +C ●)
                commu-+S ⟩
        (⟦ D ⟧L +S A) +S ((-S A) -S (⟦ T ⟧L))
          ≡ₛ⟨ asso-+S ⟩
        ((⟦ D ⟧L +S A) -S A) -S (⟦ T ⟧L)
          ≡ₛ⟨ ctxtₛ
                (● -C (CC (⟦ T ⟧L)))
                (symₛ asso-+S) ⟩
        (⟦ D ⟧L +S (A -S A)) -S (⟦ T ⟧L)
          ≡ₛ⟨ ctxtₛ
                (((CC (⟦ D ⟧L)) +C ●) -C (CC (⟦ T ⟧L)))
                opp-+S ⟩
        (⟦ D ⟧L +S botAG) -S (⟦ T ⟧L)
          ≡ₛ⟨ ctxtₛ
                (● -C (CC (⟦ T ⟧L)))
                neutral-+S ⟩
        ⟦ D ⟧L -S (⟦ T ⟧L) ∎ₛ)
      ind

  cut-sound :
    (G : HSeq) ->
    (T1 T2 D1 D2 : ListTerm) ->
    (A : Term) ->
    botAG ≤S ⟦ (G ∣ (T1 ∷ A , D1)) ⟧ ->
    botAG ≤S ⟦ (G ∣ (T2 , D2 ∷ A)) ⟧ ->
    botAG ≤S ⟦ (G ∣ (union T1 T2 , union D1 D2)) ⟧
  cut-sound G T1 T2 D1 D2 A ind ind' = 
    can-sound
      G
      (union T1 T2)
      (union D1 D2)
      A
      (≤S-cong-r
        {B = ⟦ G ⟧ ⊔S ((⟦ union D1 D2 ⟧L +S A) -S (⟦ union (T1 ∷ A) T2 ⟧L))}
        (ctxtₛ
          ((CC (⟦ G ⟧)) ⊔C ((CC (⟦ union D1 D2 ⟧L +S A)) -C ●))
          (ListExchangeSem
            (exchangeUnionLast
              T1
              T2
              A)))
        (M-sound
          {G}
          {T1 ∷ A}
          {T2}
          {D1}
          {D2 ∷ A}
          ind
          ind'))

  cut-head-sound :
    (T1 T2 D1 D2 : ListTerm) ->
    (A : Term) ->
    botAG ≤S ⟦ (head (T1 ∷ A , D1)) ⟧ ->
    botAG ≤S ⟦ (head (T2 , D2 ∷ A)) ⟧ ->
    botAG ≤S ⟦ (head (union T1 T2 , union D1 D2)) ⟧
  cut-head-sound T1 T2 D1 D2 A ind ind' = 
    can-head-sound
      (union T1 T2)
      (union D1 D2)
      A
      (≤S-cong-r
        {B = ((⟦ union D1 D2 ⟧L +S A) -S (⟦ union (T1 ∷ A) T2 ⟧L))}
        (ctxtₛ
          ((CC (⟦ union D1 D2 ⟧L +S A)) -C ●)
          (ListExchangeSem
            (exchangeUnionLast
              T1
              T2
              A)))
        (M-head-sound
          {T1 ∷ A}
          {T2}
          {D1}
          {D2 ∷ A}
          ind
          ind'))
    

  soundness :
    {G : HSeq} ->
    (p : MGA G) ->
    botAG ≤S ⟦ G ⟧
  soundness (ax A) =
    ax-sound
  soundness Δ-ax =
    Δ-ax-sound
  soundness (W G Γ1 Γ2 Δ1 Δ2 p) =
    W-sound {G} {Γ1} {Γ2} {Δ1} {Δ2} (soundness p)
  soundness (C G Γ Δ p) =
    C-sound {G} {Γ} {Δ} (soundness p)
  soundness (S G Γ1 Γ2 Δ1 Δ2 refl refl p) =
    S-sound {G} {Γ1} {Γ2} {Δ1} {Δ2} (soundness p)
  soundness (M G Γ1 Γ2 Δ1 Δ2 refl refl p p₁) =
    M-sound {G} {Γ1} {Γ2} {Δ1} {Δ2} (soundness p) (soundness p₁)
  soundness (Z-L G Γ Δ p) =
    Z-L-sound G Γ Δ (soundness p)
  soundness (Z-R G Γ Δ p) =
    Z-R-sound G Γ Δ (soundness p)
  soundness (minus-L G Γ Δ A p) =
    minus-L-sound G Γ Δ A (soundness p)
  soundness (minus-R G Γ Δ A p) = 
    minus-R-sound G Γ Δ A (soundness p)
  soundness (plus-L G Γ Δ A B p) = 
    plus-L-sound G Γ Δ A B (soundness p)
  soundness (plus-R G Γ Δ A B p) = 
    plus-R-sound G Γ Δ A B (soundness p)
  soundness (max-L G Γ Δ A B p p₁) = 
    max-L-sound G Γ Δ A B (soundness p) (soundness p₁)
  soundness (max-R G Γ Δ A B p) = 
    max-R-sound G Γ Δ A B (soundness p)
  soundness (min-L G Γ Δ A B p) = 
    min-L-sound G Γ Δ A B (soundness p)
  soundness (min-R G Γ Δ A B p p₁) = 
    min-R-sound G Γ Δ A B (soundness p) (soundness p₁)
  soundness (W-head Γ1 Γ2 Δ1 Δ2 p) =
    W-sound-head {Γ1} {Γ2} {Δ1} {Δ2} (soundness p)
  soundness (C-head Γ Δ p) =
    C-sound-head {Γ} {Δ} (soundness p)
  soundness (S-head Γ1 Γ2 Δ1 Δ2 refl refl p) =
    S-head-sound {Γ1} {Γ2} {Δ1} {Δ2} (soundness p)
  soundness (M-head Γ1 Γ2 Δ1 Δ2 refl refl p p₁) =
    M-head-sound {Γ1} {Γ2} {Δ1} {Δ2} (soundness p) (soundness p₁)
  soundness (Z-L-head Γ Δ p) =
    Z-L-head-sound Γ Δ (soundness p)
  soundness (Z-R-head Γ Δ p) =
    Z-R-head-sound Γ Δ (soundness p)
  soundness (minus-L-head Γ Δ A p) =
    minus-L-head-sound Γ Δ A (soundness p)
  soundness (minus-R-head Γ Δ A p) =
    minus-R-head-sound Γ Δ A (soundness p)
  soundness (plus-L-head Γ Δ A B p) =
    plus-L-head-sound Γ Δ A B (soundness p)
  soundness (plus-R-head Γ Δ A B p) =
    plus-R-head-sound Γ Δ A B (soundness p)
  soundness (max-L-head Γ Δ A B p p₁) =
    max-L-head-sound Γ Δ A B (soundness p) (soundness p₁)
  soundness (max-R-head Γ Δ A B p) =
    max-R-head-sound Γ Δ A B (soundness p)
  soundness (min-L-head Γ Δ A B p) =
    min-L-head-sound Γ Δ A B (soundness p)
  soundness (min-R-head Γ Δ A B p p₁) =
    min-R-head-sound Γ Δ A B (soundness p) (soundness p₁)
  soundness (seq-exchange G Γ Γ' Δ Δ' x x₁ p) =
    seq-exchange-sound G Γ Γ' Δ Δ' x x₁ (soundness p)
  soundness (seq-exchange-head Γ Γ' Δ Δ' x x₁ p) =
    seq-exchange-head-sound Γ Γ' Δ Δ' x x₁ (soundness p)
  soundness (hseq-exchange G G' x p) =
    hseq-exchange-sound G G' x (soundness p)
  soundness (◆-rule T D ◆T ◆D k refl refl refl p) =
    ◆-rule-sound ◆T ◆D k (soundness p)
  soundness 1-ax = 1-ax-sound
  soundness (cut G T T' D D' A refl refl p p') =
    cut-sound G T T' D D' A (soundness p) (soundness p')
  soundness (cut-head T T' D D' A refl refl p p') = 
    cut-head-sound T T' D D' A (soundness p) (soundness p')

