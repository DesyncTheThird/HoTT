module En.SMG where

open import En.Prelude
open import Cubical.Reflection.RecordEquiv

record SMG* {ℓ} (El : Type ℓ) : Type ℓ where
  constructor smg*
  field
    𝕀 : El
    _⊗_ : El → El → El
  field
    α : (X Y Z : El) → (X ⊗ Y) ⊗ Z ≡ X ⊗ (Y ⊗ Z)
    Λ : (X : El) → 𝕀 ⊗ X ≡ X
    ρ : (X : El) → X ⊗ 𝕀 ≡ X
    β : (X Y : El) → X ⊗ Y ≡ Y ⊗ X
  field
    ▽ : (X Y : El) → sym (α X 𝕀 Y) ∙ ap (_⊗ Y) (ρ X) ≡ ap (X ⊗_) (Λ Y)
    ⬠ : (W X Y Z : El)
      → α (W ⊗ X) Y Z ∙ α W X (Y ⊗ Z)
      ≡ ap (_⊗ Z) (α W X Y) ∙ α W (X ⊗ Y) Z ∙ ap (W ⊗_) (α X Y Z)
    ⬡ : (X Y Z : El)
      → α X Y Z ∙ β X (Y ⊗ Z) ∙ α Y Z X
      ≡ ap (_⊗ Z) (β X Y) ∙ α Y X Z ∙ ap (Y ⊗_) (β X Z)
    β² : (X Y : El) → β X Y ∙ β Y X ≡ refl
    is-groupoid : isGroupoid El

open SMG* public

record SMG*Fun {ℓ₁ ℓ₂}
  {A : Type ℓ₁} (A* : SMG* A)
  {B : Type ℓ₂} (B* : SMG* B)
  (f : A → B) : Type (ℓ-max ℓ₁ ℓ₂) where
  constructor smg*fun
  private
    module A = SMG* A*
    module B = SMG* B*
  field
    f-𝕀 : f A.𝕀 ≡ B.𝕀
    f-⊗ : (X Y : A) → f (X A.⊗ Y) ≡ f X B.⊗ f Y
  field
    f-α : (X Y Z : A)
        → ap f (A.α X Y Z) ∙ f-⊗ X (Y A.⊗ Z) ∙ ap (f X B.⊗_) (f-⊗ Y Z)
        ≡ f-⊗ (X A.⊗ Y) Z ∙ ap (B._⊗ f Z) (f-⊗ X Y) ∙ B.α (f X) (f Y) (f Z)
    f-Λ : (X : A) → ap f (A.Λ X) ≡ f-⊗ (A.𝕀) X ∙ ap (B._⊗ f X) f-𝕀 ∙ B.Λ (f X)
    f-ρ : (X : A) → ap f (A.ρ X) ≡ f-⊗ X (A.𝕀) ∙ ap (f X B.⊗_) f-𝕀 ∙ B.ρ (f X)
    f-β : (X Y : A) → ap f (A.β X Y) ∙ f-⊗ Y X ≡ f-⊗ X Y ∙ B.β (f X) (f Y)

open SMG*Fun public

record SMG*Sq {ℓ} (El : Type ℓ) : Type ℓ where
  constructor smg*sq
  field
    𝕀 : El
    _⊗_ : El → El → El
  field
    α : (X Y Z : El) → (X ⊗ Y) ⊗ Z ≡ X ⊗ (Y ⊗ Z)
    Λ : (X : El) → 𝕀 ⊗ X ≡ X
    ρ : (X : El) → X ⊗ 𝕀 ≡ X
    β : (X Y : El) → X ⊗ Y ≡ Y ⊗ X
  field
    ▽ : (X Y : El) → Square (ap (X ⊗_) (Λ Y)) (ap (_⊗ Y) (ρ X)) (sym (α X 𝕀 Y)) refl

    ⬠₌ : (W X Y Z : El)
        → ((W ⊗ X) ⊗ Y) ⊗ Z ≡ W ⊗ (X ⊗ (Y ⊗ Z))
    ⬠₁ : (W X Y Z : El)
        → Square (sym (α (W ⊗ X) Y Z)) (α W X (Y ⊗ Z)) refl (⬠₌ W X Y Z)
    ⬠₂ : (W X Y Z : El)
        → Square (ap (_⊗ Z) (α W X Y)) (sym (ap (W ⊗_) (α X Y Z))) (⬠₌ W X Y Z) (α W (X ⊗ Y) Z)

    ⬡₌ : (X Y Z : El)
        → (X ⊗ Y) ⊗ Z ≡ Y ⊗ (Z ⊗ X)
    ⬡₁ : (X Y Z : El)
        → Square (sym (α X Y Z)) (α Y Z X) (β X (Y ⊗ Z)) (⬡₌ X Y Z)
    ⬡₂ : (X Y Z : El)
        → Square (ap (_⊗ Z) (β X Y)) (ap (Y ⊗_) (sym (β X Z))) (⬡₌ X Y Z) (α Y X Z)

    β² : (X Y : El) → β X Y ≡ sym (β Y X)

    is-groupoid : isGroupoid El

open SMG*Sq public

record SMG*Fun*Sq {ℓ₁ ℓ₂}
  {A : Type ℓ₁} (A* : SMG*Sq A)
  {B : Type ℓ₂} (B* : SMG*Sq B)
  (f : A → B) : Type (ℓ-max ℓ₁ ℓ₂) where
  constructor smg*fun*sq
  private
    module A = SMG*Sq A*
    module B = SMG*Sq B*
  field
    f-𝕀 : f A.𝕀 ≡ B.𝕀
    f-⊗ : (X Y : A) → f (X A.⊗ Y) ≡ f X B.⊗ f Y
  field
    f-α₌ : (X Y Z : A)
        → f (X A.⊗ Y) B.⊗ f Z ≡ f X B.⊗ f (Y A.⊗ Z)
    f-α₁ : (X Y Z : A)
        → Square
            (ap f (A.α X Y Z))
            (f-α₌ X Y Z)
            (f-⊗ (X A.⊗ Y) Z)
            (f-⊗ X (Y A.⊗ Z))
    f-α₂ : (X Y Z : A)
        → Square
            (f-α₌ X Y Z)
            (B.α (f X) (f Y) (f Z))
            (ap (B._⊗ f Z) (f-⊗ X Y))
            (ap (f X B.⊗_) (f-⊗ Y Z))

    f-Λ : (X : A)
        → Square
            (f-⊗ A.𝕀 X)
            (sym (B.Λ (f X)))
            (ap f (A.Λ X))
            (ap (B._⊗ f X) f-𝕀)

    f-ρ : (X : A)
        → Square
            (f-⊗ X A.𝕀)
            (sym (B.ρ (f X)))
            (ap f (A.ρ X))
            (ap (f X B.⊗_) f-𝕀)

    f-β : (X Y : A) → Square (f-⊗ X Y) (f-⊗ Y X) (ap f (A.β X Y)) (B.β (f X) (f Y))

open SMG*Fun*Sq public

unquoteDecl SMG*Fun*SqIsoΣ = declareRecordIsoΣ SMG*Fun*SqIsoΣ (quote SMG*Fun*Sq)

private
  isSetSquareFromGroupoid : ∀ {ℓ} {X : Type ℓ}
    (X-is-groupoid : isGroupoid X)
    {x₀₀ x₀₁ x₁₀ x₁₁ : X}
    (x₀₋ : x₀₀ ≡ x₀₁)
    (x₁₋ : x₁₀ ≡ x₁₁)
    (x₋₀ : x₀₀ ≡ x₁₀)
    (x₋₁ : x₀₁ ≡ x₁₁)
    → isSet (Square x₀₋ x₁₋ x₋₀ x₋₁)
  isSetSquareFromGroupoid X-is-groupoid {x₁₀ = x₁₀} {x₁₁ = x₁₁} x₀₋ x₁₋ x₋₀ x₋₁ =
    isOfHLevelPathP 2 (X-is-groupoid x₁₀ x₁₁) x₀₋ x₁₋

SMG*Fun*Sq-isSet : ∀ {ℓ} {A : Type ℓ} {A* : SMG*Sq A} {B : Type ℓ} {B* : SMG*Sq B} (f : A → B)
    → isSet (SMG*Fun*Sq A* B* f)
SMG*Fun*Sq-isSet {B* = B*} f =
  let module B = SMG*Sq B* in
  isOfHLevelRetractFromIso 2 SMG*Fun*SqIsoΣ
    (isSetΣ (B.is-groupoid _ _) λ _ →
    isSetΣ (isSetΠ2 λ _ _ → B.is-groupoid _ _) λ _ →
    isSetΣ (isSetΠ3 λ _ _ _ → B.is-groupoid _ _) λ _ →
    isSetΣ (isSetΠ3 λ _ _ _ → isSetSquareFromGroupoid B.is-groupoid _ _ _ _) λ _ →
    isSetΣ (isSetΠ3 λ _ _ _ → isSetSquareFromGroupoid B.is-groupoid _ _ _ _) λ _ →
    isSetΣ (isSetΠ λ _ → isSetSquareFromGroupoid B.is-groupoid _ _ _ _) λ _ →
    isSetΣ (isSetΠ λ _ → isSetSquareFromGroupoid B.is-groupoid _ _ _ _) λ _ →
    isSetΠ2 λ _ _ → isSetSquareFromGroupoid B.is-groupoid _ _ _ _)

record SMG*Nat*Sq {ℓ}
  {A : Type ℓ} {A* : SMG*Sq A}
  {B : Type ℓ} {B* : SMG*Sq B}
  {f g : A → B}
  (f* : SMG*Fun*Sq A* B* f)
  (g* : SMG*Fun*Sq A* B* g)
  : Type ℓ where
  constructor smg*nat*sq
  private
    module A = SMG*Sq A*
    module B = SMG*Sq B*
    module f* = SMG*Fun*Sq f*
    module g* = SMG*Fun*Sq g*
  field
    nat : (X : A) → f X ≡ g X
    nat-𝕀 : Square (f* .f-𝕀) (g* .f-𝕀) (nat A.𝕀) refl
    nat-⊗ : (X Y : A) → Square (f* .f-⊗ X Y) (g* .f-⊗ X Y) (nat (X A.⊗ Y)) (ap₂ B._⊗_ (nat X) (nat Y))

module _ {ℓ}
  {A : Type ℓ} {A* : SMG*Sq A}
  {B : Type ℓ} {B* : SMG*Sq B}
  {f g : A → B}
  (f* : SMG*Fun*Sq A* B* f)
  (g* : SMG*Fun*Sq A* B* g)
  where

  -- lemma : (s : SMG*Nat*Sq f* g*) → PathP (λ i → SMG*Fun*Sq A* B* (λ x → SMG*Nat*Sq.nat s x i)) f* g*
  -- lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .f-𝕀 = nat-𝕀 i
  -- lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .f-⊗ X Y = nat-⊗ X Y i
  -- lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .f-α₌ X Y Z = {!!}
  -- lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .f-α₁ = {!!}
  -- lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .f-α₂ = {!!}
  -- lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .f-Λ X = isSet→SquareP {!!} {!!} {!!} {!!} {!!} i
  -- lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .f-ρ = {!!}
  -- lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .f-β = {!!}

  -- SMG*Fun*Sq≡ : SMG*Nat*Sq f* g* → (f , f*) ≡ (g , g*)
  -- SMG*Fun*Sq≡ (smg*nat*sq nat nat-𝕀 nat-⊗) =
  --   ΣPathP (
  --     funExt nat ,
  --     {!!}
  --     -- λ i → smg*fun*sq (nat-𝕀 i) (λ X Y → nat-⊗ X Y i)
  --     -- (λ X Y Z → {!!}) {!!} {!!} {!!} {!!} {!!}
  --   )

-- Goal: Square (nat-⊗ (𝕀 A*) X i) (sym (Λ B* (nat X i)))
--       (ap (λ x → nat x i) (Λ A* X))
--       (ap (λ section₁ → (B* ⊗ section₁) (nat X i)) (nat-𝕀 i))
-- ———— Boundary (wanted) —————————————————————————————————————
-- i = i0 ⊢ f-Λ f* X
-- i = i1 ⊢ f-Λ g* X
-- ————————————————————————————————————————————————————————————
-- X     : A
-- i     : I
-- nat-⊗ : (X₁ Y : A) →
--         Square (f-⊗ f* X₁ Y) (f-⊗ g* X₁ Y) (nat ((A* ⊗ X₁) Y))
--         (ap₂ (_⊗_ B*) (nat X₁) (nat Y))
-- nat-𝕀 : Square (f-𝕀 f*) (f-𝕀 g*) (nat (𝕀 A*)) refl
-- nat   : (X₁ : A) → f X₁ ≡ g X₁
-- g*    : SMG*Fun*Sq A* B* g
-- f*    : SMG*Fun*Sq A* B* f
-- g     : A → B
-- f     : A → B
-- B*    : SMG*Sq B
-- B     : Type ℓ
-- A*    : SMG*Sq A
-- A     : Type ℓ
-- ℓ     : Level
