module En.SMG where

open import En.Prelude

record SMG*Struct {ℓ} (El : Type ℓ) : Type ℓ where
  constructor smg*struct
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
open SMG*Struct public

record SMG⋆Functor {ℓ₁ ℓ₂}
  (A : Type ℓ₁) (SMGA : SMG*Struct A)
  (B : Type ℓ₂) (SMGB : SMG*Struct B) : Type (ℓ-max ℓ₁ ℓ₂) where
  constructor smg*functor
  private
    module A = SMG*Struct SMGA
    module B = SMG*Struct SMGB
  field
    f : A → B
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

-- 1. SMG*Struct (FSMG A)
-- 2. for any A, B, SMG*Struct B, exists symmetric-monoidal-functor (FSMG A) B
-- 3. (-) ∙ η : symmetric-monoidal-functor (FSMG A) B → (A → B) is an equivalence
