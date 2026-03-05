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

record SMG*Functor {ℓ₁ ℓ₂}
  (A : Type ℓ₁) (SMGA : SMG*Struct A)
  (B : Type ℓ₂) (SMGB : SMG*Struct B)
  (f : A → B) : Type (ℓ-max ℓ₁ ℓ₂) where
  constructor smg*functor
  private
    module A = SMG*Struct SMGA
    module B = SMG*Struct SMGB
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

open SMG*Functor public

record SMG*Struct*Square {ℓ} (El : Type ℓ) : Type ℓ where
  constructor smg*struct*square
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

open SMG*Struct*Square public

record SMG*Functor*Square {ℓ₁ ℓ₂}
  (A : Type ℓ₁) (SMGA : SMG*Struct*Square A)
  (B : Type ℓ₂) (SMGB : SMG*Struct*Square B)
  (f : A → B) : Type (ℓ-max ℓ₁ ℓ₂) where
  constructor smg*functor*square
  private
    module A = SMG*Struct*Square SMGA
    module B = SMG*Struct*Square SMGB
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

open SMG*Functor*Square public

-- 1. SMG*Struct (El)
-- 2. for any A, B, SMG*Struct B, exists symmetric-monoidal-functor (El) B
-- 3. (-) ∙ η : symmetric-monoidal-functor (El) B → (A → B) is an equivalence
