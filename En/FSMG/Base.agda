module En.FSMG.Base where

open import En.Prelude

data FSMG {ℓ} (A : Type ℓ) : Type ℓ where
    𝕀 : FSMG A
    η : A → FSMG A
    _⊗_ : FSMG A → FSMG A → FSMG A

    α : (X Y Z : FSMG A) → (X ⊗ Y) ⊗ Z ≡ X ⊗ (Y ⊗ Z)
    Λ : (X : FSMG A) → 𝕀 ⊗ X ≡ X
    ρ : (X : FSMG A) → X ⊗ 𝕀 ≡ X
    β : (X Y : FSMG A) → X ⊗ Y ≡ Y ⊗ X

    ▽ : (X Y : FSMG A)
        → Square (ap (X ⊗_) (Λ Y)) (ap (_⊗ Y) (ρ X)) (sym (α X 𝕀 Y)) refl

    -- ▽ : (X Y : FSMG)
    --     → α (X) (𝕀) (Y) ∙ ap (X ⊗_) (Λ (Y)) ≡ ap (_⊗ Y) (ρ (X))

    ⬠₌ : (W X Y Z : FSMG A)
        → ((W ⊗ X) ⊗ Y) ⊗ Z ≡ W ⊗ (X ⊗ (Y ⊗ Z))
    ⬠₁ : (W X Y Z : FSMG A)
        → Square (sym (α (W ⊗ X) Y Z)) (α W X (Y ⊗ Z)) refl (⬠₌ W X Y Z)
    ⬠₂ : (W X Y Z : FSMG A)
        → Square (ap (_⊗ Z) (α W X Y)) (sym (ap (W ⊗_) (α X Y Z))) (⬠₌ W X Y Z) (α W (X ⊗ Y) Z)

    -- ⬠ : (W X Y Z : FSMG)
    --   → α (W ⊗ X) Y Z ∙ α W X (Y ⊗ Z)
    --   ≡ ap (_⊗ Z) (α W X Y) ∙ α W (X ⊗ Y) Z ∙ ap (W ⊗_) (α X Y Z)


    ⬡₌ : (X Y Z : FSMG A)
        → (X ⊗ Y) ⊗ Z ≡ Y ⊗ (Z ⊗ X)
    ⬡₁ : (X Y Z : FSMG A)
        → Square (sym (α X Y Z)) (α Y Z X) (β X (Y ⊗ Z)) (⬡₌ X Y Z)
    ⬡₂ : (X Y Z : FSMG A)
        → Square (ap (_⊗ Z) (β X Y)) (ap (Y ⊗_) (sym (β X Z))) (⬡₌ X Y Z) (α Y X Z)

    -- ⬡ : (X Y Z : FSMG A)
    --     → α (X) (Y) (Z) ∙ β (X) (Y ⊗ Z) ∙ α (Y) (Z) (X)
    --     ≡ ap (_⊗ Z) (β (X) (Y)) ∙ α (Y) (X) (Z) ∙ ap (Y ⊗_) (β (X) (Z))

    β² : (X Y : FSMG A) → β X Y ≡ sym (β Y X)

    is-groupoid : isGroupoid (FSMG A)

module FSMG*Elim {ℓ ℓ'} (A : Type ℓ) {P : FSMG A → Type ℓ'}
    (η* : (a : A) → P (η a))
    (𝕀* : P 𝕀)
    (_⊗*_ : {X Y : FSMG A} (X* : P X) → (Y* : P Y) → (P (X ⊗ Y)))

    (α* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → PathP (λ i → P (α X Y Z i)) ((X* ⊗* Y*) ⊗* Z*) (X* ⊗* (Y* ⊗* Z*)))

    (Λ* : {X : FSMG A} (X* : P X) → PathP (λ i → P (Λ X i)) (𝕀* ⊗* X*) X*)
    (ρ* : {X : FSMG A} (X* : P X) → PathP (λ i → P (ρ X i)) (X* ⊗* 𝕀*) X*)
    (β* : {X Y : FSMG A} (X* : P X) (Y* : P Y)
        → PathP (λ i → P (β X Y i)) (X* ⊗* Y*) (Y* ⊗* X*))

    (▽* : {X Y : FSMG A} (X* : P X) (Y* : P Y)
        → SquareP (λ i j → P (▽ X Y i j)) (apP (λ i a → X* ⊗* a) (Λ* Y*)) (apP (λ i a → a ⊗* Y*) (ρ* X*)) (symP (α* X* 𝕀* Y*)) refl)

    (⬠₌* : {W X Y Z : FSMG A} (W* : P W) (X* : P X) (Y* : P Y) (Z* : P Z)
        → PathP (λ i → P (⬠₌ W X Y Z i)) (((W* ⊗* X*) ⊗* Y*) ⊗* Z*) (W* ⊗* (X* ⊗* (Y* ⊗* Z*))))
    (⬠₁* : {W X Y Z : FSMG A} (W* : P W) (X* : P X) (Y* : P Y) (Z* : P Z)
        → SquareP (λ i j → P (⬠₁ W X Y Z i j))
            (symP (α* (W* ⊗* X*) Y* Z*))
            (α* W* X* (Y* ⊗* Z*))
            refl
            (⬠₌* W* X* Y* Z*))
    (⬠₂* : {W X Y Z : FSMG A} (W* : P W) (X* : P X) (Y* : P Y) (Z* : P Z)
        → SquareP (λ i j → P (⬠₂ W X Y Z i j))
            (apP (λ i a → a ⊗* Z*) (α* W* X* Y*))
            (symP (apP (λ i a → W* ⊗* a) (α* X* Y* Z*)))
            (⬠₌* W* X* Y* Z*)
            (α* W* (X* ⊗* Y*) Z*))

    (⬡₌* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → PathP (λ i → P (⬡₌ X Y Z i)) ((X* ⊗* Y*) ⊗* Z*) (Y* ⊗* (Z* ⊗* X*)))

    (⬡₁* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → SquareP (λ i j → P (⬡₁ X Y Z i j)) (symP (α* X* Y* Z*)) (α* Y* Z* X*) (β* X* (Y* ⊗* Z*)) (⬡₌* X* Y* Z*))
    (⬡₂* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → SquareP (λ i j → P (⬡₂ X Y Z i j)) (apP (λ i a → a ⊗* Z*) (β* X* Y*)) (apP (λ i a → Y* ⊗* a) (symP (β* X* Z*))) (⬡₌* X* Y* Z*) (α* Y* X* Z*))

    (β²* : {X Y : FSMG A} (X* : P X) (Y* : P Y) → SquareP (λ i j → P (β² X Y i j)) (β* X* Y*) (symP (β* Y* X*)) refl refl)

    (is-groupoid* : (X : FSMG A) → isGroupoid (P X))

    where
    f : (xs : FSMG A) → P xs
    f 𝕀 = 𝕀*
    f (η x) = η* x
    f (X ⊗ Y) = f X ⊗* f Y
    f (α X Y Z i) = α* (f X) (f Y) (f Z) i
    f (Λ X i) = Λ* (f X) i
    f (ρ X i) = ρ* (f X) i
    f (β X Y i) = β* (f X) (f Y) i
    f (▽ X Y i j) = ▽* (f X) (f Y) i j
    f (⬠₌ W X Y Z i) = ⬠₌* (f W) (f X) (f Y) (f Z) i
    f (⬠₁ W X Y Z i j) = ⬠₁* (f W) (f X) (f Y) (f Z) i j
    f (⬠₂ W X Y Z i j) = ⬠₂* (f W) (f X) (f Y) (f Z) i j
    f (⬡₌ X Y Z i) = ⬡₌* (f X) (f Y) (f Z) i
    f (⬡₁ X Y Z i j) = ⬡₁* (f X) (f Y) (f Z) i j
    f (⬡₂ X Y Z i j) = ⬡₂* (f X) (f Y) (f Z) i j
    f (β² X Y i j) = β²* (f X) (f Y) i j
    f (is-groupoid X Y p q r s i j k) = isGroupoid→CubeP (λ i j k → P (is-groupoid X Y p q r s i j k))
        (λ j k → f (r j k)) (λ j k → f (s j k)) (λ i k → f (p k)) (λ i k → f (q k)) (λ i j → f X) (λ i j → f Y) (is-groupoid* Y) i j k

module FSMG*Rec {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'}
    (η* : (a : A) → B)
    (𝕀* : B)
    (_⊗*_ : B → B → B)

    (α* : (X* Y* Z* : B) → (X* ⊗* Y*) ⊗* Z* ≡ X* ⊗* (Y* ⊗* Z*))

    (Λ* : (X* : B) → 𝕀* ⊗* X* ≡ X*)
    (ρ* : (X* : B) → X* ⊗* 𝕀* ≡ X*)
    (β* : (X* Y* : B) → X* ⊗* Y* ≡ Y* ⊗* X*)

    (▽* : (X* Y* : B)
        → Square (ap (X* ⊗*_) (Λ* Y*)) (ap (_⊗* Y*) (ρ* X*)) (sym (α* X* 𝕀* Y*)) refl)

    (⬠₌* : (W* X* Y* Z* : B)
        → ((W* ⊗* X*) ⊗* Y*) ⊗* Z* ≡ W* ⊗* (X* ⊗* (Y* ⊗* Z*)))
    (⬠₁* : (W* X* Y* Z* : B)
        → Square (sym (α* (W* ⊗* X*) Y* Z*)) (α* W* X* (Y* ⊗* Z*)) refl (⬠₌* W* X* Y* Z*))
    (⬠₂* : (W* X* Y* Z* : B)
        → Square (ap (_⊗* Z*) (α* W* X* Y*)) (sym (ap (W* ⊗*_) (α* X* Y* Z*))) (⬠₌* W* X* Y* Z*) (α* W* (X* ⊗* Y*) Z*))

    (⬡₌* : (X* Y* Z* : B)
        → (X* ⊗* Y*) ⊗* Z* ≡ Y* ⊗* (Z* ⊗* X*))
    (⬡₁* : (X* Y* Z* : B)
        → Square (sym (α* X* Y* Z*)) (α* Y* Z* X*) (β* X* (Y* ⊗* Z*)) (⬡₌* X* Y* Z*))
    (⬡₂* : (X* Y* Z* : B)
        → Square (ap (_⊗* Z*) (β* X* Y*)) (ap (Y* ⊗*_) (sym (β* X* Z*))) (⬡₌* X* Y* Z*) (α* Y* X* Z*))

    (β²* : (X* Y* : B) → Square (β* X* Y*) (sym (β* Y* X*)) refl refl)

    (is-groupoid* : isGroupoid B)

    where

    module Elim = FSMG*Elim A {P = λ _ → B}
        η* 𝕀* (λ x y → x ⊗* y) α* Λ* ρ* β* ▽* ⬠₌* ⬠₁* ⬠₂* ⬡₌* ⬡₁* ⬡₂* β²*
        (λ _ → is-groupoid*)

    f : FSMG A → B
    f = Elim.f
