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

    ⬠₌ : (W X Y Z : FSMG A)
        → ((W ⊗ X) ⊗ Y) ⊗ Z ≡ W ⊗ (X ⊗ (Y ⊗ Z))
    ⬠₁ : (W X Y Z : FSMG A)
        → Square (sym (α (W ⊗ X) Y Z)) (α W X (Y ⊗ Z)) refl (⬠₌ W X Y Z)
    ⬠₂ : (W X Y Z : FSMG A)
        → Square (ap (_⊗ Z) (α W X Y)) (sym (ap (W ⊗_) (α X Y Z))) (⬠₌ W X Y Z) (α W (X ⊗ Y) Z)

    -- ⬠ : (W X Y Z : FSMG)
    --   → α (W ⊗ X) Y Z ∙ α W X (Y ⊗ Z)
    --   ≡ ap (_⊗ Z) (α W X Y) ∙ α W (X ⊗ Y) Z ∙ ap (W ⊗_) (α X Y Z)

    ▽ : (X Y : FSMG A)
        → Square (ap (X ⊗_) (Λ Y)) (ap (_⊗ Y) (ρ X)) (sym (α X 𝕀 Y)) refl

    -- ▽ : (X Y : FSMG)
    --     → α (X) (𝕀) (Y) ∙ ap (X ⊗_) (Λ (Y)) ≡ ap (_⊗ Y) (ρ (X))

    ⬡₌ : (X Y Z : FSMG A)
        → (X ⊗ Y) ⊗ Z ≡ Y ⊗ (Z ⊗ X)
    ⬡₁ : (X Y Z : FSMG A)
        → Square (sym (α X Y Z)) (α Y Z X) (β X (Y ⊗ Z)) (⬡₌ X Y Z)
    ⬡₂ : (X Y Z : FSMG A)
        → Square (ap (_⊗ Z) (β X Y)) (ap (Y ⊗_) (β Z X)) (⬡₌ X Y Z) (α Y X Z)

    -- ⬡ : (X Y Z : FSMG A)
    --     → α (X) (Y) (Z) ∙ β (X) (Y ⊗ Z) ∙ α (Y) (Z) (X)
    --     ≡ ap (_⊗ Z) (β (X) (Y)) ∙ α (Y) (X) (Z) ∙ ap (Y ⊗_) (β (X) (Z))

    β² : (X Y : FSMG A) → β X Y ≡ sym (β Y X)

module FSMG-elim {ℓ ℓ'} (A : Type ℓ) {P : FSMG A → Type ℓ'}
    (𝕀* : P 𝕀)
    (η* : (a : A) → P (η a))
    (_⊗*_ : {X Y : FSMG A} (X* : P X) → (Y* : P Y) → (P (X ⊗ Y)))

    (α* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → PathP (λ i → P (α X Y Z i)) ((X* ⊗* Y*) ⊗* Z*) (X* ⊗* (Y* ⊗* Z*)))

    (Λ* : {X : FSMG A} (X* : P X) → PathP (λ i → P (Λ X i)) (𝕀* ⊗* X*) X*)
    (ρ* : {X : FSMG A} (X* : P X) → PathP (λ i → P (ρ X i)) (X* ⊗* 𝕀*) X*)
    (β* : {X Y : FSMG A} (X* : P X) (Y* : P Y)
        → PathP (λ i → P (β X Y i)) (X* ⊗* Y*) (Y* ⊗* X*))
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

    (▽* : {X Y : FSMG A} (X* : P X) (Y* : P Y)
        → SquareP (λ i j → P (▽ X Y i j)) (apP (λ i a → X* ⊗* a) (Λ* Y*)) (apP (λ i a → a ⊗* Y*) (ρ* X*)) (symP (α* X* 𝕀* Y*)) refl)

    (⬡₌* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → PathP (λ i → P (⬡₌ X Y Z i)) ((X* ⊗* Y*) ⊗* Z*) (Y* ⊗* (Z* ⊗* X*)))

    (⬡₁* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → SquareP (λ i j → P (⬡₁ X Y Z i j)) (symP (α* X* Y* Z*)) (α* Y* Z* X*) (β* X* (Y* ⊗* Z*)) (⬡₌* X* Y* Z*))
    (⬡₂* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → SquareP (λ i j → P (⬡₂ X Y Z i j)) (apP (λ i a → a ⊗* Z*) (β* X* Y*)) (apP (λ i a → Y* ⊗* a) (β* Z* X*)) (⬡₌* X* Y* Z*) (α* Y* X* Z*))

    (β²* : {X Y : FSMG A} (X* : P X) (Y* : P Y) → SquareP (λ i j → P (β² X Y i j)) (β* X* Y*) (symP (β* Y* X*)) refl refl)

    where
    elim : (xs : FSMG A) → P xs
    elim 𝕀 = 𝕀*
    elim (η x) = η* x
    elim (X ⊗ Y) = elim X ⊗* elim Y
    elim (α X Y Z i) = α* (elim X) (elim Y) (elim Z) i
    elim (Λ X i) = Λ* (elim X) i
    elim (ρ X i) = ρ* (elim X) i
    elim (β X Y i) = β* (elim X) (elim Y) i
    elim (⬠₌ W X Y Z i) = ⬠₌* (elim W) (elim X) (elim Y) (elim Z) i
    elim (⬠₁ W X Y Z i j) = ⬠₁* (elim W) (elim X) (elim Y) (elim Z) i j
    elim (⬠₂ W X Y Z i j) = ⬠₂* (elim W) (elim X) (elim Y) (elim Z) i j
    elim (▽ X Y i j) = ▽* (elim X) (elim Y) i j
    elim (⬡₌ X Y Z i) = ⬡₌* (elim X) (elim Y) (elim Z) i
    elim (⬡₁ X Y Z i j) = ⬡₁* (elim X) (elim Y) (elim Z) i j
    elim (⬡₂ X Y Z i j) = ⬡₂* (elim X) (elim Y) (elim Z) i j
    elim (β² X Y i j) = β²* (elim X) (elim Y) i j

-- ▽-FSMG : {A : Type ℓ} (W X Y Z : FSMG A)
--     → α (X) (𝕀) (Y) ∙ ap (X ⊗_) (Λ (Y)) ≡ ap (_⊗ Y) (ρ (X))
-- ▽-FSMG W X Y Z = sorry

-- ⬠-FSMG : {A : Type ℓ} (W X Y Z : FSMG A)
--     → α (W ⊗ X) Y Z ∙ α W X (Y ⊗ Z)
--     ≡ ap (_⊗ Z) (α W X Y) ∙ α W (X ⊗ Y) Z ∙ ap (W ⊗_) (α X Y Z)
-- ⬠-FSMG W X Y Z = sorry

-- ⬡-FSMG : {A : Type ℓ} (X Y Z : FSMG A)
--         → α (X) (Y) (Z) ∙ β (X) (Y ⊗ Z) ∙ α (Y) (Z) (X)
--         ≡ ap (_⊗ Z) (β (X) (Y)) ∙ α (Y) (X) (Z) ∙ ap (Y ⊗_) (β (X) (Z))
-- ⬡-FSMG X Y Z = sorry

-- recFSMG : (P : FSMG A → Type ℓ)
--     (η* : (a : A) → P (η a))
--     (𝕀* : P 𝕀)
--     (_⊗*_ : {X Y : FSMG A} → (X* : P X) → (Y* : P Y) → P (X ⊗ Y))
--     (α* : {X Y Z : FSMG A} → (X* : P X) (Y* : P Y) (Z* : P Z)
--         → ((X* ⊗* Y*) ⊗* Z*) ≡ (X* ⊗* (Y* ⊗* Z*)) [ P ↓ α X Y Z ])
--     (Λ* : {X : FSMG A} (X* : P X) → (𝕀* ⊗* X*) ≡ X* [ P ↓ Λ X ])
--     (ρ* : {X : FSMG A} (X* : P X) → (X* ⊗* 𝕀*) ≡ X* [ P ↓ ρ X ])
--     (β* : {X Y : FSMG A} (X* : P X) (Y* : P Y) → (X* ⊗* Y*) ≡ (Y* ⊗* X*) [ P ↓ β X Y ])
--     (▽* : {X Y : FSMG A} (X* : P X) (Y* : P Y)
--         → let p1 = (α* {X} {𝕀} {Y} X* 𝕀* Y* ∙ᵈ $ (X* ⊗*_) (Λ* {Y} Y*)) in
--         let p2 = $ (_⊗* Y*) (ρ* {X} X*) in
--         p1 ≡ p2 [ (λ p → ((X* ⊗* 𝕀*) ⊗* Y*) ≡ (X* ⊗* Y*) [ P ↓ p ]) ↓ ▽ X Y ])
--     (⬠* : {W X Y Z : FSMG A} (W* : P W) (X* : P X) (Y* : P Y) (Z* : P Z)
--         → let p1 = α* {W ⊗ X} {Y} {Z} (W* ⊗* X*) Y* Z* ∙ᵈ α* {W} {X} {Y ⊗ Z} W* X* (Y* ⊗* Z*) in
--         let p2 = $ (_⊗* Z*) (α* {W} {X} {Y} W* X* Y*) ∙ᵈ (α* {W} {X ⊗ Y} {Z} W* (X* ⊗* Y*) Z* ∙ᵈ $ (W* ⊗*_) (α* {X} {Y} {Z} X* Y* Z*)) in
--         p1 ≡ p2 [ (λ p → (((W* ⊗* X*) ⊗* Y*) ⊗* Z*) ≡ (W* ⊗* ((X* ⊗* (Y* ⊗* Z*)))) [ P ↓ p ]) ↓ ⬠ W X Y Z ])
--     (⬡* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
--         → let p1 = α* {X} {Y} {Z} X* Y* Z* ∙ᵈ (β* {X} {Y ⊗ Z} X* (Y* ⊗* Z*) ∙ᵈ α* {Y} {Z} {X} Y* Z* X*) in
--             let p2 = $ (_⊗* Z*) (β* {X} {Y} X* Y*) ∙ᵈ (α* {Y} {X} {Z} Y* X* Z* ∙ᵈ $ (Y* ⊗*_) (β* {X} {Z} X* Z*)) in
--             p1 ≡ p2 [ (λ p → ((X* ⊗* Y*) ⊗* Z*) ≡ (Y* ⊗* (Z* ⊗* X*)) [ P ↓ p ]) ↓ ⬡ X Y Z ])
--     (β²* : {X Y : FSMG A} (X* : P X) (Y* : P Y)
--         → (β* {X} {Y} X* Y* ∙ᵈ β* {Y} {X} Y* X*) ≡ refl [ (λ p → (X* ⊗* Y*) ≡ (X* ⊗* Y*) [ P ↓ p ]) ↓ β² X Y ])
--     → (f : (X : FSMG A) → P X)
