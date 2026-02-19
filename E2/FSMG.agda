{-# OPTIONS --cubical --safe --guardedness #-}

open import Cubical.Foundations.Prelude renaming (congS to ap ; cong to apd ; subst to tpt)
open import Cubical.Foundations.HLevels

module FSMG {ℓ} (A : Type ℓ) (is-groupoid : isGroupoid A) where

postulate
  sorry : ∀ {P} → P

data FSMG : Type ℓ where
    𝕀 : FSMG
    η : A → FSMG
    _⊗_ : FSMG → FSMG → FSMG

    α : (X Y Z : FSMG) → (X ⊗ Y) ⊗ Z ≡ X ⊗ (Y ⊗ Z)
    Λ : (X : FSMG) → 𝕀 ⊗ X ≡ X
    ρ : (X : FSMG) → X ⊗ 𝕀 ≡ X
    β : (X Y : FSMG) → X ⊗ Y ≡ Y ⊗ X

    ⬠₌ : (W X Y Z : FSMG)
        → ((W ⊗ X) ⊗ Y) ⊗ Z ≡ W ⊗ (X ⊗ (Y ⊗ Z))
    ⬠₁ : (W X Y Z : FSMG)
        → Square (sym (α (W ⊗ X) Y Z)) (α W X (Y ⊗ Z)) refl (⬠₌ W X Y Z)
    ⬠₂ : (W X Y Z : FSMG)
        → Square (ap (_⊗ Z) (α W X Y)) (sym (ap (W ⊗_) (α X Y Z))) (⬠₌ W X Y Z) (α W (X ⊗ Y) Z)

    -- ⬠ : (W X Y Z : FSMG)
    --   → α (W ⊗ X) Y Z ∙ α W X (Y ⊗ Z)
    --   ≡ ap (_⊗ Z) (α W X Y) ∙ α W (X ⊗ Y) Z ∙ ap (W ⊗_) (α X Y Z)

    ▽ : (X Y : FSMG)
        → α (X) (𝕀) (Y) ∙ ap (X ⊗_) (Λ (Y))
        ≡ ap (_⊗ Y) (ρ (X))

    ⬡₌ : (X Y Z : FSMG)
        → (X ⊗ Y) ⊗ Z ≡ Y ⊗ (Z ⊗ X)
    ⬡₁ : (X Y Z : FSMG)
        → Square (sym (α X Y Z)) (α Y Z X) (β X (Y ⊗ Z)) (⬡₌ X Y Z)
    ⬡₂ : (X Y Z : FSMG)
        → Square (ap (_⊗ Z) (β X Y)) (ap (Y ⊗_) (β Z X)) (⬡₌ X Y Z) (α Y X Z)

    -- ⬡ : (X Y Z : FSMG)
    --     → α (X) (Y) (Z) ∙ β (X) (Y ⊗ Z) ∙ α (Y) (Z) (X)
    --     ≡ ap (_⊗ Z) (β (X) (Y)) ∙ α (Y) (X) (Z) ∙ ap (Y ⊗_) (β (X) (Z))

    β² : (X Y : FSMG) → β X Y ∙ β Y X ≡ refl {_} {_} {X ⊗ Y}

⬠-FSMG : (W X Y Z : FSMG)
    → α (W ⊗ X) Y Z ∙ α W X (Y ⊗ Z)
    ≡ ap (_⊗ Z) (α W X Y) ∙ α W (X ⊗ Y) Z ∙ ap (W ⊗_) (α X Y Z)
⬠-FSMG W X Y Z = sorry

⬡-FSMG : (X Y Z : FSMG)
        → α (X) (Y) (Z) ∙ β (X) (Y ⊗ Z) ∙ α (Y) (Z) (X)
        ≡ ap (_⊗ Z) (β (X) (Y)) ∙ α (Y) (X) (Z) ∙ ap (Y ⊗_) (β (X) (Z))
⬡-FSMG X Y Z = sorry

-- recFSMG : (P : FSMG → Type ℓ)
--     (η* : (a : A) → P (η a))
--     (𝕀* : P 𝕀)
--     (_⊗*_ : {X Y : FSMG} → (X* : P X) → (Y* : P Y) → P (X ⊗ Y))
--     (α* : {X Y Z : FSMG} → (X* : P X) (Y* : P Y) (Z* : P Z)
--         → ((X* ⊗* Y*) ⊗* Z*) ≡ (X* ⊗* (Y* ⊗* Z*)) [ P ↓ α X Y Z ])
--     (Λ* : {X : FSMG} (X* : P X) → (𝕀* ⊗* X*) ≡ X* [ P ↓ Λ X ])
--     (ρ* : {X : FSMG} (X* : P X) → (X* ⊗* 𝕀*) ≡ X* [ P ↓ ρ X ])
--     (β* : {X Y : FSMG} (X* : P X) (Y* : P Y) → (X* ⊗* Y*) ≡ (Y* ⊗* X*) [ P ↓ β X Y ])
--     (▽* : {X Y : FSMG} (X* : P X) (Y* : P Y)
--         → let p1 = (α* {X} {𝕀} {Y} X* 𝕀* Y* ∙ᵈ $ (X* ⊗*_) (Λ* {Y} Y*)) in
--         let p2 = $ (_⊗* Y*) (ρ* {X} X*) in
--         p1 ≡ p2 [ (λ p → ((X* ⊗* 𝕀*) ⊗* Y*) ≡ (X* ⊗* Y*) [ P ↓ p ]) ↓ ▽ X Y ])
--     (⬠* : {W X Y Z : FSMG} (W* : P W) (X* : P X) (Y* : P Y) (Z* : P Z)
--         → let p1 = α* {W ⊗ X} {Y} {Z} (W* ⊗* X*) Y* Z* ∙ᵈ α* {W} {X} {Y ⊗ Z} W* X* (Y* ⊗* Z*) in
--         let p2 = $ (_⊗* Z*) (α* {W} {X} {Y} W* X* Y*) ∙ᵈ (α* {W} {X ⊗ Y} {Z} W* (X* ⊗* Y*) Z* ∙ᵈ $ (W* ⊗*_) (α* {X} {Y} {Z} X* Y* Z*)) in
--         p1 ≡ p2 [ (λ p → (((W* ⊗* X*) ⊗* Y*) ⊗* Z*) ≡ (W* ⊗* ((X* ⊗* (Y* ⊗* Z*)))) [ P ↓ p ]) ↓ ⬠ W X Y Z ])
--     (⬡* : {X Y Z : FSMG} (X* : P X) (Y* : P Y) (Z* : P Z)
--         → let p1 = α* {X} {Y} {Z} X* Y* Z* ∙ᵈ (β* {X} {Y ⊗ Z} X* (Y* ⊗* Z*) ∙ᵈ α* {Y} {Z} {X} Y* Z* X*) in
--             let p2 = $ (_⊗* Z*) (β* {X} {Y} X* Y*) ∙ᵈ (α* {Y} {X} {Z} Y* X* Z* ∙ᵈ $ (Y* ⊗*_) (β* {X} {Z} X* Z*)) in
--             p1 ≡ p2 [ (λ p → ((X* ⊗* Y*) ⊗* Z*) ≡ (Y* ⊗* (Z* ⊗* X*)) [ P ↓ p ]) ↓ ⬡ X Y Z ])
--     (β²* : {X Y : FSMG} (X* : P X) (Y* : P Y)
--         → (β* {X} {Y} X* Y* ∙ᵈ β* {Y} {X} Y* X*) ≡ refl [ (λ p → (X* ⊗* Y*) ≡ (X* ⊗* Y*) [ P ↓ p ]) ↓ β² X Y ])
--     → (f : (X : FSMG A) → P X)

