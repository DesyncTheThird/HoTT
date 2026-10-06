module En.BAut.Base where

open import En.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.HITs.PropositionalTruncation
open import En.Univ.Base

private
  variable
    ℓ : Level

-- automorphism groups and their delooping

Aut : Type ℓ → Type ℓ
Aut T = T ≃ T

Aut∙ : (T : Type ℓ) → Pointed ℓ
Aut∙ T = Aut T , idEquiv T

BAut : Type ℓ → Type (ℓ-suc ℓ)
BAut {ℓ} T = Σ[ X ∈ Type ℓ ] ∥ T ≃ X ∥₁

BAutSub : (T : Type ℓ) → SubUniv ℓ ℓ
BAutSub T = (λ X → ∥ T ≃ X ∥₁) , λ _ → isPropPropTrunc

BAut∙ : (T : Type ℓ) → Pointed (ℓ-suc ℓ)
BAut∙ T = BAut T , T , ∣ idEquiv T ∣₁
