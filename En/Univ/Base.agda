module En.Univ.Base where

open import En.Prelude
open import Cubical.Foundations.Univalence

-- Tarski universes

record Univ ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor univ
  field
    U : Type ℓ
    El : U → Type ℓ'

open Univ public

isUUniv : ∀ {ℓ ℓ'} → Univ ℓ ℓ' → Type (ℓ-max ℓ ℓ')
isUUniv 𝒰 = (X Y : 𝒰 .U) → isEquiv (λ (p : X ≡ Y) → pathToEquiv (ap (𝒰 .El) p))

-- univalent universes

UUniv : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
UUniv ℓ ℓ' = Σ (Univ ℓ ℓ') isUUniv
