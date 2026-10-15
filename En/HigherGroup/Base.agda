module En.HigherGroup.Base where

open import En.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.Data.Unit
open import Cubical.HITs.Truncation as Trunc using ( ∣_∣ₕ ; isOfHLevelTrunc )
open import En.BAut

-- higher groups as pointed connected types

record ∞Group (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor ∞group
  field
    B : Type ℓ
    sh : B
    isConnectedB : isConnected 2 B

  B∙ : Pointed ℓ
  B∙ = B , sh

open ∞Group public

Ωᵍ : ∞Group ℓ → Type ℓ
Ωᵍ G = ⟨ Ω (B∙ G) ⟩

∞GroupHom : ∞Group ℓ → ∞Group ℓ' → Type (ℓ-max ℓ ℓ')
∞GroupHom G H = B∙ G →∙ B∙ H

∞GroupEquiv : ∞Group ℓ → ∞Group ℓ' → Type (ℓ-max ℓ ℓ')
∞GroupEquiv G H = B∙ G ≃∙ B∙ H

-- concrete groups are 1-truncated higher groups

ConcreteGroup : (ℓ : Level) → Type (ℓ-suc ℓ)
ConcreteGroup ℓ = Σ[ G ∈ ∞Group ℓ ] isGroupoid (G .B)

Unit∞Group : ∞Group ℓ-zero
Unit∞Group .B = Unit
Unit∞Group .sh = tt
Unit∞Group .isConnectedB = ∣ tt ∣ₕ , Trunc.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _) λ _ → refl

UnitConcreteGroup : ConcreteGroup ℓ-zero
UnitConcreteGroup = Unit∞Group , isOfHLevelUnit 3

BAutGroup : (T : Type ℓ) → ∞Group (ℓ-suc ℓ)
BAutGroup T .B = BAut T
BAutGroup T .sh = pt (BAut∙ T)
BAutGroup T .isConnectedB = isConnectedBAut T

BAutConcrete : (T : Type ℓ) → isSet T → ConcreteGroup (ℓ-suc ℓ)
BAutConcrete T isSetT = BAutGroup T , isOfHLevelBAut 2 isSetT

ElBAut : {T : Type ℓ} → BAut T → Type ℓ
ElBAut = fst

-- actions

∞Action : ∞Group ℓ → (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
∞Action G ℓ' = G .B → Type ℓ'

ActionType : {B : Type ℓ} → (B → Type ℓ') → Type (ℓ-max ℓ ℓ')
ActionType X = Σ _ X

restrict : (G : ∞Group ℓ) (H : ∞Group ℓ') → ∞GroupHom G H → ∞Action H ℓ'' → ∞Action G ℓ''
restrict G H f X = X ∘ f .fst

-- wreath products

infix 25 _≀_

_≀_ : (A : Type ℓ'') {B : Type ℓ} → (B → Type ℓ') → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
A ≀ X = Σ[ b ∈ _ ] (X b → A)
