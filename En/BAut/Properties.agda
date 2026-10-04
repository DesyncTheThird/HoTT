module En.BAut.Properties where

open import En.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as Trunc
open import Cubical.HITs.PropositionalTruncation as PT
open import En.Univ
open import En.BAut.Base

private
  variable
    ℓ : Level

BAutUUniv : (T : Type ℓ) → UUniv (ℓ-suc ℓ) ℓ
BAutUUniv T = SubUUniv {P = λ X → ∥ T ≃ X ∥₁} λ _ → isPropPropTrunc

BAut≡ : {T : Type ℓ} (X Y : BAut T) → (X .fst ≡ Y .fst) ≃ (X ≡ Y)
BAut≡ _ _ = Σ≡PropEquiv λ _ → isPropPropTrunc

ΩBAut≃Aut : (T : Type ℓ) → ⟨ Ω (BAut∙ T) ⟩ ≃ Aut T
ΩBAut≃Aut T = El≡≃ (BAutUUniv T)

isPathConnectedBAut : {T : Type ℓ} (X Y : BAut T) → ∥ X ≡ Y ∥₁
isPathConnectedBAut X Y = PT.map2 (λ e e' → –> (BAut≡ X Y) (ua (e ⁻¹ₑ ∙ₑ e'))) (X .snd) (Y .snd)

isConnectedBAut : (T : Type ℓ) → isConnected 2 (BAut T)
isConnectedBAut T = ∣ pt (BAut∙ T) ∣ₕ , Trunc.elim (λ _ → isOfHLevelSuc 1 (isOfHLevelTrunc 2 _ _))
  λ X → PT.rec (isOfHLevelTrunc 2 _ _) (ap ∣_∣ₕ) (isPathConnectedBAut _ X)

elimPropBAut : {ℓ' : Level} {T : Type ℓ} (P : BAut T → Type ℓ') → (∀ X → isProp (P X))
  → P (pt (BAut∙ T)) → ∀ X → P X
elimPropBAut P isPropP p X = PT.rec (isPropP X) (λ q → tpt P q p) (isPathConnectedBAut _ X)

isOfHLevelBAut : {T : Type ℓ} (n : HLevel) → isOfHLevel n T → isOfHLevel (suc n) (BAut T)
isOfHLevelBAut {T = T} n hT =
  isOfHLevelU (BAutUUniv T) n (elimPropBAut (λ X → isOfHLevel n (X .fst)) (λ _ → isPropIsOfHLevel n) hT)
