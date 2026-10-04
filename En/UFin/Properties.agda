module En.UFin.Properties where

open import En.Prelude
open SumFin
open import Cubical.Foundations.Pointed
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.Fin.LehmerCode
open import En.Univ
open import En.BAut
open import En.UFin.Base
import En.SMG as S hiding ( SMG* ; SMG*Fun )

isGroupoidUFin : isGroupoid UFin
isGroupoidUFin = isGroupoidFinSet

UFinUUniv : UUniv (ℓ-suc ℓ-zero) ℓ-zero
UFinUUniv = SubUUniv {P = isFinSet} λ _ → isPropIsFinSet

-- cardinality

UFin≃ΣBAut : UFin ≃ (Σ[ n ∈ ℕ ] BAut (Fin n))
UFin≃ΣBAut = isoToEquiv i
  where
    open Iso
    i : Iso UFin (Σ[ n ∈ ℕ ] BAut (Fin n))
    i .fun (X , n , t) = n , X , PT.map invEquiv t
    i .inv (n , X , t) = X , n , PT.map invEquiv t
    i .sec (n , X , t) j = n , X , squash₁ (PT.map invEquiv (PT.map invEquiv t)) t j
    i .ret (X , n , t) j = X , n , squash₁ (PT.map invEquiv (PT.map invEquiv t)) t j

Fin≃→≡ : {m n : ℕ} → Fin m ≃ Fin n → m ≡ n
Fin≃→≡ e = cardEquiv (FinU _) (FinU _) ∣ e ∣₁

ΩUFin≃Aut : (n : ℕ) → ⟨ Ω (UFin∙ n) ⟩ ≃ Aut (Fin n)
ΩUFin≃Aut n = El≡≃ UFinUUniv

ΩUFin≃LehmerCode : (n : ℕ) → ⟨ Ω (UFin∙ n) ⟩ ≃ LehmerCode n
ΩUFin≃LehmerCode n =
  ΩUFin≃Aut n ∙ₑ equivComp (SumFin≃Fin n) (SumFin≃Fin n) ∙ₑ lehmerEquiv

isContrAutFin0 : isContr (Aut (Fin 0))
isContrAutFin0 = idEquiv _ , λ e → equivEq (funExt λ ())

module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} where

  ×-distribˡ≃ : A × (B ⊎ C) ≃ (A × B) ⊎ (A × C)
  ×-distribˡ≃ = isoToEquiv ×DistR⊎Iso

  ×-distribʳ≃ : (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
  ×-distribʳ≃ = isoToEquiv i
    where
      open Iso
      i : Iso ((A ⊎ B) × C) ((A × C) ⊎ (B × C))
      i .fun (inl a , c) = inl (a , c)
      i .fun (inr b , c) = inr (b , c)
      i .inv (inl (a , c)) = inl a , c
      i .inv (inr (b , c)) = inr b , c
      i .sec (inl _) = refl
      i .sec (inr _) = refl
      i .ret (inl _ , _) = refl
      i .ret (inr _ , _) = refl

module _ {ℓ ℓ'} {A : Type ℓ} where

  ×-unitˡ≃ : Unit* {ℓ'} × A ≃ A
  ×-unitˡ≃ = isoToEquiv lUnit*×Iso

  ×-unitʳ≃ : A × Unit* {ℓ'} ≃ A
  ×-unitʳ≃ = isoToEquiv rUnit*×Iso

  ×-zeroˡ≃ : ⊥* {ℓ'} × A ≃ ⊥* {ℓ'}
  ×-zeroˡ≃ = uninhabEquiv (λ ()) (λ ())

  ×-zeroʳ≃ : A × ⊥* {ℓ'} ≃ ⊥* {ℓ'}
  ×-zeroʳ≃ = uninhabEquiv (λ ()) (λ ())

-- rig laws

module _ (X Y Z : UFin) where

  private
    uaU = uaEl UFinUUniv

  +ᶠ-assoc : (X +ᶠ Y) +ᶠ Z ≡ X +ᶠ (Y +ᶠ Z)
  +ᶠ-assoc = uaU ⊎-assoc-≃

  ×ᶠ-assoc : (X ×ᶠ Y) ×ᶠ Z ≡ X ×ᶠ (Y ×ᶠ Z)
  ×ᶠ-assoc = uaU Σ-assoc-≃

  ×ᶠ-distribˡ : X ×ᶠ (Y +ᶠ Z) ≡ (X ×ᶠ Y) +ᶠ (X ×ᶠ Z)
  ×ᶠ-distribˡ = uaU ×-distribˡ≃

  ×ᶠ-distribʳ : (X +ᶠ Y) ×ᶠ Z ≡ (X ×ᶠ Z) +ᶠ (Y ×ᶠ Z)
  ×ᶠ-distribʳ = uaU ×-distribʳ≃

module _ (X : UFin) where

  private
    uaU = uaEl UFinUUniv

  +ᶠ-unitˡ : 𝟘 +ᶠ X ≡ X
  +ᶠ-unitˡ = uaU ⊎-IdL-⊥*-≃

  +ᶠ-unitʳ : X +ᶠ 𝟘 ≡ X
  +ᶠ-unitʳ = uaU ⊎-IdR-⊥*-≃

  ×ᶠ-unitˡ : 𝟙 ×ᶠ X ≡ X
  ×ᶠ-unitˡ = uaU ×-unitˡ≃

  ×ᶠ-unitʳ : X ×ᶠ 𝟙 ≡ X
  ×ᶠ-unitʳ = uaU ×-unitʳ≃

  ×ᶠ-zeroˡ : 𝟘 ×ᶠ X ≡ 𝟘
  ×ᶠ-zeroˡ = uaU ×-zeroˡ≃

  ×ᶠ-zeroʳ : X ×ᶠ 𝟘 ≡ 𝟘
  ×ᶠ-zeroʳ = uaU ×-zeroʳ≃

+ᶠ-comm : (X Y : UFin) → X +ᶠ Y ≡ Y +ᶠ X
+ᶠ-comm _ _ = uaEl UFinUUniv ⊎-swap-≃

×ᶠ-comm : (X Y : UFin) → X ×ᶠ Y ≡ Y ×ᶠ X
×ᶠ-comm _ _ = uaEl UFinUUniv Σ-swap-≃

-- additive and multiplicative symmetric monoidal structures

UFin+* : S.SMG*Sq UFin
UFin+* = UUnivSMG.UUniv* UFinUUniv isGroupoidUFin 𝟘 _+ᶠ_ ⊎-equiv
  (λ _ _ → equivEq (⊎-η refl refl))
  (λ _ _ _ → ⊎-assoc-≃) (λ _ → ⊎-IdL-⊥*-≃) (λ _ → ⊎-IdR-⊥*-≃) (λ _ _ → ⊎-swap-≃)
  (λ _ _ → equivEq (⊎-η (⊎-η refl ⊥*-η) refl))
  (λ _ _ _ _ → equivEq (⊎-η (⊎-η (⊎-η refl refl) refl) refl))
  (λ _ _ _ → equivEq (⊎-η (⊎-η refl refl) refl))
  (λ _ _ → equivEq (⊎-η refl refl))

UFin×* : S.SMG*Sq UFin
UFin×* = UUnivSMG.UUniv* UFinUUniv isGroupoidUFin 𝟙 _×ᶠ_ ≃-×
  (λ _ _ → equivEq (funExt λ _ → refl))
  (λ _ _ _ → Σ-assoc-≃) (λ _ → ×-unitˡ≃) (λ _ → ×-unitʳ≃) (λ _ _ → Σ-swap-≃)
  (λ _ _ → equivEq refl)
  (λ _ _ _ _ → equivEq refl)
  (λ _ _ _ → equivEq refl)
  (λ _ _ → equivEq refl)
