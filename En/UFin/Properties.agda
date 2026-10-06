module En.UFin.Properties where

open import En.Prelude
open SumFin
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.Fin.LehmerCode
open import Cubical.Data.Empty.Properties
open import Cubical.Foundations.Equiv.Properties
import Cubical.Data.FinSet.Induction as FS
open import Cubical.HITs.Truncation as Trunc
open import En.Univ
open import En.BAut
open import En.UFin.Base
import En.SMG as S hiding ( SMG* ; SMG*Fun )

isGroupoidUFin : isGroupoid UFin
isGroupoidUFin = isGroupoidFinSet

UFinUUniv : UUniv (ℓ-suc ℓ-zero) ℓ-zero
UFinUUniv = SubUUniv UFinSub

-- cardinality

UFin≃ΣBAut : UFin ≃ (Σ[ n ∈ ℕ ] BAut (Fin n))
UFin≃ΣBAut = isoToEquiv i
  where
    open Iso
    i : Iso UFin (Σ[ n ∈ ℕ ] BAut (Fin n))
    i .fun (X , n , t) = n , X , PT.map _⁻¹ₑ t
    i .inv (n , X , t) = X , n , PT.map _⁻¹ₑ t
    i .sec (n , X , t) j = n , X , squash₁ (PT.map _⁻¹ₑ (PT.map _⁻¹ₑ t)) t j
    i .ret (X , n , t) j = X , n , squash₁ (PT.map _⁻¹ₑ (PT.map _⁻¹ₑ t)) t j

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

-- truncation commutes with finite products

module _ {ℓ} {A : Type ℓ} (n : HLevel) where

  private
    open Iso

    Π𝟙+Iso : {X : Type} {B : Type ℓ} → Iso ((Unit* {ℓ-zero} ⊎ X) → B) (B × (X → B))
    Π𝟙+Iso .fun f = f (inl tt*) , f ∘ inr
    Π𝟙+Iso .inv (b , g) = ⊎.rec (λ _ → b) g
    Π𝟙+Iso .sec _ = refl
    Π𝟙+Iso .ret _ = ⊎-η refl refl

    truncΠ→' : (X : UFin) → ∥ (⟨ X ⟩ → A) ∥ (suc n) → (⟨ X ⟩ → ∥ A ∥ (suc n))
    truncΠ→' X = truncΠ→ n ⟨ X ⟩

  isEquivTruncΠ→ : (X : UFin) → isEquiv (truncΠ→ n ⟨ X ⟩)
  isEquivTruncΠ→ =
    FS.elimProp𝟙+
      (λ X → isEquiv (truncΠ→' X))
      (λ _ → isPropIsEquiv _)
      base
      (λ {X} → step {X})
    where
      base : isEquiv (truncΠ→' 𝟘)
      base = isEquivFromIsContr _ (isContr→isContrTrunc (suc n) isContrΠ⊥*) isContrΠ⊥*

      module _ {X : UFin} (h : isEquiv (truncΠ→' X)) where

        e : ∥ (Unit* ⊎ ⟨ X ⟩ → A) ∥ (suc n) ≃ (Unit* ⊎ ⟨ X ⟩ → ∥ A ∥ (suc n))
        e =
          ∥ (Unit* ⊎ ⟨ X ⟩ → A) ∥ (suc n)
            ≃⟨ isoToEquiv (mapCompIso Π𝟙+Iso) ⟩
          ∥ A × (⟨ X ⟩ → A) ∥ (suc n)
            ≃⟨ isoToEquiv (truncOfProdIso (suc n)) ⟩
          ∥ A ∥ (suc n) × ∥ (⟨ X ⟩ → A) ∥ (suc n)
            ≃⟨ Σ-cong-equiv-snd (λ _ → truncΠ→' X , h) ⟩
          ∥ A ∥ (suc n) × (⟨ X ⟩ → ∥ A ∥ (suc n))
            ≃⟨ isoToEquiv (invIso Π𝟙+Iso) ⟩
          (Unit* ⊎ ⟨ X ⟩ → ∥ A ∥ (suc n))
            ■

        e≡truncΠ→ : –> e ≡ truncΠ→' (𝟙 +ᶠ X)
        e≡truncΠ→ =
          funExt (Trunc.elim {B = λ p → –> e p ≡ truncΠ→' (𝟙 +ᶠ X) p}
            (λ _ → isOfHLevelPath (suc n) (isOfHLevelΠ _ λ _ → isOfHLevelTrunc _) _ _)
            (λ _ → ⊎-η refl refl)
          )

        step : isEquiv (truncΠ→' (𝟙 +ᶠ X))
        step = tpt isEquiv e≡truncΠ→ (snd e)

-- rig coherences for fun (we don't need them)

-- naturality of distributors and annihilators

module _ {ℓ} {A A' B B' C C' : Type ℓ} (e₁ : A ≃ A') (e₂ : B ≃ B') (e₃ : C ≃ C') where

  -- dist⟷₂l
  ×-distribʳ≃-nat : ≃-× (⊎-equiv e₁ e₂) e₃ ∙ₑ ×-distribʳ≃ ≡ ×-distribʳ≃ ∙ₑ ⊎-equiv (≃-× e₁ e₃) (≃-× e₂ e₃)
  ×-distribʳ≃-nat = equivEq (×-η (⊎-η refl refl))

  -- distl⟷₂l
  ×-distribˡ≃-nat : ≃-× e₁ (⊎-equiv e₂ e₃) ∙ₑ ×-distribˡ≃ ≡ ×-distribˡ≃ ∙ₑ ⊎-equiv (≃-× e₁ e₂) (≃-× e₁ e₃)
  ×-distribˡ≃-nat = equivEq (×-η (funExt λ _ → ⊎-η refl refl))

module _ {ℓ} {A A' : Type ℓ} (e : A ≃ A') where

  -- absorbl⟷₂l
  ×-zeroʳ≃-nat : ≃-× e (idEquiv (⊥* {ℓ})) ∙ₑ ×-zeroʳ≃ ≡ ×-zeroʳ≃
  ×-zeroʳ≃-nat = equivEq (×-η (funExt λ _ → ⊥*-η))

  -- absorbr⟷₂l
  ×-zeroˡ≃-nat : ≃-× (idEquiv (⊥* {ℓ})) e ∙ₑ ×-zeroˡ≃ ≡ ×-zeroˡ≃
  ×-zeroˡ≃-nat = equivEq (×-η ⊥*-η)

-- laplaza's coherences

module _ {ℓ} {A B C D : Type ℓ} where

  -- swap₊distl⟷₂l
  ×-distribˡ-swap : Path (A × (B ⊎ C) ≃ (A × C) ⊎ (A × B))
    (≃-× (idEquiv A) ⊎-swap-≃ ∙ₑ ×-distribˡ≃) (×-distribˡ≃ ∙ₑ ⊎-swap-≃)
  ×-distribˡ-swap = equivEq (×-η (funExt λ _ → ⊎-η refl refl))

  -- dist-swap⋆⟷₂l
  ×-distribʳ-swap : Path ((A ⊎ B) × C ≃ (C × A) ⊎ (C × B))
    (×-distribʳ≃ ∙ₑ ⊎-equiv Σ-swap-≃ Σ-swap-≃) (Σ-swap-≃ ∙ₑ ×-distribˡ≃)
  ×-distribʳ-swap = equivEq (×-η (⊎-η refl refl))

  -- assocl₊-dist-dist⟷₂l
  ×-distribʳ-assoc : Path ((A ⊎ (B ⊎ C)) × D ≃ ((A × D) ⊎ (B × D)) ⊎ (C × D))
    (≃-× (⊎-assoc-≃ ⁻¹ₑ) (idEquiv D) ∙ₑ ×-distribʳ≃ ∙ₑ ⊎-equiv ×-distribʳ≃ (idEquiv _))
    (×-distribʳ≃ ∙ₑ ⊎-equiv (idEquiv _) ×-distribʳ≃ ∙ₑ ⊎-assoc-≃ ⁻¹ₑ)
  ×-distribʳ-assoc = equivEq (×-η (⊎-η refl (⊎-η refl refl)))

  -- assocl⋆-distl⟷₂l
  ×-distribˡ-assoc : Path (A × (B × (C ⊎ D)) ≃ ((A × B) × C) ⊎ ((A × B) × D))
    (Σ-assoc-≃ ⁻¹ₑ ∙ₑ ×-distribˡ≃)
    (≃-× (idEquiv A) ×-distribˡ≃ ∙ₑ ×-distribˡ≃ ∙ₑ ⊎-equiv (Σ-assoc-≃ ⁻¹ₑ) (Σ-assoc-≃ ⁻¹ₑ))
  ×-distribˡ-assoc = equivEq (×-η (funExt λ _ → ×-η (funExt λ _ → ⊎-η refl refl)))

  -- absorbr0-absorbl0⟷₂
  ×-zeroˡ≡×-zeroʳ : Path (⊥* {ℓ} × ⊥* {ℓ} ≃ ⊥*) ×-zeroˡ≃ ×-zeroʳ≃
  ×-zeroˡ≡×-zeroʳ = equivEq (×-η ⊥*-η)

  -- absorbr⟷₂distl-absorb-unite
  ×-zeroˡ-distribˡ : Path (⊥* {ℓ} × (A ⊎ B) ≃ ⊥*)
    ×-zeroˡ≃ (×-distribˡ≃ ∙ₑ ⊎-equiv ×-zeroˡ≃ ×-zeroˡ≃ ∙ₑ ⊎-IdL-⊥*-≃)
  ×-zeroˡ-distribˡ = equivEq (×-η ⊥*-η)

  -- unite⋆r0-absorbr1⟷₂
  ×-unitʳ≡×-zeroˡ : Path (⊥* {ℓ} × Unit* {ℓ} ≃ ⊥*) ×-unitʳ≃ ×-zeroˡ≃
  ×-unitʳ≡×-zeroˡ = equivEq (×-η ⊥*-η)

  -- absorbl≡swap⋆◎absorbr
  ×-zeroʳ-swap : Path (A × ⊥* {ℓ} ≃ ⊥*) ×-zeroʳ≃ (Σ-swap-≃ ∙ₑ ×-zeroˡ≃)
  ×-zeroʳ-swap = equivEq (×-η (funExt λ _ → ⊥*-η))

  -- absorbr⟷₂[assocl⋆◎[absorbr⊗id⟷]]◎absorbr
  ×-zeroˡ-assoc : Path (⊥* {ℓ} × (A × B) ≃ ⊥*)
    ×-zeroˡ≃ (Σ-assoc-≃ ⁻¹ₑ ∙ₑ ≃-× ×-zeroˡ≃ (idEquiv B) ∙ₑ ×-zeroˡ≃)
  ×-zeroˡ-assoc = equivEq (×-η ⊥*-η)

  -- [id⟷⊗absorbr]◎absorbl⟷₂assocl⋆◎[absorbl⊗id⟷]◎absorbr
  ×-zero-assoc : Path (A × (⊥* {ℓ} × B) ≃ ⊥*)
    (≃-× (idEquiv A) ×-zeroˡ≃ ∙ₑ ×-zeroʳ≃) (Σ-assoc-≃ ⁻¹ₑ ∙ₑ ≃-× ×-zeroʳ≃ (idEquiv B) ∙ₑ ×-zeroˡ≃)
  ×-zero-assoc = equivEq (×-η (funExt λ _ → ×-η ⊥*-η))

  -- elim⊥-A[0⊕B]⟷₂l
  ×-distribˡ-unitˡ : Path (A × (⊥* {ℓ} ⊎ B) ≃ A × B)
    (≃-× (idEquiv A) ⊎-IdL-⊥*-≃) (×-distribˡ≃ ∙ₑ ⊎-equiv ×-zeroʳ≃ (idEquiv _) ∙ₑ ⊎-IdL-⊥*-≃)
  ×-distribˡ-unitˡ = equivEq (×-η (funExt λ _ → ⊎-η ⊥*-η refl))

  -- elim⊥-1[A⊕B]⟷₂l
  ×-unitˡ-distribˡ : Path (Unit* {ℓ} × (A ⊎ B) ≃ A ⊎ B) ×-unitˡ≃ (×-distribˡ≃ ∙ₑ ⊎-equiv ×-unitˡ≃ ×-unitˡ≃)
  ×-unitˡ-distribˡ = equivEq (×-η (funExt λ _ → ⊎-η refl refl))

  -- fully-distribute⟷₂l
  ×-distrib-full : Path ((A ⊎ B) × (C ⊎ D) ≃ (((A × C) ⊎ (B × C)) ⊎ (A × D)) ⊎ (B × D))
    (×-distribˡ≃ ∙ₑ ⊎-equiv ×-distribʳ≃ ×-distribʳ≃ ∙ₑ ⊎-assoc-≃ ⁻¹ₑ)
    (×-distribʳ≃ ∙ₑ ⊎-equiv ×-distribˡ≃ ×-distribˡ≃ ∙ₑ ⊎-assoc-≃ ⁻¹ₑ
     ∙ₑ ⊎-equiv ⊎-assoc-≃ (idEquiv _) ∙ₑ ⊎-equiv (⊎-equiv (idEquiv _) ⊎-swap-≃) (idEquiv _)
     ∙ₑ ⊎-equiv (⊎-assoc-≃ ⁻¹ₑ) (idEquiv _))
  ×-distrib-full = equivEq (×-η (⊎-η (funExt λ _ → ⊎-η refl refl) (funExt λ _ → ⊎-η refl refl)))
