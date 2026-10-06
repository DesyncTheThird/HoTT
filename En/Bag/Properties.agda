module En.Bag.Properties where

open import En.Prelude
open import Cubical.Data.Sum
open import En.Univ
open import En.UFin
open import En.Bag.Base
import En.SMG as S hiding ( SMG* ; SMG*Fun )
open import En.SMG.Code
open import Cubical.HITs.Truncation as Trunc

private
  variable
    ℓ : Level

module _ {A : Type ℓ} where

  open FamPath UFinSub A public

  isOfHLevelBag : (n : HLevel) → isOfHLevel (3 + n) A → isOfHLevel (3 + n) (Bag A)
  isOfHLevelBag n = isOfHLevelFam (3 + n) (isOfHLevelPlus' 3 isGroupoidUFin)

  isGroupoidBag : isGroupoid A → isGroupoid (Bag A)
  isGroupoidBag = isOfHLevelBag 0

  _⊗ᶜ_ : {X X' Y Y' : Bag A} → Cover X X' → Cover Y Y' → Cover (X ⊗ Y) (X' ⊗ Y')
  (c ⊗ᶜ d) .equiv = ⊎-equiv (c .equiv) (d .equiv)
  (c ⊗ᶜ d) .label (inl x) = c .label x
  (c ⊗ᶜ d) .label (inr y) = d .label y

  -- encode on sums
  encode-⊗ : {X X' Y Y' : Bag A} (p : X ≡ X') (q : Y ≡ Y')
    → encode (X ⊗ Y) (X' ⊗ Y') (λ i → p i ⊗ q i) ≡ encode X X' p ⊗ᶜ encode Y Y' q
  encode-⊗ p q =
    encodeTransport _ _ _ ∙ Cover≡ (⊎-η refl refl) (⊎-ηP refl refl)
    ∙ sym (cong₂ _⊗ᶜ_ (encodeTransport _ _ p) (encodeTransport _ _ q))

  -- SM structure on relabellings

  αᶜ : (X Y Z : Bag A) → Cover ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z))
  αᶜ X Y Z = cover ⊎-assoc-≃ (funExt⁻ (⊎-η (⊎-η refl refl) refl))

  Λᶜ : (X : Bag A) → Cover (𝕀 ⊗ X) X
  Λᶜ X = cover ⊎-IdL-⊥*-≃ (funExt⁻ (⊎-η ⊥*-η refl))

  ρᶜ : (X : Bag A) → Cover (X ⊗ 𝕀) X
  ρᶜ X = cover ⊎-IdR-⊥*-≃ (funExt⁻ (⊎-η refl ⊥*-η))

  βᶜ : (X Y : Bag A) → Cover (X ⊗ Y) (Y ⊗ X)
  βᶜ X Y = cover ⊎-swap-≃ (funExt⁻ (⊎-η refl refl))

  private
    r3 : {a : A} → refl {x = a} ≡ refl ∙ refl ∙ refl
    r3 = rUnit refl ∙ ap (refl ∙_) (rUnit refl)

  open CodeSMG Cover Path≃Cover reflCode _∙ᶜ_ encodeRefl encode-∙ 𝕀 _⊗_ _⊗ᶜ_ encode-⊗ αᶜ Λᶜ ρᶜ βᶜ
    (λ _ _ → Cover≡ (⊎-η (⊎-η refl ⊥*-η) refl) (⊎-ηP (⊎-ηP (funExt λ _ → r3) ⊥*-ηP) (funExt λ _ → r3)))
    (λ _ _ _ _ → Cover≡ (⊎-η (⊎-η (⊎-η refl refl) refl) refl) (⊎-ηP (⊎-ηP (⊎-ηP refl refl) refl) refl))
    (λ _ _ _ → Cover≡ (⊎-η (⊎-η refl refl) refl) (⊎-ηP (⊎-ηP refl refl) refl))
    (λ _ _ → Cover≡ (⊎-η refl refl) (⊎-ηP (funExt λ _ → sym (rUnit refl)) (funExt λ _ → sym (rUnit refl))))
    using (α ; Λ ; ρ ; β ; Code*) public

-- SMG on bags

Bag* : {A : Type ℓ} → isGroupoid A → S.SMG*Sq (Bag A)
Bag* isGroupoidA = Code* (isGroupoidBag isGroupoidA)

-- truncation commutes with bags

module _ {A : Type ℓ} (n : HLevel) where

  truncBag≃ : ∥ Bag A ∥ (3 + n) ≃ Bag (∥ A ∥ (3 + n))
  truncBag≃ = truncFam≃ UFinSub (2 + n) (isOfHLevelPlus' 3 isGroupoidUFin) (isEquivTruncΠ→ (2 + n))

  truncBag≃-β : (X : Bag A) → –> truncBag≃ ∣ X ∣ ≡ mapBag ∣_∣ X
  truncBag≃-β _ = refl
