module En.Univ.Properties where

open import En.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv.Properties
open import En.Univ.Base
import En.SMG as S hiding ( SMG* ; SMG*Fun )
open import En.SMG.Code

private
  variable
    ℓ ℓ' : Level

module _ (𝒰 : UUniv ℓ ℓ') where

  private
    module 𝒰 = Univ (𝒰 .fst)

  El≡≃ : {X Y : 𝒰.U} → (X ≡ Y) ≃ (𝒰.El X ≃ 𝒰.El Y)
  El≡≃ = _ , 𝒰 .snd _ _

  pathToEquivEl : {X Y : 𝒰.U} → X ≡ Y → 𝒰.El X ≃ 𝒰.El Y
  pathToEquivEl = –> El≡≃

  uaEl : {X Y : 𝒰.U} → 𝒰.El X ≃ 𝒰.El Y → X ≡ Y
  uaEl = <– El≡≃

  uaElβ : {X Y : 𝒰.U} (e : 𝒰.El X ≃ 𝒰.El Y) → pathToEquivEl (uaEl e) ≡ e
  uaElβ = secEq El≡≃

  uaElη : {X Y : 𝒰.U} (p : X ≡ Y) → uaEl (pathToEquivEl p) ≡ p
  uaElη = retEq El≡≃

  pathToEquivElInj : {X Y : 𝒰.U} {p q : X ≡ Y} → pathToEquivEl p ≡ pathToEquivEl q → p ≡ q
  pathToEquivElInj = <– (congEquiv El≡≃)

  pathToEquivEl-refl : {X : 𝒰.U} → pathToEquivEl (refl {x = X}) ≡ idEquiv (𝒰.El X)
  pathToEquivEl-refl = pathToEquivRefl

  pathToEquivEl-∙ : {X Y Z : 𝒰.U} (p : X ≡ Y) (q : Y ≡ Z)
    → pathToEquivEl (p ∙ q) ≡ pathToEquivEl p ∙ₑ pathToEquivEl q
  pathToEquivEl-∙ p q = equivEq (funExt (substComposite 𝒰.El p q))

  isContrΣEl≃ : (X : 𝒰.U) → isContr (Σ[ Y ∈ 𝒰.U ] (𝒰.El X ≃ 𝒰.El Y))
  isContrΣEl≃ X = isOfHLevelRespectEquiv 0 (Σ-cong-equiv-snd λ _ → El≡≃) (isContrSingl X)

  isOfHLevelU : (n : HLevel) → ((X : 𝒰.U) → isOfHLevel n (𝒰.El X)) → isOfHLevel (suc n) 𝒰.U
  isOfHLevelU n hEl = isOfHLevelPath'⁻ n λ X Y →
    isOfHLevelRespectEquiv n (El≡≃ ⁻¹ₑ) (isOfHLevel≃ n (hEl X) (hEl Y))

-- Type is a univalent universe

TypeUUniv : ∀ ℓ → UUniv (ℓ-suc ℓ) ℓ
TypeUUniv ℓ .fst = univ (Type ℓ) (idfun _)
TypeUUniv ℓ .snd _ _ = univalence .snd

-- subuniverses of Type are univalent universes

SubUUniv : SubUniv ℓ ℓ' → UUniv (ℓ-max (ℓ-suc ℓ) ℓ') ℓ
SubUUniv (P , _) .fst = univ (TypeWithStr _ P) fst
SubUUniv (_ , isPropP) .snd _ _ = ((_ , isEmbeddingFstΣProp isPropP) ∙ₑ univalence) .snd

-- SMG on a univalent universe

module _ (𝒰 : UUniv ℓ ℓ') (isGroupoidU : isGroupoid (𝒰 .fst .U)) where

  private
    module 𝒰 = Univ (𝒰 .fst)

  module UUnivSMG
    (𝕀 : 𝒰.U)
    (_⊗_ : 𝒰.U → 𝒰.U → 𝒰.U)
    (_⊗≃_ : {X X' Y Y' : 𝒰.U} → 𝒰.El X ≃ 𝒰.El X' → 𝒰.El Y ≃ 𝒰.El Y' → 𝒰.El (X ⊗ Y) ≃ 𝒰.El (X' ⊗ Y'))
    (pathToEquivEl-⊗ : {X X' Y Y' : 𝒰.U} (p : X ≡ X') (q : Y ≡ Y')
      → pathToEquivEl 𝒰 (λ i → p i ⊗ q i) ≡ pathToEquivEl 𝒰 p ⊗≃ pathToEquivEl 𝒰 q)
    (α≃ : (X Y Z : 𝒰.U) → 𝒰.El ((X ⊗ Y) ⊗ Z) ≃ 𝒰.El (X ⊗ (Y ⊗ Z)))
    (Λ≃ : (X : 𝒰.U) → 𝒰.El (𝕀 ⊗ X) ≃ 𝒰.El X)
    (ρ≃ : (X : 𝒰.U) → 𝒰.El (X ⊗ 𝕀) ≃ 𝒰.El X)
    (β≃ : (X Y : 𝒰.U) → 𝒰.El (X ⊗ Y) ≃ 𝒰.El (Y ⊗ X))
    (▽≃ : (X Y : 𝒰.U) → ρ≃ X ⊗≃ idEquiv (𝒰.El Y) ≡ α≃ X 𝕀 Y ∙ₑ (idEquiv (𝒰.El X) ⊗≃ Λ≃ Y))
    (⬠≃ : (W X Y Z : 𝒰.U)
      → α≃ (W ⊗ X) Y Z ∙ₑ α≃ W X (Y ⊗ Z)
      ≡ (α≃ W X Y ⊗≃ idEquiv (𝒰.El Z)) ∙ₑ α≃ W (X ⊗ Y) Z ∙ₑ (idEquiv (𝒰.El W) ⊗≃ α≃ X Y Z))
    (⬡≃ : (X Y Z : 𝒰.U)
      → α≃ X Y Z ∙ₑ β≃ X (Y ⊗ Z) ∙ₑ α≃ Y Z X
      ≡ (β≃ X Y ⊗≃ idEquiv (𝒰.El Z)) ∙ₑ α≃ Y X Z ∙ₑ (idEquiv (𝒰.El Y) ⊗≃ β≃ X Z))
    (β²≃ : (X Y : 𝒰.U) → β≃ X Y ∙ₑ β≃ Y X ≡ idEquiv (𝒰.El (X ⊗ Y)))
    where

    open CodeSMG (λ X Y → 𝒰.El X ≃ 𝒰.El Y) (λ _ _ → El≡≃ 𝒰) (λ X → idEquiv (𝒰.El X)) _∙ₑ_
      (λ _ → pathToEquivEl-refl 𝒰) (pathToEquivEl-∙ 𝒰) 𝕀 _⊗_ _⊗≃_ pathToEquivEl-⊗ α≃ Λ≃ ρ≃ β≃
      (λ X Y → ▽≃ X Y ∙ ap (α≃ X 𝕀 Y ∙ₑ_) (sym (compEquivEquivId _)))
      (λ W X Y Z → ap (α≃ (W ⊗ X) Y Z ∙ₑ_) (compEquivIdEquiv _) ∙ ⬠≃ W X Y Z)
      ⬡≃ β²≃ using (Code*)

    UUniv* : S.SMG*Sq 𝒰.U
    UUniv* = Code* isGroupoidU
