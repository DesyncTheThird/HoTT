module En.Univ.Properties where

open import En.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv.Properties
open import En.Univ.Base
import En.SMG as S hiding ( SMG* ; SMG*Fun )

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

-- SMG structure on a univalent universe

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

    private
      ptoe = pathToEquivEl 𝒰
      uaU = uaEl 𝒰
      β' = uaElβ 𝒰
      inj = pathToEquivElInj 𝒰
      ptoe-∙ = pathToEquivEl-∙ 𝒰
      ptoe-refl = pathToEquivEl-refl 𝒰

      ptoe-⊗ = pathToEquivEl-⊗

      ptoe-⊗ₗ : {X X' : 𝒰.U} (p : X ≡ X') (Y : 𝒰.U) → ptoe (ap (_⊗ Y) p) ≡ ptoe p ⊗≃ idEquiv (𝒰.El Y)
      ptoe-⊗ₗ p Y = ptoe-⊗ p refl ∙ ap (ptoe p ⊗≃_) ptoe-refl

      ptoe-⊗ᵣ : (X : 𝒰.U) {Y Y' : 𝒰.U} (q : Y ≡ Y') → ptoe (ap (X ⊗_) q) ≡ idEquiv (𝒰.El X) ⊗≃ ptoe q
      ptoe-⊗ᵣ X q = ptoe-⊗ refl q ∙ ap (_⊗≃ ptoe q) ptoe-refl

      α : (X Y Z : 𝒰.U) → (X ⊗ Y) ⊗ Z ≡ X ⊗ (Y ⊗ Z)
      α X Y Z = uaU (α≃ X Y Z)

      Λ : (X : 𝒰.U) → 𝕀 ⊗ X ≡ X
      Λ X = uaU (Λ≃ X)

      ρ : (X : 𝒰.U) → X ⊗ 𝕀 ≡ X
      ρ X = uaU (ρ≃ X)

      β : (X Y : 𝒰.U) → X ⊗ Y ≡ Y ⊗ X
      β X Y = uaU (β≃ X Y)

    UUniv* : S.SMG*Sq 𝒰.U
    UUniv* .S.𝕀 = 𝕀
    UUniv* .S._⊗_ = _⊗_
    UUniv* .S.α = α
    UUniv* .S.Λ = Λ
    UUniv* .S.ρ = ρ
    UUniv* .S.β = β
    UUniv* .S.▽ X Y = compPath→Square₁ (inj (lhs ∙ ▽≃ X Y ∙ sym rhs))
      where
        lhs : ptoe (ap (_⊗ Y) (ρ X)) ≡ ρ≃ X ⊗≃ idEquiv (𝒰.El Y)
        lhs = ptoe-⊗ₗ _ Y ∙ ap (_⊗≃ idEquiv (𝒰.El Y)) (β' _)
        rhs : ptoe (α X 𝕀 Y ∙ ap (X ⊗_) (Λ Y) ∙ refl) ≡ α≃ X 𝕀 Y ∙ₑ (idEquiv (𝒰.El X) ⊗≃ Λ≃ Y)
        rhs = ptoe-∙ _ _ ∙ cong₂ _∙ₑ_ (β' _)
                (ptoe-∙ _ _ ∙ ap (_∙ₑ ptoe refl) (ptoe-⊗ᵣ X _ ∙ ap (idEquiv (𝒰.El X) ⊗≃_) (β' _))
                 ∙ ap ((idEquiv (𝒰.El X) ⊗≃ Λ≃ Y) ∙ₑ_) ptoe-refl ∙ compEquivEquivId _)
    UUniv* .S.⬠₌ W X Y Z = α (W ⊗ X) Y Z ∙∙ refl ∙∙ α W X (Y ⊗ Z)
    UUniv* .S.⬠₁ W X Y Z = flipSquare (doubleCompPath-filler (α (W ⊗ X) Y Z) refl (α W X (Y ⊗ Z)))
    UUniv* .S.⬠₂ W X Y Z = compPath→Square₂ (inj (lhs ∙ ⬠≃ W X Y Z ∙ sym rhs))
      where
        lhs : ptoe (α (W ⊗ X) Y Z ∙∙ refl ∙∙ α W X (Y ⊗ Z)) ≡ α≃ (W ⊗ X) Y Z ∙ₑ α≃ W X (Y ⊗ Z)
        lhs = ap ptoe (doubleCompPath≡compPath _ _ _) ∙ ptoe-∙ _ _
            ∙ cong₂ _∙ₑ_ (β' _) (ptoe-∙ _ _ ∙ cong₂ _∙ₑ_ ptoe-refl (β' _) ∙ compEquivIdEquiv _)
        rhs : ptoe (ap (_⊗ Z) (α W X Y) ∙ α W (X ⊗ Y) Z ∙ ap (W ⊗_) (α X Y Z))
            ≡ (α≃ W X Y ⊗≃ idEquiv (𝒰.El Z)) ∙ₑ α≃ W (X ⊗ Y) Z ∙ₑ (idEquiv (𝒰.El W) ⊗≃ α≃ X Y Z)
        rhs = ptoe-∙ _ _ ∙ cong₂ _∙ₑ_ (ptoe-⊗ₗ _ Z ∙ ap (_⊗≃ idEquiv (𝒰.El Z)) (β' _))
                (ptoe-∙ _ _ ∙ cong₂ _∙ₑ_ (β' _) (ptoe-⊗ᵣ W _ ∙ ap (idEquiv (𝒰.El W) ⊗≃_) (β' _)))
    UUniv* .S.⬡₌ X Y Z = α X Y Z ∙∙ β X (Y ⊗ Z) ∙∙ α Y Z X
    UUniv* .S.⬡₁ X Y Z = flipSquare (doubleCompPath-filler (α X Y Z) (β X (Y ⊗ Z)) (α Y Z X))
    UUniv* .S.⬡₂ X Y Z = compPath→Square₂ (inj (lhs ∙ ⬡≃ X Y Z ∙ sym rhs))
      where
        lhs : ptoe (α X Y Z ∙∙ β X (Y ⊗ Z) ∙∙ α Y Z X) ≡ α≃ X Y Z ∙ₑ β≃ X (Y ⊗ Z) ∙ₑ α≃ Y Z X
        lhs = ap ptoe (doubleCompPath≡compPath _ _ _) ∙ ptoe-∙ _ _
            ∙ cong₂ _∙ₑ_ (β' _) (ptoe-∙ _ _ ∙ cong₂ _∙ₑ_ (β' _) (β' _))
        rhs : ptoe (ap (_⊗ Z) (β X Y) ∙ α Y X Z ∙ ap (Y ⊗_) (β X Z))
            ≡ (β≃ X Y ⊗≃ idEquiv (𝒰.El Z)) ∙ₑ α≃ Y X Z ∙ₑ (idEquiv (𝒰.El Y) ⊗≃ β≃ X Z)
        rhs = ptoe-∙ _ _ ∙ cong₂ _∙ₑ_ (ptoe-⊗ₗ _ Z ∙ ap (_⊗≃ idEquiv (𝒰.El Z)) (β' _))
                (ptoe-∙ _ _ ∙ cong₂ _∙ₑ_ (β' _) (ptoe-⊗ᵣ Y _ ∙ ap (idEquiv (𝒰.El Y) ⊗≃_) (β' _)))
    UUniv* .S.β² X Y = compPath≡refl→≡sym (inj (ptoe-∙ _ _ ∙ cong₂ _∙ₑ_ (β' _) (β' _) ∙ β²≃ X Y ∙ sym ptoe-refl))
    UUniv* .S.is-groupoid = isGroupoidU
