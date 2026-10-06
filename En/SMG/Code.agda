module En.SMG.Code where

open import En.Prelude
open import Cubical.Foundations.Equiv.Properties
import En.SMG as S hiding ( SMG* ; SMG*Fun )

private
  variable
    ℓ ℓ' : Level

-- SMG via path codes

module CodeSMG {El : Type ℓ}
  (Code : El → El → Type ℓ')
  (Path≃Code : (X Y : El) → (X ≡ Y) ≃ Code X Y)
  (reflᶜ : (X : El) → Code X X)
  (_∙ᶜ_ : {X Y Z : El} → Code X Y → Code Y Z → Code X Z)
  (encodeRefl : (X : El) → –> (Path≃Code X X) refl ≡ reflᶜ X)
  (encode-∙ : {X Y Z : El} (p : X ≡ Y) (q : Y ≡ Z)
    → –> (Path≃Code X Z) (p ∙ q) ≡ –> (Path≃Code X Y) p ∙ᶜ –> (Path≃Code Y Z) q)
  (𝕀 : El)
  (_⊗_ : El → El → El)
  (_⊗ᶜ_ : {X X' Y Y' : El} → Code X X' → Code Y Y' → Code (X ⊗ Y) (X' ⊗ Y'))
  (encode-⊗ : {X X' Y Y' : El} (p : X ≡ X') (q : Y ≡ Y')
    → –> (Path≃Code (X ⊗ Y) (X' ⊗ Y')) (λ i → p i ⊗ q i) ≡ –> (Path≃Code X X') p ⊗ᶜ –> (Path≃Code Y Y') q)
  (αᶜ : (X Y Z : El) → Code ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z)))
  (Λᶜ : (X : El) → Code (𝕀 ⊗ X) X)
  (ρᶜ : (X : El) → Code (X ⊗ 𝕀) X)
  (βᶜ : (X Y : El) → Code (X ⊗ Y) (Y ⊗ X))
  (▽ᶜ : (X Y : El) → ρᶜ X ⊗ᶜ reflᶜ Y ≡ αᶜ X 𝕀 Y ∙ᶜ ((reflᶜ X ⊗ᶜ Λᶜ Y) ∙ᶜ reflᶜ (X ⊗ Y)))
  (⬠ᶜ : (W X Y Z : El)
    → αᶜ (W ⊗ X) Y Z ∙ᶜ (reflᶜ ((W ⊗ X) ⊗ (Y ⊗ Z)) ∙ᶜ αᶜ W X (Y ⊗ Z))
    ≡ (αᶜ W X Y ⊗ᶜ reflᶜ Z) ∙ᶜ (αᶜ W (X ⊗ Y) Z ∙ᶜ (reflᶜ W ⊗ᶜ αᶜ X Y Z)))
  (⬡ᶜ : (X Y Z : El)
    → αᶜ X Y Z ∙ᶜ (βᶜ X (Y ⊗ Z) ∙ᶜ αᶜ Y Z X)
    ≡ (βᶜ X Y ⊗ᶜ reflᶜ Z) ∙ᶜ (αᶜ Y X Z ∙ᶜ (reflᶜ Y ⊗ᶜ βᶜ X Z)))
  (β²ᶜ : (X Y : El) → βᶜ X Y ∙ᶜ βᶜ Y X ≡ reflᶜ (X ⊗ Y))
  where

  private
    encode : {X Y : El} → X ≡ Y → Code X Y
    encode = –> (Path≃Code _ _)

    decode : {X Y : El} → Code X Y → X ≡ Y
    decode = <– (Path≃Code _ _)

    encodeDecode : {X Y : El} (c : Code X Y) → encode (decode c) ≡ c
    encodeDecode = secEq (Path≃Code _ _)

    encodeInj : {X Y : El} {p q : X ≡ Y} → encode p ≡ encode q → p ≡ q
    encodeInj = <– (congEquiv (Path≃Code _ _))

    encode-⊗ₗ : {X X' : El} (p : X ≡ X') (Y : El) → encode (ap (_⊗ Y) p) ≡ encode p ⊗ᶜ reflᶜ Y
    encode-⊗ₗ p Y = encode-⊗ p refl ∙ ap (encode p ⊗ᶜ_) (encodeRefl _)

    encode-⊗ᵣ : (X : El) {Y Y' : El} (q : Y ≡ Y') → encode (ap (X ⊗_) q) ≡ reflᶜ X ⊗ᶜ encode q
    encode-⊗ᵣ X q = encode-⊗ refl q ∙ ap (_⊗ᶜ encode q) (encodeRefl _)

  α : (X Y Z : El) → (X ⊗ Y) ⊗ Z ≡ X ⊗ (Y ⊗ Z)
  α X Y Z = decode (αᶜ X Y Z)

  Λ : (X : El) → 𝕀 ⊗ X ≡ X
  Λ X = decode (Λᶜ X)

  ρ : (X : El) → X ⊗ 𝕀 ≡ X
  ρ X = decode (ρᶜ X)

  β : (X Y : El) → X ⊗ Y ≡ Y ⊗ X
  β X Y = decode (βᶜ X Y)

  Code* : isGroupoid El → S.SMG*Sq El
  Code* _ .S.𝕀 = 𝕀
  Code* _ .S._⊗_ = _⊗_
  Code* _ .S.α = α
  Code* _ .S.Λ = Λ
  Code* _ .S.ρ = ρ
  Code* _ .S.β = β
  Code* _ .S.▽ X Y = compPath→Square₁ (encodeInj (lhs ∙ ▽ᶜ X Y ∙ sym rhs))
    where
      lhs : encode (ap (_⊗ Y) (ρ X)) ≡ ρᶜ X ⊗ᶜ reflᶜ Y
      lhs = encode-⊗ₗ (ρ X) Y ∙ ap (_⊗ᶜ reflᶜ Y) (encodeDecode _)
      rhs : encode (α X 𝕀 Y ∙ ap (X ⊗_) (Λ Y) ∙ refl) ≡ αᶜ X 𝕀 Y ∙ᶜ ((reflᶜ X ⊗ᶜ Λᶜ Y) ∙ᶜ reflᶜ (X ⊗ Y))
      rhs = encode-∙ _ _ ∙ cong₂ _∙ᶜ_ (encodeDecode _)
              (encode-∙ _ _ ∙ cong₂ _∙ᶜ_ (encode-⊗ᵣ X (Λ Y) ∙ ap (reflᶜ X ⊗ᶜ_) (encodeDecode _)) (encodeRefl _))
  Code* _ .S.⬠₌ W X Y Z = α (W ⊗ X) Y Z ∙∙ refl ∙∙ α W X (Y ⊗ Z)
  Code* _ .S.⬠₁ W X Y Z = flipSquare (doubleCompPath-filler (α (W ⊗ X) Y Z) refl (α W X (Y ⊗ Z)))
  Code* _ .S.⬠₂ W X Y Z = compPath→Square₂ (encodeInj (lhs ∙ ⬠ᶜ W X Y Z ∙ sym rhs))
    where
      lhs : encode (α (W ⊗ X) Y Z ∙∙ refl ∙∙ α W X (Y ⊗ Z))
          ≡ αᶜ (W ⊗ X) Y Z ∙ᶜ (reflᶜ ((W ⊗ X) ⊗ (Y ⊗ Z)) ∙ᶜ αᶜ W X (Y ⊗ Z))
      lhs = ap encode (doubleCompPath≡compPath _ _ _) ∙ encode-∙ _ _
          ∙ cong₂ _∙ᶜ_ (encodeDecode _) (encode-∙ _ _ ∙ cong₂ _∙ᶜ_ (encodeRefl _) (encodeDecode _))
      rhs : encode (ap (_⊗ Z) (α W X Y) ∙ α W (X ⊗ Y) Z ∙ ap (W ⊗_) (α X Y Z))
          ≡ (αᶜ W X Y ⊗ᶜ reflᶜ Z) ∙ᶜ (αᶜ W (X ⊗ Y) Z ∙ᶜ (reflᶜ W ⊗ᶜ αᶜ X Y Z))
      rhs = encode-∙ _ _ ∙ cong₂ _∙ᶜ_ (encode-⊗ₗ _ Z ∙ ap (_⊗ᶜ reflᶜ Z) (encodeDecode _))
              (encode-∙ _ _ ∙ cong₂ _∙ᶜ_ (encodeDecode _) (encode-⊗ᵣ W _ ∙ ap (reflᶜ W ⊗ᶜ_) (encodeDecode _)))
  Code* _ .S.⬡₌ X Y Z = α X Y Z ∙∙ β X (Y ⊗ Z) ∙∙ α Y Z X
  Code* _ .S.⬡₁ X Y Z = flipSquare (doubleCompPath-filler (α X Y Z) (β X (Y ⊗ Z)) (α Y Z X))
  Code* _ .S.⬡₂ X Y Z = compPath→Square₂ (encodeInj (lhs ∙ ⬡ᶜ X Y Z ∙ sym rhs))
    where
      lhs : encode (α X Y Z ∙∙ β X (Y ⊗ Z) ∙∙ α Y Z X) ≡ αᶜ X Y Z ∙ᶜ (βᶜ X (Y ⊗ Z) ∙ᶜ αᶜ Y Z X)
      lhs = ap encode (doubleCompPath≡compPath _ _ _) ∙ encode-∙ _ _
          ∙ cong₂ _∙ᶜ_ (encodeDecode _) (encode-∙ _ _ ∙ cong₂ _∙ᶜ_ (encodeDecode _) (encodeDecode _))
      rhs : encode (ap (_⊗ Z) (β X Y) ∙ α Y X Z ∙ ap (Y ⊗_) (β X Z))
          ≡ (βᶜ X Y ⊗ᶜ reflᶜ Z) ∙ᶜ (αᶜ Y X Z ∙ᶜ (reflᶜ Y ⊗ᶜ βᶜ X Z))
      rhs = encode-∙ _ _ ∙ cong₂ _∙ᶜ_ (encode-⊗ₗ _ Z ∙ ap (_⊗ᶜ reflᶜ Z) (encodeDecode _))
              (encode-∙ _ _ ∙ cong₂ _∙ᶜ_ (encodeDecode _) (encode-⊗ᵣ Y _ ∙ ap (reflᶜ Y ⊗ᶜ_) (encodeDecode _)))
  Code* _ .S.β² X Y =
    compPath≡refl→≡sym (encodeInj (encode-∙ _ _ ∙ cong₂ _∙ᶜ_ (encodeDecode _) (encodeDecode _) ∙ β²ᶜ X Y ∙ sym (encodeRefl _)))
  Code* isGroupoidEl .S.is-groupoid = isGroupoidEl
