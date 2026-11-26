-- {-# OPTIONS --lossy-unification #-}

module En.SList.Properties where

open import En.Prelude
open import En.SList.Base
open import En.SList.0Cells
open import En.SList.1Cells
open import En.SList.2Cells
import En.SMG as S hiding (SMG* ; SMG*Fun)
open import En.SMG.Free

private
  variable
    A : Type ℓ

SList* : ∀ {ℓ} (A : Type ℓ) → S.SMG*Sq (SList A)
SList* A = record
  { 𝕀 = nil
  ; _⊗_ = _++_
  ; α = ++-α
  ; Λ = ++-Λ
  ; ρ = ++-ρ
  ; β = ++-β
  ; ▽ = ++-▽
  ; ⬠₌ = ++-⬠₌
  ; ⬠₁ = ++-⬠₁
  ; ⬠₂ = ++-⬠₂
  ; ⬡₌ = ++-⬡₌
  ; ⬡₁ = ++-⬡₁
  ; ⬡₂ = ++-⬡₂
  ; β² = ++-β²
  ; is-groupoid = is-groupoid
 }

-- singletons

[_] : A → SList A
[ x ] = x :: nil

-- universal property

module Univ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) (B* : S.SMG*Sq B) where

  module B = S.SMG*Sq B*

  module _ (f : A → B) where

    _♯ : SList A → B
    _♯ =
      SListElim.elim (λ _ → B)
        B.𝕀
        (λ x b → f x B.⊗ b)
        (λ x y {xs} b →
          swap12 x y b)
        (λ x y {xs} b i →
          f x B.⊗ (f y B.⊗ b) ≡⟨ sym (B.α (f x) (f y) b) ⟩∙∙
          (f x B.⊗ f y) B.⊗ b ≡⟨ ap (B._⊗ b) (B.β² (f x) (f y) i) ⟩∙∙
          (f y B.⊗ f x) B.⊗ b ≡⟨ B.α (f y) (f x) b ⟩∙∙
          f y B.⊗ (f x B.⊗ b) ∎∙∙)
        (λ x y z {xs} b i →
          hcomp (hex-faces x y z b i) (f y B.⊗ swap12 x z b i))
        (λ x y z {xs} b i j →
          hfill (hex-faces x y z b i) (inS (f y B.⊗ swap12 x z b i)) j)
        sorry
        -- TODO: ⬡₂ case of SList ♯
        -- needs hexagon for swap12
        -- should use ⬡₁, ⬡₂, β-nat, α-nat and the pentagon
        (λ _ → B.is-groupoid)
      where
        swap12 : (x y : A) (b : B) → (f x B.⊗ (f y B.⊗ b)) ≡ (f y B.⊗ (f x B.⊗ b))
        swap12 x y b =
          f x B.⊗ (f y B.⊗ b) ≡⟨ sym (B.α (f x) (f y) b) ⟩∙∙
          (f x B.⊗ f y) B.⊗ b ≡⟨ ap (B._⊗ b) (B.β (f x) (f y)) ⟩∙∙
          (f y B.⊗ f x) B.⊗ b ≡⟨ B.α (f y) (f x) b ⟩∙∙
          f y B.⊗ (f x B.⊗ b) ∎∙∙
        hex-faces : (x y z : A) (b : B) (i : I) → I → Partial (i ∨ ~ i) B
        hex-faces x y z b i j (i = i0) = swap12 x y (f z B.⊗ b) (~ j)
        hex-faces x y z b i j (i = i1) = swap12 y z (f x B.⊗ b) j

    _♯* : S.SMG*Fun*Sq (SList* A) B* _♯
    _♯* .S.-𝕀 = refl
    _♯* .S.-⊗ xs ys =
      SListElimSet.elim (λ xs → (xs ++ ys) ♯ ≡ (xs ♯) B.⊗ (ys ♯))
        (sym (B.Λ (ys ♯)))
        (λ x {xs} p → ap (f x B.⊗_) p ∙ sym (B.α (f x) (xs ♯) (ys ♯)))
        sorry
        -- TODO: swap case of SList ♯ preserves ⊗
        --  naturality of swap12 against α and β
        (λ xs → B.is-groupoid _ _)
        xs
    _♯* .S.-α₌ X Y Z =
      ((X ++ Y) ♯) B.⊗ (Z ♯) ≡⟨ sym (_♯* .S.-⊗ (X ++ Y) Z) ⟩∙∙
      ((X ++ Y) ++ Z) ♯ ≡⟨ ap _♯ (++-α X Y Z) ⟩∙∙
      (X ++ (Y ++ Z)) ♯ ≡⟨ _♯* .S.-⊗ X (Y ++ Z) ⟩∙∙
      (X ♯) B.⊗ ((Y ++ Z) ♯) ∎∙∙
    _♯* .S.-α₁ X Y Z =
      doubleCompPath-filler (sym (_♯* .S.-⊗ (X ++ Y) Z)) (ap _♯ (++-α X Y Z)) (_♯* .S.-⊗ X (Y ++ Z))
    _♯* .S.-α₂ = sorry
      -- TODO: SList ♯ preserves α (-α₂)
    _♯* .S.-Λ X i = sym (B.Λ (X ♯))
    _♯* .S.-ρ = sorry
      -- TODO: SList ♯ preserves ρ
    _♯* .S.-β = sorry
      -- TODO: SList ♯ preserves β

  _♭ : Σ (SList A → B) (S.SMG*Fun*Sq (SList* A) B*) → (A → B)
  _♭ g = g .fst ∘ [_]

  ♭♯ : (f : A → B) → (f ♯ , f ♯*) ♭ ≡ f
  ♭♯ f = funExt (B.ρ ∘ f)

  ♯♭ : (g : Σ (SList A → B) (S.SMG*Fun*Sq (SList* A) B*)) → (g ♭ ♯ , g ♭ ♯*) ≡ g
  ♯♭ = sorry
    -- TODO: SList ♯ after ♭
    --  S.SMG*Fun*Sq≡ with nat by SListElimSet, as FSMG ♯-uniq and ♭-retract

  univ : isEquiv _♭
  univ = isoToIsEquiv (iso _♭ (λ f → f ♯ , f ♯*) ♭♯ ♯♭)

isFreeSList : isFreeSMG (SList* A) [_] ℓ'
isFreeSList {A = A} B B* = Univ.univ A B B*
