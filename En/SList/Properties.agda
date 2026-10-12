module En.SList.Properties where

open import En.Prelude
open import En.SList.Base
open import En.SList.0Cells
open import En.SList.1Cells
import En.SMG as S hiding (SMG* ; SMG*Fun)

private
  variable
    ℓ : Level
    A : Type ℓ

SList* : ∀ {ℓ} (A : Type ℓ) → S.SMG*Sq (SList A)
SList* A .S.𝕀 = nil
SList* A .S._⊗_ = _++_
SList* A .S.α = ++-α
SList* A .S.Λ = ++-Λ
SList* A .S.ρ = ++-ρ
SList* A .S.β = sorry -- TODO: symmetry β for SList*
SList* A .S.▽ = sorry -- TODO: triangle ▽ for SList*
SList* A .S.⬠₌ = sorry -- TODO: pentagon ⬠₌ for SList*
SList* A .S.⬠₁ = sorry -- TODO: pentagon ⬠₁ for SList*
SList* A .S.⬠₂ = sorry -- TODO: pentagon ⬠₂ for SList*
SList* A .S.⬡₌ = sorry -- TODO: hexagon ⬡₌ for SList*
SList* A .S.⬡₁ = sorry -- TODO: hexagon ⬡₁ for SList*
SList* A .S.⬡₂ = sorry -- TODO: hexagon ⬡₂ for SList*
SList* A .S.β² = sorry -- TODO: symmetry involution β² for SList*
SList* A .S.is-groupoid = sorry -- TODO: is-groupoid for SList*


-- module Univ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) (B* : S.SMG*Sq B) where

  -- module B = SMG*Sq B*

  -- module _ (f : A → B) where

  -- _♭ : Σ (FSMG A → B) (S.SMG*Fun*Sq (SList* A) B*) → (A → B)
  -- _♭ (g , _) = g ∘ η

  -- ♯-uniq : (f : A → B) (h : FSMG A → B) (h* : S.SMG*Fun*Sq (SList* A) B* h) → (h ∘ η ≡ f) → ∀ xs → h xs ≡ (f ♯) xs

  -- ♯-uniq-⊗ : (f : A → B)
  --            (h : FSMG A → B)
  --            (h* : S.SMG*Fun*Sq (FSMG* A) B* h)
  --            (p : h ∘ η ≡ f)
  --            (X Y : FSMG A)
  --            → ♯-uniq f h h* p (X ⊗ Y) ≡ let open S in
  --             (h* .-⊗ X Y ∙ ap₂ B._⊗_ (♯-uniq f h h* p X) (♯-uniq f h h* p Y))
  -- ♯-uniq-⊗ f h h* p X Y = ?


  -- ♭-retract : retract _♭ (λ g → (g ♯) , (g ♯*))
  -- ♭-retract (g , g*) = ?
  -- univ : isEquiv _♭
  -- univ = isoToIsEquiv (
  --   iso _♭ (λ f → f ♯ , f ♯*)
  --     (λ _ → refl)
  --     ♭-retract
  --   )
