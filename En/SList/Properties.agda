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
SList* A .S.β = ++-β
SList* A .S.▽ = {!!}
SList* A .S.⬠₌ = {!!}
SList* A .S.⬠₁ = {!!}
SList* A .S.⬠₂ = {!!}
SList* A .S.⬡₌ = {!!}
SList* A .S.⬡₁ = {!!}
SList* A .S.⬡₂ = {!!}
SList* A .S.β² = {!!}
SList* A .S.is-groupoid = {!!}


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
