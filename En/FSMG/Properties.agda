module En.FSMG.Properties where

open import En.Prelude
open import En.FSMG.Base
import En.SMG as S

-- FSMG-has-SMG*Struct : ∀ {ℓ} (A : Type ℓ) → S.SMG*Struct (FSMG A)
-- FSMG-has-SMG*Struct A .S.𝕀 = 𝕀
-- FSMG-has-SMG*Struct A .S._⊗_ = _⊗_
-- FSMG-has-SMG*Struct A .S.α = α
-- FSMG-has-SMG*Struct A .S.Λ = Λ
-- FSMG-has-SMG*Struct A .S.ρ = ρ
-- FSMG-has-SMG*Struct A .S.β = β
-- FSMG-has-SMG*Struct A .S.▽ X Y = Triangle→compPath₃ (▽ X Y)
-- FSMG-has-SMG*Struct A .S.⬠ W X Y Z = Pentagon→compPath (⬠₌ W X Y Z) (⬠₁ W X Y Z) (⬠₂ W X Y Z)
-- FSMG-has-SMG*Struct A .S.⬡ X Y Z = Hexagon→compPath (⬡₌ X Y Z) (⬡₁ X Y Z) (⬡₂ X Y Z)
-- FSMG-has-SMG*Struct A .S.β² X Y = ap (_∙ β Y X) (β² X Y) ∙ lCancel (β Y X)
-- FSMG-has-SMG*Struct A .S.is-groupoid = is-groupoid

-- module Univ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) (SMGB : S.SMG*Struct B) where

--   module B = S.SMG*Struct SMGB

--   module _ (f : A → B) where

--     module F = FSMG*Rec A f B.𝕀 B._⊗_ B.α B.Λ B.ρ B.β
--         (λ X* Y* → compPath→Triangle₃ (B.▽ X* Y*))
--         (λ W* X* Y* Z* → B.α (W* B.⊗ X*) Y* Z* ∙ B.α W* X* (Y* B.⊗ Z*))
--         (λ W* X* Y* Z* → compPath→Pentagon (B.⬠ W* X* Y* Z*) .snd .fst)
--         (λ W* X* Y* Z* → compPath→Pentagon (B.⬠ W* X* Y* Z*) .snd .snd)
--         (λ X* Y* Z* → compPath→Hexagon (B.⬡ X* Y* Z*) .fst)
--         (λ X* Y* Z* → compPath→Hexagon (B.⬡ X* Y* Z*) .snd .fst)
--         (λ X* Y* Z* → compPath→Hexagon (B.⬡ X* Y* Z*) .snd .snd)
--         (λ X* Y* → Eq→Square₂₃ (B.β² X* Y*))
--         B.is-groupoid


--     _♯ : (FSMG A → B)
--     _♯ = F.f

--     ♯-SMG*Functor : S.SMG*Functor (FSMG A) (FSMG-has-SMG*Struct A) B SMGB (_♯)
--     ♯-SMG*Functor .S.f-𝕀 = refl
--     ♯-SMG*Functor .S.f-⊗ X Y = refl
--     ♯-SMG*Functor .S.f-α X Y Z = sorry
--     ♯-SMG*Functor .S.f-Λ X = sorry
--     ♯-SMG*Functor .S.f-ρ X = sorry
--     ♯-SMG*Functor .S.f-β X Y = sorry

FSMG* : ∀ {ℓ} (A : Type ℓ) → S.SMG*Sq (FSMG A)
FSMG* A .S.𝕀 = 𝕀
FSMG* A .S._⊗_ = _⊗_
FSMG* A .S.α = α
FSMG* A .S.Λ = Λ
FSMG* A .S.ρ = ρ
FSMG* A .S.β = β
FSMG* A .S.▽ = ▽
FSMG* A .S.⬠₌ = ⬠₌
FSMG* A .S.⬠₁ = ⬠₁
FSMG* A .S.⬠₂ = ⬠₂
FSMG* A .S.⬡₌ = ⬡₌
FSMG* A .S.⬡₁ = ⬡₁
FSMG* A .S.⬡₂ = ⬡₂
FSMG* A .S.β² = β²
FSMG* A .S.is-groupoid = is-groupoid

module Univ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) (B* : S.SMG*Sq B) where

  module B = S.SMG*Sq B*

  module _ (f : A → B) where

    module Rec = FSMG*Rec A f B.𝕀 B._⊗_ B.α B.Λ B.ρ B.β
                          B.▽ B.⬠₌ B.⬠₁ B.⬠₂ B.⬡₌ B.⬡₁ B.⬡₂ B.β² B.is-groupoid

    _♯ : FSMG A → B
    _♯ = Rec.rec

    _♯* : S.SMG*Fun*Sq (FSMG* A) B* _♯
    _♯* .S.f-𝕀 = refl
    _♯* .S.f-⊗ X Y = refl
    _♯* .S.f-α₌ X Y Z = ap _♯ (α X Y Z) -- B.α (X ♯) (Y ♯) (Z ♯)
    _♯* .S.f-α₁ X Y Z = constⱼSquare (ap _♯ (α X Y Z))
    _♯* .S.f-α₂ X Y Z = constⱼSquare (B.α (X ♯) (Y ♯) (Z ♯))
    _♯* .S.f-Λ X = Eq→Square₀₃ (lCancel (B.Λ (X ♯)))
    _♯* .S.f-ρ X = Eq→Square₀₃ (lCancel (B.ρ (X ♯)))
    _♯* .S.f-β X Y = constᵢSquare (B.β (X ♯) (Y ♯))

  _♭ : Σ (FSMG A → B) (λ g → S.SMG*Fun*Sq (FSMG* A) B* g) → (A → B)
  _♭ (g , _) = g ∘ η

  -- univ : isEquiv _♭
  -- univ = isoToIsEquiv (
  --   iso _♭ (\f → f ♯ , f ♯*)
  --     (λ _ → refl)
  --     λ { (g , g*) → let open S in
  --         ΣPathP (funExt (FSMG*Elim.elim A (λ _ → refl) (sym (g* .f-𝕀)) (λ {X = X} {Y = Y} p q → (ap₂ B._⊗_ p q ∙ sym (g* .f-⊗ X Y)))
  --           (λ {X = X} {Y = Y} {Z = Z} p q r → {!!})
  --           {!!}
  --           {!!}
  --           {!!}
  --           {!!}
  --           {!!}
  --           {!!}
  --           {!!}
  --           {!!}
  --           {!!}
  --           {!!}
  --           {!!}
  --           {!!}) ,
  --         {!!} ) }
  --   )
