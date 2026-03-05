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



FSMG-has-SMG*Struct*Square : ∀ {ℓ} (A : Type ℓ) → S.SMG*Struct*Square (FSMG A)
FSMG-has-SMG*Struct*Square A .S.𝕀 = 𝕀
FSMG-has-SMG*Struct*Square A .S._⊗_ = _⊗_
FSMG-has-SMG*Struct*Square A .S.α = α
FSMG-has-SMG*Struct*Square A .S.Λ = Λ
FSMG-has-SMG*Struct*Square A .S.ρ = ρ
FSMG-has-SMG*Struct*Square A .S.β = β
FSMG-has-SMG*Struct*Square A .S.▽ = ▽
FSMG-has-SMG*Struct*Square A .S.⬠₌ = ⬠₌
FSMG-has-SMG*Struct*Square A .S.⬠₁ = ⬠₁
FSMG-has-SMG*Struct*Square A .S.⬠₂ = ⬠₂
FSMG-has-SMG*Struct*Square A .S.⬡₌ = ⬡₌
FSMG-has-SMG*Struct*Square A .S.⬡₁ = ⬡₁
FSMG-has-SMG*Struct*Square A .S.⬡₂ = ⬡₂
FSMG-has-SMG*Struct*Square A .S.β² = β²
FSMG-has-SMG*Struct*Square A .S.is-groupoid = is-groupoid

module Univ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) (SMGB : S.SMG*Struct*Square B) where

  module B = S.SMG*Struct*Square SMGB

  module _ (f : A → B) where

    module Rec = FSMG*Rec A f B.𝕀 B._⊗_ B.α B.Λ B.ρ B.β
        B.▽ B.⬠₌ B.⬠₁ B.⬠₂ B.⬡₌ B.⬡₁ B.⬡₂ B.β² B.is-groupoid

    _♯ : FSMG A → B
    _♯ = Rec.f

    ♯-SMG*Functor*Square : S.SMG*Functor*Square (FSMG A) (FSMG-has-SMG*Struct*Square A) B SMGB _♯
    ♯-SMG*Functor*Square .S.f-𝕀 = refl
    ♯-SMG*Functor*Square .S.f-⊗ X Y = refl
    ♯-SMG*Functor*Square .S.f-α₌ X Y Z = ap _♯ (α X Y Z) -- B.α (X ♯) (Y ♯) (Z ♯)
    ♯-SMG*Functor*Square .S.f-α₁ X Y Z = constⱼSquare (ap _♯ (α X Y Z))
    ♯-SMG*Functor*Square .S.f-α₂ X Y Z = constⱼSquare (B.α (X ♯) (Y ♯) (Z ♯))
    ♯-SMG*Functor*Square .S.f-Λ X = Eq→Square₀₃ (lCancel (B.Λ (X ♯)))
    ♯-SMG*Functor*Square .S.f-ρ X = Eq→Square₀₃ (lCancel (B.ρ (X ♯)))
    ♯-SMG*Functor*Square .S.f-β X Y = constᵢSquare (B.β (X ♯) (Y ♯))

    _♭ : (g : FSMG A → B) → S.SMG*Functor*Square (FSMG A) (FSMG-has-SMG*Struct*Square A) B SMGB g → (A → B)
    _♭ g _ = g ∘ η
