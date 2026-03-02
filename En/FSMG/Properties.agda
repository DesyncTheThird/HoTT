module En.FSMG.Properties where

open import En.Prelude
open import En.FSMG.Base
import En.SMG as S

FSMG-has-SMG*Struct : ∀ {ℓ} (A : Type ℓ) → S.SMG*Struct (FSMG A)
FSMG-has-SMG*Struct A .S.𝕀 = 𝕀
FSMG-has-SMG*Struct A .S._⊗_ = _⊗_
FSMG-has-SMG*Struct A .S.α = α
FSMG-has-SMG*Struct A .S.Λ = Λ
FSMG-has-SMG*Struct A .S.ρ = ρ
FSMG-has-SMG*Struct A .S.β = β
FSMG-has-SMG*Struct A .S.▽ X Y = Triangle→compPath₃ (▽ X Y)
FSMG-has-SMG*Struct A .S.⬠ W X Y Z = Pentagon→compPath (⬠₌ W X Y Z) (⬠₁ W X Y Z) (⬠₂ W X Y Z)
FSMG-has-SMG*Struct A .S.⬡ X Y Z = Hexagon→compPath (⬡₌ X Y Z) (⬡₁ X Y Z) (⬡₂ X Y Z)
FSMG-has-SMG*Struct A .S.β² X Y = ap (_∙ β Y X) (β² X Y) ∙ lCancel (β Y X)
FSMG-has-SMG*Struct A .S.is-groupoid = is-groupoid

module Univ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) (SMGB : S.SMG*Struct B) where

  module B = S.SMG*Struct SMGB

  module _ (f : A → B) where

    module F = FSMG*Rec A f B.𝕀 B._⊗_ B.α B.Λ B.ρ B.β
                            (λ W* X* Y* Z* → B.α (W* B.⊗ X*) Y* Z* ∙ B.α W* X* (Y* B.⊗ Z*))
                            (λ W* X* Y* Z* → compPath→Pentagon (B.⬠ W* X* Y* Z*) .snd .fst)
                            (λ W* X* Y* Z* → compPath→Pentagon (B.⬠ W* X* Y* Z*) .snd .snd)
                            (λ X* Y* → compPath→Triangle₃ (B.▽ X* Y*))
                            (λ X* Y* Z* → compPath→Hexagon (B.⬡ X* Y* Z*) .fst)
                            (λ X* Y* Z* → compPath→Hexagon (B.⬡ X* Y* Z*) .snd .fst)
                            (λ X* Y* Z* → compPath→Hexagon (B.⬡ X* Y* Z*) .snd .snd)
                            (λ X* Y* → Eq→Square₂₃ (B.β² X* Y*))
                            B.is-groupoid


    _♯ : (FSMG A → B)
    _♯ = F.f

    ♯-SMG*Functor : S.SMG*Functor (FSMG A) (FSMG-has-SMG*Struct A) B SMGB (_♯)
    ♯-SMG*Functor .S.f-𝕀 = refl
    ♯-SMG*Functor .S.f-⊗ X Y = refl
    ♯-SMG*Functor .S.f-α X Y Z = {!   !}
    ♯-SMG*Functor .S.f-Λ X = {!   !}
    ♯-SMG*Functor .S.f-ρ X = {!   !}
    ♯-SMG*Functor .S.f-β X Y = {!   !}
