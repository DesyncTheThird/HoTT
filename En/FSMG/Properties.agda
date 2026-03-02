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

  _♯ : (f : A → B) → (FSMG A → B)
  f ♯ =
    let module F = FSMG*Rec A f B.𝕀 B._⊗_ B.α B.Λ B.ρ B.β
                            (λ W* X* Y* Z* → B.α (W* B.⊗ X*) Y* Z* ∙ B.α W* X* (Y* B.⊗ Z*))
                            (λ W* X* Y* Z* →
                              let a = B.α (W* B.⊗ X*) Y* Z*
                                  b = B.α W* X* (Y* B.⊗ Z*)
                              in compPath→Square (ap (_∙ b) (sym (lCancel a)) ∙ sym (assoc (sym a) a b)))
                            (λ W* X* Y* Z* →
                              let c = ap (B._⊗ Z*) (B.α W* X* Y*)
                                  d = B.α W* (X* B.⊗ Y*) Z*
                                  e = ap (W* B.⊗_) (B.α X* Y* Z*)
                              in compPath→Square (ap (_∙ (sym e)) (B.⬠ W* X* Y* Z*)
                                                ∙ sym (assoc c (d ∙ e) (sym e))
                                                ∙ ap (c ∙_) (sym (assoc d e (sym e)))
                                                ∙ ap (c ∙_) (ap (d ∙_) (rCancel e))
                                                ∙ ap (c ∙_) (sym (rUnit d))))
                            {!!}
     in {!!}

  ♯-SMG*Functor : (f : A → B) → S.SMG*Functor (FSMG A) (FSMG-has-SMG*Struct A) B SMGB (f ♯)
  ♯-SMG*Functor = sorry
