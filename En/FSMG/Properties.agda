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
FSMG-has-SMG*Struct A .S.▽ X Y = Square→Triangle₃ (▽ X Y)
FSMG-has-SMG*Struct A .S.⬠ W X Y Z =
  let ⬠₌ = ⬠₌ W X Y Z
      ⬠₁ = Square→Triangle₂ (⬠₁ W X Y Z)
      ⬠₂ = Square→compPath (⬠₂ W X Y Z)
      a = α (W ⊗ X) Y Z
      b = α W X (Y ⊗ Z)
      c = ap (_⊗ Z) (α W X Y)
      d = α W (X ⊗ Y) Z
      e = ap (W ⊗_) (α X Y Z)
      u : a ∙ b ≡ ⬠₌
      u = ap (a ∙_) ⬠₁ ∙ assoc a (sym a) ⬠₌ ∙ ap (_∙ ⬠₌) (rCancel a) ∙ sym (lUnit ⬠₌)
      v : ⬠₌ ≡ c ∙ (d ∙ e)
      v = rUnit ⬠₌ ∙ ap (⬠₌ ∙_) (sym (lCancel e)) ∙ assoc ⬠₌ (sym e) e ∙ ap (_∙ e) ⬠₂ ∙ sym (assoc c d e)
  in u ∙ v
FSMG-has-SMG*Struct A .S.⬡ X Y Z =
  let ⬡₌ = ⬡₌ X Y Z
      ⬡₁ = Square→compPath (⬡₁ X Y Z)
      ⬡₂ = Square→compPath (⬡₂ X Y Z)
      a = α X Y Z
      b = β X (Y ⊗ Z)
      c = α Y Z X
      d = ap (_⊗ Z) (β X Y)
      e = α Y X Z
      f = ap (Y ⊗_) (β X Z)
      u : a ∙ b ∙ c ≡ ⬡₌
      u = ap (a ∙_) ⬡₁ ∙ assoc a (sym a) ⬡₌ ∙ ap (_∙ ⬡₌) (rCancel a) ∙ sym (lUnit ⬡₌)
      v : ⬡₌ ≡ d ∙ e ∙ f
      v = rUnit ⬡₌ ∙ ap (⬡₌ ∙_) (sym (lCancel f)) ∙ assoc ⬡₌ (sym f) f ∙ ap (_∙ f) ⬡₂ ∙ sym (assoc d e f)
  in u ∙ v
FSMG-has-SMG*Struct A .S.β² X Y =
  ap (_∙ β Y X) (β² X Y) ∙ lCancel (β Y X)
FSMG-has-SMG*Struct A .S.is-groupoid = is-groupoid
