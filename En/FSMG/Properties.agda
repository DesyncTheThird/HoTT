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
