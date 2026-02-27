module En.FSMG.Properties where

open import En.Prelude
import En.FSMG.Base as F
open import En.SMG

FSMG-has-SMG*Struct : ∀ {ℓ} (A : Type ℓ) → SMG*Struct (F.FSMG A)
FSMG-has-SMG*Struct A .𝕀 = F.𝕀
FSMG-has-SMG*Struct A ._⊗_ = F._⊗_
FSMG-has-SMG*Struct A .α = F.α
FSMG-has-SMG*Struct A .Λ = F.Λ
FSMG-has-SMG*Struct A .ρ = F.ρ
FSMG-has-SMG*Struct A .β = F.β
FSMG-has-SMG*Struct A .▽ X Y = Square→Triangle (F.▽ X Y)
FSMG-has-SMG*Struct A .⬠ W X Y Z =
  Square→Triangle {!F.⬠₁ W X Y Z !} ∙ {!!}
FSMG-has-SMG*Struct A .⬡ = {!!}
FSMG-has-SMG*Struct A .β² = {!!}
FSMG-has-SMG*Struct A .is-groupoid = {!!}
