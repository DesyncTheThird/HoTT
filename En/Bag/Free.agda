module En.Bag.Free where

open import En.Prelude
open import Cubical.HITs.Truncation as Trunc
open import En.FSMG
open import En.Bag.Base
open import En.Bag.Properties
import En.Equiv
open En.Equiv.Concrete using ( FSMG≃Bag ) public

-- 1-truncated freeness

FSMG≃TruncBag : {A : Type ℓ} → FSMG A ≃ ∥ Bag A ∥ 3
FSMG≃TruncBag {A = A} = FSMG≃FSMGTrunc A ∙ₑ FSMG≃Bag (isOfHLevelTrunc 3) ∙ₑ truncBag≃ 0 ⁻¹ₑ
