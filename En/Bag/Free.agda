module En.Bag.Free where

open import En.Prelude
open import Cubical.HITs.Truncation as Trunc
open import En.FSMG
open import En.Bag.Base
open import En.Bag.Properties

private
  variable
    ℓ : Level

-- bags are the free symmetric monoidal groupoid

FSMG≃Bag : {A : Type ℓ} → isGroupoid A → FSMG A ≃ Bag A
FSMG≃Bag = sorry -- TODO: bags are the free symmetric monoidal groupoid (FSMG≃Bag)

-- 1-truncated freeness

FSMG≃TruncBag : {A : Type ℓ} → FSMG A ≃ ∥ Bag A ∥ 3
FSMG≃TruncBag {A = A} = FSMG≃FSMGTrunc A ∙ₑ FSMG≃Bag (isOfHLevelTrunc 3) ∙ₑ truncBag≃ 0 ⁻¹ₑ
