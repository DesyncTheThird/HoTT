module En.PList.Properties where

open import En.Prelude
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT
open import En.Bag
open import En.PList.Base
open import En.GroupoidQuotients.Properties

private
  variable
    ℓ : Level

module _ {A : Type ℓ} where

  isGroupoidPList : isGroupoid (PList A)
  isGroupoidPList = squash//

  -- every bag is merely a vector
  isSurjectionVec→Bag : isSurjection (Vec→Bag {A = A})
  isSurjectionVec→Bag (T , v , n , t) =
    PT.map (λ e → (n , v ∘ invEq e) , decode _ _ (cover (invEquiv e) λ _ → refl)) t

  module _ (isGroupoidA : isGroupoid A) where

    private
      module K = KernelPair isTrans≈ (isGroupoidBag isGroupoidA) Vec→Bag (Path≃Cover _ _ ⁻¹ₑ) decode-∙

    PList→Bag : PList A → Bag A
    PList→Bag = K.rec//

    PList≃Bag : PList A ≃ Bag A
    PList≃Bag = K.quotSurjectionEquiv isSurjectionVec→Bag
