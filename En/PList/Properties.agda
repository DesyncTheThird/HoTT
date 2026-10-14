module En.PList.Properties where

open import En.Prelude
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import En.Bag.Base
open import En.Bag.Properties
open import En.PList.Base
open import En.GroupoidQuotients.Properties
open import En.GroupAction.Base

-- vectors up to automorphisms of their positions

Vec//Aut : Type ℓ → Type ℓ
Vec//Aut A = Σ[ m ∈ ℕ ] A ≀ autAction (FS.Fin m) FS.isSetFin

module _ {A : Type ℓ} where

  isGroupoidPList : isGroupoid (PList A)
  isGroupoidPList = squash//

  -- every bag is merely a vector
  isSurjectionVec→Bag : isSurjection (Vec→Bag {A = A})
  isSurjectionVec→Bag (T , v , n , t) =
    PT.map (λ e → (n , v ∘ <– e) , decode _ _ (cover (invEquiv e) λ _ → refl)) t

  module _ (isGroupoidA : isGroupoid A) where

    private
      module K = KernelPair isTrans≈ (isGroupoidBag isGroupoidA) Vec→Bag (Path≃Cover _ _ ⁻¹ₑ) decode-∙

    PList→Bag : PList A → Bag A
    PList→Bag = K.rec//

    isEmbeddingPList→Bag : isEmbedding PList→Bag
    isEmbeddingPList→Bag = K.isEmbeddingRec//

    isSurjectionPList→Bag : isSurjection PList→Bag
    isSurjectionPList→Bag = K.isSurjectionRec// isSurjectionVec→Bag
