module En.Equiv where

open import En.Prelude
open import Cubical.Functions.Surjection
open import En.FSMG.Base using ( FSMG )
open import En.SList.Base
open import En.PList.Base
open import En.PList.Properties
open import En.Bag.Base

module _ {A : Type ℓ} where

  -- free symmetric monoidal groupoids are swap lists

  FSMG≃SList : FSMG A ≃ SList A
  FSMG≃SList = sorry
    -- TODO: FSMGs are swap lists (FSMG≃SList)
    --  free symmetric monoidal groupoids are swap lists; FSMG.Univ into SList* one way and SListElim the other

  -- swap lists are lists up to permutation

  SList≃PList : SList A ≃ PList A
  SList≃PList = sorry
    -- TODO: swap lists are permutation lists (SList≃PList)
    --  swap lists are lists up to permutation; via vectors up to the coxeter groups and up to automorphisms

  -- lists up to permutation are bags

  PList≃Bag : isGroupoid A → PList A ≃ Bag A
  PList≃Bag isGroupoidA =
    PList→Bag isGroupoidA , isEmbedding×isSurjection→isEquiv (isEmbeddingPList→Bag isGroupoidA , isSurjectionPList→Bag isGroupoidA)

  -- composites

  SList≃Bag : isGroupoid A → SList A ≃ Bag A
  SList≃Bag isGroupoidA = SList≃PList ∙ₑ PList≃Bag isGroupoidA

  FSMG≃Bag : isGroupoid A → FSMG A ≃ Bag A
  FSMG≃Bag isGroupoidA =
    FSMG A
      ≃⟨ FSMG≃SList ⟩
    SList A
      ≃⟨ SList≃PList ⟩
    PList A
      ≃⟨ PList≃Bag isGroupoidA ⟩
    Bag A
      ■
