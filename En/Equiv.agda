module En.Equiv where

open import En.Prelude
open import Cubical.Functions.Surjection
open import En.Univ.Fam
open import En.BAut
open import En.UFin.Base
open import En.UFin.Properties using ( UFin≃ΣBAut )
open import En.HigherGroup
open import En.FSMG.Base using ( FSMG )
open import En.SList.Base
open import En.SList.Sym
open import En.SList.Concrete
open import En.Sn.Concrete
open import En.PList.Base
open import En.PList.Properties
open import En.Bag.Base

-- free symmetric monoidal groupoids are swap lists

FSMG≃SList : {A : Type ℓ} → FSMG A ≃ SList A
FSMG≃SList = sorry
  -- TODO: FSMGs are swap lists (FSMG≃SList)
  --  free symmetric monoidal groupoids are swap lists; they both satisfy the same universal property

-- external proof using groupoid quotients

module Abstract {A : Type ℓ} where

  -- swap lists are vectors up to the coxeter groups

  SList≃Vec//𝔖 : SList A ≃ Vec//𝔖 A
  SList≃Vec//𝔖 = sorry
    -- TODO: swap lists as vectors up to 𝔖 (SList≃Vec//𝔖)
    --  cells of SList go to constructors of Sym; maps by groupoid-quotient and SList recursion

  -- change of group from coxeter presentation to permutations

  Vec//𝔖≃Vec//Aut : Vec//𝔖 A ≃ Vec//Aut A
  Vec//𝔖≃Vec//Aut = sorry
    -- TODO: change of group 𝔖 to Aut (Vec//𝔖≃Vec//Aut)
    --  WreathGroupoid≃ along 𝔖≃Aut, from completeness of the coxeter presentation

  -- vectors up to automorphisms are lists up to permutation

  Vec//Aut≃PList : Vec//Aut A ≃ PList A
  Vec//Aut≃PList = sorry
    -- TODO: regroup PList by length (Vec//Aut≃PList)
    --  matching lengths with Fin≃→≡

  -- lists up to permutation are bags

  PList≃Bag : isGroupoid A → PList A ≃ Bag A
  PList≃Bag isGroupoidA =
    PList→Bag isGroupoidA , isEmbedding×isSurjection→isEquiv (isEmbeddingPList→Bag isGroupoidA , isSurjectionPList→Bag isGroupoidA)

  -- composites

  SList≃PList : SList A ≃ PList A
  SList≃PList =
    SList A
      ≃⟨ SList≃Vec//𝔖 ⟩
    Vec//𝔖 A
      ≃⟨ Vec//𝔖≃Vec//Aut ⟩
    Vec//Aut A
      ≃⟨ Vec//Aut≃PList ⟩
    PList A
      ■

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

-- internal proof using actions of concrete groups

module Concrete {A : Type ℓ} where

  -- labellings of shapes of the automorphism groups

  BagBAut : Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
  BagBAut = Σ[ m ∈ ℕ ] A ≀ ElBAut {T = FS.Fin m}

    -- change of group from coxeter presentation to permutations

  Bag𝔖≃BagBAut : Bag𝔖 A ≃ BagBAut
  Bag𝔖≃BagBAut = Σ-cong-equiv-snd λ m → ≀-cong (B𝔖≃BAut m .fst) ElBAut

  -- finite labelled types are bags

  BagBAut≃Bag : BagBAut ≃ Bag A
  BagBAut≃Bag =
    BagBAut
      ≃⟨ Σ-assoc-≃ ⁻¹ₑ ⟩
    Σ[ (m , X) ∈ Σ[ m ∈ ℕ ] BAut (FS.Fin m) ] (⟨ X ⟩ → A)
      ≃⟨ Σ-cong-equiv-fst (UFin≃ΣBAut ⁻¹ₑ) ⟩
    Σ[ X ∈ UFin ] (⟨ X ⟩ → A)
      ≃⟨ FamPath.Fam≃Σ UFinSub A ⁻¹ₑ ⟩
    Bag A
      ■

  -- composites

  SList≃Bag : isGroupoid A → SList A ≃ Bag A
  SList≃Bag isGroupoidA =
    SList A
      ≃⟨ SList≃Bag𝔖 isGroupoidA ⟩
    Bag𝔖 A
      ≃⟨ Bag𝔖≃BagBAut ⟩
    BagBAut
      ≃⟨ BagBAut≃Bag ⟩
    Bag A
      ■

  FSMG≃Bag : isGroupoid A → FSMG A ≃ Bag A
  FSMG≃Bag isGroupoidA = FSMG≃SList ∙ₑ SList≃Bag isGroupoidA
