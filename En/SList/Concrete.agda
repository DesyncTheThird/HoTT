module En.SList.Concrete where

open import En.Prelude hiding ( _·_ )
open import En.HigherGroup
open import En.SList.Base
open import En.Sn.Concrete

-- labellings of shapes of the concrete symmetric groups

Bag𝔖 : Type ℓ → Type ℓ
Bag𝔖 A = Σ[ m ∈ ℕ ] A ≀ El𝔖 m

module _ {A : Type ℓ} where

  isGroupoidBag𝔖 : isGroupoid A → isGroupoid (Bag𝔖 A)
  isGroupoidBag𝔖 isGroupoidA =
    isOfHLevelΣ 3 (isSet→isGroupoid isSetℕ) λ m →
      isOfHLevelΣ 3 (B𝔖 m .snd) λ _ → isOfHLevelΠ 3 λ _ → isGroupoidA

  -- swap lists are labelled shapes

  SList≃Bag𝔖 : isGroupoid A → SList A ≃ Bag𝔖 A
  SList≃Bag𝔖 = sorry
    -- TODO: swap lists are labelled shapes (SList≃Bag𝔖)
    --  SListElim one way, BSymElim the other
