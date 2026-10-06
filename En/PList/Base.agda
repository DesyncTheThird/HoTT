module En.PList.Base where

open import En.Prelude
open SumFin
open import Cubical.HITs.GroupoidQuotients.Base public
open import En.Univ.Fam
open import En.UFin.Base
open import En.Bag.Base

private
  variable
    ℓ : Level

-- finite vectors

Vec : Type ℓ → Type ℓ
Vec A = Σ[ n ∈ ℕ ] (Fin n → A)

module _ {A : Type ℓ} where

  open FamPath UFinSub A

  Vec→Bag : Vec A → Bag A
  Vec→Bag (n , v) = ⟨ FinU n ⟩ , v , str (FinU n)

  -- permutations are relabelings
  _≈_ : Vec A → Vec A → Type ℓ
  xs ≈ ys = Cover (Vec→Bag xs) (Vec→Bag ys)

  isTrans≈ : BinaryRelation.isTrans _≈_
  isTrans≈ _ _ _ = _∙ᶜ_

-- lists up to permutation as a groupoid quotient

PList : Type ℓ → Type ℓ
PList A = Vec A // isTrans≈ {A = A}
