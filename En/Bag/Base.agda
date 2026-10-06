module En.Bag.Base where

open import En.Prelude
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.FinSet.Constructors
open import En.Univ.Fam
open import En.UFin.Base

private
  variable
    ℓ : Level

-- homotopy finite multisets

Bag : Type ℓ → Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
Bag = Fam UFinSub

module _ {A : Type ℓ} where

  η : A → Bag A
  η a = ⟨ 𝟙 ⟩ , (λ _ → a) , str 𝟙

  𝕀 : Bag A
  𝕀 = ⟨ 𝟘 ⟩ , (λ ()) , str 𝟘

  _⊗_ : Bag A → Bag A → Bag A
  (X ⊗ Y) .fst = ⟨ X ⟩ ⊎ ⟨ Y ⟩
  (X ⊗ Y) .snd .fst = ⊎.rec (X .snd .fst) (Y .snd .fst)
  (X ⊗ Y) .snd .snd = isFinSet⊎ (⟨ X ⟩ , X .snd .snd) (⟨ Y ⟩ , Y .snd .snd)
