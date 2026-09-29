module En.Sn.Quotient where

open import En.Prelude
open import En.Sn.Base
open import Cubical.HITs.SetQuotients
open import Cubical.Data.List hiding ( elim ; rec ) public

{-
Implementation as a set quotient
-}

infixr 10 _↙_

_↙_ : ℕ → ℕ → List ℕ
n ↙ zero = []
n ↙ suc k = (k + n) ∷ n ↙ k

infixr 4 _↝_

data _↝_ : List ℕ → List ℕ → Type where
    ∷-cong : (σ τ : List ℕ) → (p : σ ↝ τ) → (k : ℕ) → k ∷ σ ↝ k ∷ τ
    cancel : (k : ℕ) (σ : List ℕ) → k ∷ k ∷ σ ↝ σ
    swap :   (k l : ℕ) → {p : suc k < l} → (σ : List ℕ) → l ∷ k ∷ σ ↝ k ∷ l ∷ σ
    ↙braid : (n k : ℕ) → (σ : List ℕ) →
      (n ↙ suc (suc k)) ++ (suc (suc (k + n)) ∷ σ) ↝ k + n ∷ n ↙ suc (suc k) ++ σ

_↝ᶠ_ : {n : ℕ} → List (Fin n) → List (Fin n) → Type
σ ↝ᶠ τ = (map fst σ) ↝ (map fst τ)

-- data _* {ℓ : Level} {A : Type ℓ} (R : Rel A A ℓ) : Rel A A ℓ where
--     reflex : (w : A) → (R *) w w
--     trans : ∀ {u} v {w} → R u v → (R *) v w → (R *) u w




qSym₂ : (n : SLevel) → Type₀
qSym₂ n = List (Fin n) / _↝ᶠ_ {n}


