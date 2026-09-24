module En.Sn.Quotient where

open import En.Prelude
open import En.Sn.Base
open import Cubical.HITs.SetQuotients public

{-
Implementation as a set quotient
-}



infixr 4 _↝_

data _↝_ : List ℕ → List ℕ → Type where
    ∷-cong : (σ τ : List ℕ) → (p : σ ↝ τ) → (k : ℕ) → k ∷ σ ↝ k ∷ τ
    cancel : (k : ℕ) (σ : List ℕ) → k ∷ k ∷ σ ↝ σ
    swap :   (k l : ℕ) → {p : suc k < l} → (σ : List ℕ) → l ∷ k ∷ σ ↝ k ∷ l ∷ σ
    ↙braid : (n k : ℕ) → (σ : List ℕ) →
      (n ↙ suc (suc k)) ++ (suc (suc (k + n)) ∷ σ) ↝ k + n ∷ n ↙ suc (suc k) ++ σ

_↝ᶠ_ : {n : ℕ} → List (Fin n) → List (Fin n) → Type
σ ↝ᶠ τ = (map fst σ) ↝ (map fst τ)

qSym₂ : (n : SLevel) → Type₀
qSym₂ n = List (Fin n) / _↝ᶠ_ {n}
