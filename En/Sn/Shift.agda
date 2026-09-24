module En.Sn.Shift where

open import En.Prelude
open import En.Sn.Base

{-
Implementation with stairs inlined into the list structure
-}

infix 2 _↙_∷_

infixr 1 _↝_

StairList : Type
StairList = List (ℕ × ℕ)

_↙_∷_ : ℕ → ℕ → StairList → StairList
n ↙ a ∷ σ = (n , a) ∷ σ

data _↝_ : StairList → StairList → Type where
    ∷-cong : (σ τ : StairList) → (p : σ ↝ τ) → (k l : ℕ) → (k ↙ l ∷ σ) ↝ k ↙ l ∷ τ
    cancel : (n : ℕ) (σ : StairList) → n ↙ 1 ∷ (n ↙ 1 ∷ σ) ↝ σ
    swap :   (k l m n : ℕ) → {p : suc k < l} → (σ : StairList) → l ↙ n ∷ (k ↙ m ∷ σ) ↝ k ↙ m ∷ (l ↙ n ∷ σ)
    braid :  (n k : ℕ) → (σ : StairList) → n ↙ suc (suc k) ∷ (suc (k + n) ↙ 1 ∷ σ) ↝ k + n ↙ 1 ∷ (n ↙ suc (suc k) ∷ σ)
    join :   (n a b : ℕ) → (σ : StairList) → (n ↙ a ∷ (suc (n + a) ↙ b ∷ σ)) ↝ n ↙ a + b ∷ σ
    remove : (n : ℕ) (σ : StairList) → n ↙ 0 ∷ σ ↝ σ
