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

-- data _↝_ : {n m : ℕ} → List (Fin (suc n)) → List (Fin (suc m)) → Type₀ where
--     ∷-cong : {n : ℕ} (σ τ : List (Fin (suc n))) → (p : σ ↝ τ) → (k : Fin (suc n)) → (k ∷ σ) ↝ k ∷ τ
--     cancel : {n : ℕ} (k : Fin (suc n)) (σ : List (Fin (suc n))) → k ∷ k ∷ σ ↝ σ
--     swap :   {n : ℕ} (k@(a , _) l(b , _) : Fin (suc n)) → {p : suc a < b} → (σ : List (Fin (suc n))) → l ∷ k ∷ σ ↝ k ∷ l ∷ σ
--     ↙braid : {n : ℕ} (k@(a , p) : Fin n) → (σ : List (Fin (suc (suc (a + n))))) →
--       (n ↙ suc (suc a)) ++ (fsuc ((a + n , <ᵗsucm {m = a + n})) ∷ σ)
--         ↝ (_+ᶠ_ {n = {!suc a!}} {m = suc n} (a , <ᵗsucm {a}) (n , <ᵗsucm {n})) ∷ n ↙ suc (suc a) ++ σ

-- test : {n : ℕ} → (k@( a , b ) : Fin n) → (σ : List (Fin (suc (suc (a + n))))) →
--     (n ↙ suc (suc a)) ++ (fsuc ((a + n , <ᵗsucm {m = a + n})) ∷ σ)
--       ↝ ((a , <ᵗ-trans {n = a} {m = suc (a + n)} {k = suc (suc (a + n))} (tpt (λ x → x) (ap (λ z → a <ᵗ suc z) (+-comm n a)) ((<ᵗ-+ {n = a} {k = n}))) (<ᵗsucm {m = suc (a + n)}))) ∷ n ↙ suc (suc a) ++ σ
-- test = {!!}

_↝ᶠ_ : {n : ℕ} → List (Fin n) → List (Fin n) → Type
σ ↝ᶠ τ = (map fst σ) ↝ (map fst τ)

-- data _* {ℓ : Level} {A : Type ℓ} (R : Rel A A ℓ) : Rel A A ℓ where
--     reflex : (w : A) → (R *) w w
--     trans : ∀ {u} v {w} → R u v → (R *) v w → (R *) u w

qSym₂ : (n : SLevel) → Type₀
qSym₂ n = List (Fin n) / _↝ᶠ_ {n}








