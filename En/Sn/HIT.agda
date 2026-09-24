module En.Sn.HIT where

open import En.Prelude hiding (_++_)


{-
Implementation with rewriting rules inlined into the HIT
-}

data StairList : Type where
    [] : StairList
    _↙_∷_ : (n : ℕ) → (a : ℕ) → StairList → StairList
    cancel : (n : ℕ) (σ : StairList) → n ↙ 1 ∷ (n ↙ 1 ∷ σ) ≡ σ
    swap :   (k l m n : ℕ) → {p : suc k < l} → (σ : StairList) → l ↙ n ∷ (k ↙ m ∷ σ) ≡ k ↙ m ∷ (l ↙ n ∷ σ)
    braid :  (n k : ℕ) → (σ : StairList) → n ↙ suc (suc k) ∷ (suc (k + n) ↙ 1 ∷ σ) ≡ (k + n) ↙ 1 ∷ (n ↙ suc (suc k) ∷ σ)
    join :   (n a b : ℕ) → (σ : StairList) → (n ↙ a ∷ (suc (n + a) ↙ b ∷ σ)) ≡ n ↙ a + b ∷ σ
    remove : (n : ℕ) (σ : StairList) → n ↙ 0 ∷ σ ≡ σ
    is-set : isSet StairList

infixr 20 _++_

_++_ : StairList → StairList → StairList
[] ++ y = y
(n ↙ a ∷ σ) ++ τ = n ↙ a ∷ (σ ++ τ)
cancel n σ i ++ τ = cancel n (σ ++ τ) i
swap k l m n σ i ++ τ = swap k l m n (σ ++ τ) i
braid n k σ i ++ τ = braid n k (σ ++ τ) i
join n a b σ i ++ τ = join n a b (σ ++ τ) i
remove n σ i ++ τ = remove n (σ ++ τ) i
is-set σ σ' p q i j ++ τ = isSet→Square is-set (σ ++ τ) (σ' ++ τ) (ap (_++ τ) p) (σ ++ τ) (σ' ++ τ) (ap (_++ τ) q) refl refl i j


