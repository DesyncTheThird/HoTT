module En.Sn.HIT where

open import En.Prelude
open import En.Sn.Base
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
    renaming ( ∥_∥₁ to ∥_∥ 
             ; ∣_∣₁ to ∣_∣
             ; squash₁ to squash 
             )
open import Cubical.HITs.PropositionalTruncation.Properties

{-
Implementation with rewriting rules inlined into the HIT
-}


curryΣ :
  {A C : Type} {B : A → Type}
  → (Σ[ a ∈ A ] B a → C) → (a : A) → B a → C
curryΣ f a b = f (a , b)

uncurryΣ :
  {A C : Type} {B : A → Type}
  → ((a : A) → B a → C) → (Σ[ a ∈ A ] B a) → C
uncurryΣ f (a , b) = f a b

∃∥∥-rec : {A : Type} {B : A → Type} → ∥ Σ[ a ∈ A ] (∥ B a ∥) ∥ → ∥ Σ[ a ∈ A ] B a ∥
∃∥∥-rec {A} {B} = rec ((isPropPropTrunc {A = Σ[ a ∈ A ] B a})) (uncurryΣ (λ a → map λ b → a , b))




data StairList : Type where
    [] : StairList
    _↙_∷_ : (n : ℕ) → (a : ℕ) → StairList → StairList
    cancel : (n : ℕ) (σ : StairList) → n ↙ 1 ∷ (n ↙ 1 ∷ σ) ≡ σ
    swap :   (k l m n : ℕ) → {p : suc k < l} → (σ : StairList) → l ↙ n ∷ (k ↙ m ∷ σ) ≡ k ↙ m ∷ (l ↙ n ∷ σ)
    braid :  (n k : ℕ) → (σ : StairList) → n ↙ suc (suc k) ∷ (suc (k + n) ↙ 1 ∷ σ) ≡ (k + n) ↙ 1 ∷ (n ↙ suc (suc k) ∷ σ)
    join :   (n a b : ℕ) → (σ : StairList) → (n ↙ a ∷ (suc (n + a) ↙ b ∷ σ)) ≡ n ↙ a + b ∷ σ
    remove : (n : ℕ) (σ : StairList) → n ↙ 0 ∷ σ ≡ σ
    is-set : isSet StairList

f : List (ℕ × ℕ) → StairList
f [] = []
f ((a , b) ∷ l) = a ↙ b ∷ f l

proj : (σ : StairList) → ∥ (Σ[ l ∈ List (ℕ × ℕ) ] f l ≡ σ) ∥
proj [] = ∣ [] , refl ∣
proj (n ↙ a ∷ σ) = ∃∥∥-rec (rec isPropPropTrunc (map (λ (τ , r) → (n , a) ∷ τ , ∣ (ap (n ↙ a ∷_) r) ∣)) ∣ proj σ ∣)
proj (cancel n σ i) = {!!}
proj (swap k l m n s i) = {!!}
proj (braid n k s i) = {!!}
proj (join n a b s i) = {!!}
proj (remove n s i) = {!!}
proj (is-set σ τ p q i j) = {!!}

-- 𝔫 : StairList → List (ℕ × ℕ)
-- 𝔫 [] = []
-- 𝔫 (n ↙ a ∷ σ) = (n , a) ∷ 𝔫 σ
-- 𝔫 (cancel n σ i) = {!.!}
-- 𝔫 (swap k l m n₁ σ i) = {!!}
-- 𝔫 (braid n₁ k σ i) = {!!}
-- 𝔫 (join n₁ a b σ i) = {!!}
-- 𝔫 (remove n₁ σ i) = {!!}
-- 𝔫 (is-set σ σ₁ x y i i₁) = {!!}


infixr 20 _⧺_

_⧺_ : StairList → StairList → StairList
[] ⧺ y = y
(n ↙ a ∷ σ) ⧺ τ = n ↙ a ∷ (σ ⧺ τ)
cancel n σ i ⧺ τ = cancel n (σ ⧺ τ) i
swap k l m n {p} σ i ⧺ τ = swap k l m n {p} (σ ⧺ τ) i
braid n k σ i ⧺ τ = braid n k (σ ⧺ τ) i
join n a b σ i ⧺ τ = join n a b (σ ⧺ τ) i
remove n σ i ⧺ τ = remove n (σ ⧺ τ) i
is-set σ σ' p q i j ⧺ τ = isSet→Square is-set (σ ⧺ τ) (σ' ⧺ τ) (ap (_⧺ τ) p) (σ ⧺ τ) (σ' ⧺ τ) (ap (_⧺ τ) q) refl refl i j

