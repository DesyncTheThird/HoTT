module En.Sn.HIT where

open import En.Prelude
open Finℕ
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
    remove : (n : ℕ) (σ : StairList) → n ↙ 0 ∷ σ ≡ σ
    cancel : (n : ℕ) (σ : StairList) → n ↙ 1 ∷ (n ↙ 1 ∷ σ) ≡ σ
    join :   (n a b : ℕ) → (σ : StairList) → (n ↙ a ∷ (suc (n + a) ↙ b ∷ σ)) ≡ n ↙ a + b ∷ σ
    
    swap :   (k l m n : ℕ) → {p : suc k < l} → (σ : StairList) → l ↙ n ∷ (k ↙ m ∷ σ) ≡ k ↙ m ∷ (l ↙ n ∷ σ)
    braid :  (n k : ℕ) → (σ : StairList) → n ↙ suc (suc k) ∷ (suc (k + n) ↙ 1 ∷ σ) ≡ (k + n) ↙ 1 ∷ (n ↙ suc (suc k) ∷ σ)
    
    is-set : isSet StairList

f : List (ℕ × ℕ) → StairList
f [] = []
f ((a , b) ∷ l) = a ↙ b ∷ f l

proj-fib : StairList → Type
proj-fib σ = ∥ (Σ[ l ∈ List (ℕ × ℕ) ] f l ≡ σ) ∥

proj∷ : (n a : ℕ) {σ : StairList} → proj-fib σ → proj-fib (n ↙ a ∷ σ)
proj∷ n a x = ∃∥∥-rec (rec isPropPropTrunc (map (λ (τ , r) → (n , a) ∷ τ , ∣ (ap (n ↙ a ∷_) r) ∣)) ∣ x ∣)

proj-path : {σ τ : StairList} (p : σ ≡ τ) (x : proj-fib σ) (y : proj-fib τ) → PathP (λ i → proj-fib (p i)) x y
proj-path p x y = isOfHLevel→isOfHLevelDep 1 (λ _ → squash) x y p

proj : (σ : StairList) → proj-fib σ
proj [] = ∣ [] , refl ∣
proj (n ↙ a ∷ σ) = proj∷ n a (proj σ)
proj (cancel n σ i) = proj-path (cancel n σ) (proj∷ n 1 (proj∷ n 1 (proj σ))) (proj σ) i
proj (swap k l m n {p} s i) = proj-path (swap k l m n {p} s) (proj∷ l n (proj∷ k m (proj s))) (proj∷ k m (proj∷ l n (proj s))) i
proj (braid n k s i) = proj-path (braid n k s) (proj∷ n (suc (suc k)) (proj∷ (suc (k + n)) 1 (proj s))) (proj∷ (k + n) 1 (proj∷ n (suc (suc k)) (proj s))) i
proj (join n a b s i) = proj-path (join n a b s) (proj∷ n a (proj∷ (suc (n + a)) b (proj s))) (proj∷ n (a + b) (proj s)) i
proj (remove n s i) = proj-path (remove n s) (proj∷ n 0 (proj s)) (proj s) i
proj (is-set σ τ p q i j) = isOfHLevel→isOfHLevelDep 2 {B = proj-fib} (λ _ → isProp→isSet squash) (proj σ) (proj τ) (λ k → proj (p k)) (λ k → proj (q k)) (is-set σ τ p q) i j

-- 𝔫 : StairList → List (ℕ × ℕ)
-- 𝔫 [] = []
-- 𝔫 (n ↙ zero ∷ σ) = 𝔫 σ
-- 𝔫 (n ↙ suc a ∷ σ) = {!!}
-- 𝔫 (n ↙ a ∷ cancel n₁ σ i) = {!!}
-- 𝔫 (n ↙ a ∷ swap k l m n₁ σ i) = {!!}
-- 𝔫 (n ↙ a ∷ braid n₁ k σ i) = {!!}
-- 𝔫 (n ↙ a ∷ join n₁ a₁ b σ i) = {!!}
-- 𝔫 (n ↙ a ∷ remove n₁ σ i) = {!!}
-- 𝔫 (n ↙ a ∷ is-set σ σ₁ x y i i₁) = {!!}
-- 𝔫 (cancel n σ i) = {!!}
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
