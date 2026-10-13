module En.Sn.Base where

open import En.Prelude
open FN

infixr 30 _::_

-- Coxeter presentation of the symmetric group on suc n points

data Sym (n : ℕ) : Type where
  nil : Sym n
  _::_ : Fin n → Sym n → Sym n
  cancel : (k : Fin n) (σ : Sym n) → k :: k :: σ ≡ σ
  comm : (k l : Fin n) → suc (k .fst) <ᵗ l .fst → (σ : Sym n) → l :: k :: σ ≡ k :: l :: σ
  braid : (k l : Fin n) → suc (k .fst) ≡ l .fst → (σ : Sym n) → l :: k :: l :: σ ≡ k :: l :: k :: σ
  trunc : isSet (Sym n)

module SymElimSet {ℓ} {n : ℕ} (P : Sym n → Type ℓ)
  (nil* : P nil)
  (_::*_ : (k : Fin n) {σ : Sym n} → P σ → P (k :: σ))
  (cancel* : (k : Fin n) {σ : Sym n} (σ* : P σ)
    → PathP (λ i → P (cancel k σ i)) (k ::* (k ::* σ*)) σ*)
  (comm* : (k l : Fin n) (p : suc (k .fst) <ᵗ l .fst) {σ : Sym n} (σ* : P σ)
    → PathP (λ i → P (comm k l p σ i)) (l ::* (k ::* σ*)) (k ::* (l ::* σ*)))
  (braid* : (k l : Fin n) (p : suc (k .fst) ≡ l .fst) {σ : Sym n} (σ* : P σ)
    → PathP (λ i → P (braid k l p σ i)) (l ::* (k ::* (l ::* σ*))) (k ::* (l ::* (k ::* σ*))))
  (isSet* : (σ : Sym n) → isSet (P σ))
  where

  elim : (σ : Sym n) → P σ
  elim nil = nil*
  elim (k :: σ) = k ::* elim σ
  elim (cancel k σ i) = cancel* k (elim σ) i
  elim (comm k l p σ i) = comm* k l p (elim σ) i
  elim (braid k l p σ i) = braid* k l p (elim σ) i
  elim (trunc σ τ p q i j) =
    isOfHLevel→isOfHLevelDep 2 isSet*
      (elim σ) (elim τ) (λ k → elim (p k)) (λ k → elim (q k)) (trunc σ τ p q) i j

module SymElimProp {ℓ} {n : ℕ} (P : Sym n → Type ℓ)
  (nil* : P nil)
  (_::*_ : (k : Fin n) {σ : Sym n} → P σ → P (k :: σ))
  (isProp* : (σ : Sym n) → isProp (P σ))
  where

  elim : (σ : Sym n) → P σ
  elim =
    SymElimSet.elim P
      nil*
      _::*_
      (λ k {σ} _ → isProp→PathP (λ i → isProp* (cancel k σ i)) _ _)
      (λ k l p {σ} _ → isProp→PathP (λ i → isProp* (comm k l p σ i)) _ _)
      (λ k l p {σ} _ → isProp→PathP (λ i → isProp* (braid k l p σ i)) _ _)
      (λ σ → isProp→isSet (isProp* σ))
