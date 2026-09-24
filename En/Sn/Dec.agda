module En.Sn.Dec where

open import En.Prelude
open import En.Sn.Base
open import Cubical.Data.Empty as ⊥

{-
Implementation using decidability
-}

infixr 30 _::_

data Sym₂ (n : SLevel) : Type₀ where
    nil : Sym₂ n
    _::_ : (k : Fin (suc n)) → Sym₂ n → Sym₂ n

    cancel : (k : Fin (suc n)) (σ : Sym₂ n) → k :: k :: σ ≡ σ
    swap : (k l : Fin (suc n)) → {p : suc (k .fst) < l .fst} → (σ : Sym₂ n) → l :: k :: σ ≡ k :: l :: σ
    braid : (k : Fin n) → (σ : Sym₂ n)
        → fsuc k :: finj k :: fsuc k :: σ ≡ finj k :: fsuc k :: finj k :: σ


swapAt≠ : (n : SLevel) (k : Fin (suc n)) → (l : Fin (suc (suc n))) → Fin (suc (suc n))
swapAt≠ n (k , ϕ) (l , ψ) =
    decRec
        (λ q → (k , <ᵗ-trans-suc {n = k} {m = suc n} ϕ))
        (λ ¬q → (l , ψ))
        (discreteℕ (suc k) l)

swapAt≠-=β : (n : SLevel) (fk@(k , ϕ) : Fin (suc n)) → (fl@(l , ψ) : Fin (suc (suc n))) → (p : suc k ≡ l) → swapAt≠ n fk fl ≡ (k , <ᵗ-trans-suc {n = k} {m = suc n} ϕ)
swapAt≠-=β n (k , ϕ) (l , ψ) p = decRecYes (isSetℕ (suc k) l) p (discreteℕ (suc k) l)

swapAt≠-≠β : (n : SLevel) (fk@(k , ϕ) : Fin (suc n)) → (fl@(l , ψ) : Fin (suc (suc n))) → (¬p : ¬ (suc k ≡ l)) → swapAt≠ n fk fl ≡ fl
swapAt≠-≠β n (k , ϕ) (l , ψ) ¬p = decRecNo (isSetℕ (suc k) l) ¬p (discreteℕ (suc k) l)

swapAt : (n : SLevel) → (k : Fin (suc n)) → Fin (suc (suc n)) → Fin (suc (suc n))
swapAt n (k , ϕ) (l , ψ) =
    decRec
        (λ p → (suc k , ϕ))
        (λ _ → swapAt≠ n (k , ϕ) (l , ψ))
        (discreteℕ k l)

swapAt=-=β : (n : SLevel) (k : Fin (suc n)) → (l : Fin (suc (suc n))) → (p : k .fst ≡ l .fst) → swapAt n k l ≡ fsuc k
swapAt=-=β n (k , ϕ) (l , ψ) p = decRecYes (isSetℕ k l) p (discreteℕ k l)

swapAt=-≠β : (n : SLevel) (fk@(k , ϕ) : Fin (suc n)) → (fl@(l , ψ) : Fin (suc (suc n))) → (p : k ≡ l) (¬q : ¬(k ≡ l)) → swapAt n fk fl ≡ swapAt≠ n fk fl
swapAt=-≠β n (k , ϕ) (l , ψ) p ¬q = decRecNo (isSetℕ k l) ¬q (discreteℕ k l)


_ : swapAt 5 2 3 ≡ 2
_ = refl

swapAt-suc : (n : SLevel) (k : Fin (suc n)) → swapAt n k (fsuc k) ≡ finj k
swapAt-suc n fk@(k , ϕ) with discreteℕ k (suc k) | discreteℕ (suc k) (suc k)
... | yes p | yes q = ⊥.rec (sucn≠n (sym p))
... | yes p | no ¬q = ⊥.rec (sucn≠n (sym p))
... | no ¬p | yes q = refl

... | no ¬p | no ¬q = ⊥.rec (¬q refl)
swapAt-eq : (n : SLevel) (k : Fin (suc n)) → swapAt n k (finj k) ≡ fsuc k
swapAt-eq n fk@(k , ϕ) with discreteℕ k k | discreteℕ (suc k) k
... | yes p | yes q = refl
... | yes p | no ¬q = refl
... | no ¬p | yes q = ⊥.rec (¬p refl)
... | no ¬p | no ¬q = ⊥.rec (¬p refl)


swapAt² : (n : SLevel) (k : Fin (suc n)) → (l : Fin (suc (suc n))) → swapAt n k (swapAt n k l) ≡ l
swapAt² n fk@(k , ϕ) fl@(l , ψ) = {!!}


-- swapAt n (k , ϕ) (swapAt n (k , ϕ) (l , ψ)) ≡ (l , ψ)

-- encode : (n : SLevel) → Sym₂ n → Fin (2 + n) ≅ Fin (2 + n)
-- encode n nil = iso (idfun (Fin (2 + n))) (idfun (Fin (2 + n))) (λ _ → refl) λ _ → refl
-- encode n (k :: x) = iso (swapAt n k) (swapAt n k) (λ y → {!!}) {!!}
-- encode n (cancel k x i) = {!!}
-- encode n (swap k l p x i) = {!!}
-- encode n (braid k x i) = {!!}
