module En.Sn where

open import En.Prelude
open import Cubical.Data.Nat.Order
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Binary
open import Cubical.Data.Fin.LehmerCode hiding ( encode ; decode ) renaming ( _∷_ to _▹_)
open import Cubical.Data.List

SLevel = ℕ

infixr 30 _::_

data Sym₂ (n : SLevel) : Type₀ where
    nil : Sym₂ n
    _::_ : (k : Fin (suc n)) → Sym₂ n → Sym₂ n

    cancel : (k : Fin (suc n)) (σ : Sym₂ n) → k :: k :: σ ≡ σ
    swap : (k l : Fin (suc n)) → (p : suc (k .fst) < l .fst) → (σ : Sym₂ n) → l :: k :: σ ≡ k :: l :: σ
    braid : (k : Fin n) → (σ : Sym₂ n)
        → fsuc k :: finj k :: fsuc k :: σ ≡ finj k :: fsuc k :: finj k :: σ



infixr 40 _*

data _* {ℓ : Level} {A : Type ℓ} (R : Rel A A ℓ) : Rel A A ℓ where
    reflex : (w : A) → (R *) w w
    trans : ∀ u v w → R u v → (R *) v w → (R *) u w

-- infixr 50 _↝_

-- data _↝_ {n : ℕ} : List (Fin n) → List (Fin n) → Type₀ where
--     cancel : (k : Fin (suc n)) (σ : Sym₂ n) → k :: k :: σ ↝ σ
--     swap : (k l : Fin (suc n)) → (p : suc (k .fst) < l .fst) → (σ : Sym₂ n) → l :: k :: σ ↝ k :: l :: σ
--     braid : (k : Fin n) → (σ : Sym₂ n) → fsuc k :: finj k :: fsuc k :: σ ↝ finj k :: fsuc k :: finj k :: σ






qSym₂ : (n : SLevel) → Type₀
qSym₂ n = List (Fin n) / {!!}



Sym : (n : ℕ) → Type₀
Sym zero = Unit
Sym (suc zero) = Unit
Sym (suc (suc n)) = Sym₂ n

baz : equivFun (Iso.inv (equivToIso lehmerEquiv) (1 ▹ 0 ▹ 1 ▹ 0 ▹ [])) ≡ (λ { (0 , tt) → 1 ; (1 , tt) → 0 ; (2 , tt) → 3 ; (3 , tt) → 2 })
baz = funExt λ { (0 , tt) → refl ; (1 , tt) → refl ; (2 , tt) → refl ; (3 , tt) → refl}
-- baz i (zero , ϕ) = 1
-- baz i (suc zero , ϕ) = 0
-- baz i (suc (suc zero) , ϕ) = 3
-- baz i (suc (suc (suc zero)) , ϕ) = 2










-- Sym→Lehmer : (n : SLevel) → Sym n → LehmerCode n
-- Sym→Lehmer zero s = []
-- Sym→Lehmer (suc zero) s = {!!}
-- Sym→Lehmer (suc (suc n)) nil = {!!}
-- Sym→Lehmer (suc (suc n)) (k :: s) = {!!}
-- Sym→Lehmer (suc (suc n)) (cancel k s i) = {!!}
-- Sym→Lehmer (suc (suc n)) (swap k l p s i) = {!!}
-- Sym→Lehmer (suc (suc n)) (braid k s i) = {!!}















-- swapAt≠ : (n : SLevel) (k : Fin (suc n)) → (l : Fin (suc (suc n))) → Fin (suc (suc n))
-- swapAt≠ n (k , ϕ) (l , ψ) =
--     decRec
--         (λ q → (k , <ᵗ-trans-suc {n = k} {m = suc n} ϕ))
--         (λ ¬q → (l , ψ))
--         (discreteℕ (suc k) l)

-- swapAt≠-=β : (n : SLevel) (fk@(k , ϕ) : Fin (suc n)) → (fl@(l , ψ) : Fin (suc (suc n))) → (p : suc k ≡ l) → swapAt≠ n fk fl ≡ (k , <ᵗ-trans-suc {n = k} {m = suc n} ϕ)
-- swapAt≠-=β n (k , ϕ) (l , ψ) p = decRecYes (isSetℕ (suc k) l) p (discreteℕ (suc k) l)

-- swapAt≠-≠β : (n : SLevel) (fk@(k , ϕ) : Fin (suc n)) → (fl@(l , ψ) : Fin (suc (suc n))) → (¬p : ¬ (suc k ≡ l)) → swapAt≠ n fk fl ≡ fl
-- swapAt≠-≠β n (k , ϕ) (l , ψ) ¬p = decRecNo (isSetℕ (suc k) l) ¬p (discreteℕ (suc k) l)

-- swapAt : (n : SLevel) → (k : Fin (suc n)) → Fin (suc (suc n)) → Fin (suc (suc n))
-- swapAt n (k , ϕ) (l , ψ) =
--     decRec
--         (λ p → (suc k , ϕ))
--         (λ _ → swapAt≠ n (k , ϕ) (l , ψ))
--         (discreteℕ k l)

-- swapAt=-=β : (n : SLevel) (k : Fin (suc n)) → (l : Fin (suc (suc n))) → (p : k .fst ≡ l .fst) → swapAt n k l ≡ fsuc k
-- swapAt=-=β n (k , ϕ) (l , ψ) p = decRecYes (isSetℕ k l) p (discreteℕ k l)

-- swapAt=-≠β : (n : SLevel) (fk@(k , ϕ) : Fin (suc n)) → (fl@(l , ψ) : Fin (suc (suc n))) → (p : k ≡ l) (¬q : ¬(k ≡ l)) → swapAt n fk fl ≡ swapAt≠ n fk fl
-- swapAt=-≠β n (k , ϕ) (l , ψ) p ¬q = decRecNo (isSetℕ k l) ¬q (discreteℕ k l)


-- _ : swapAt 5 2 3 ≡ 2
-- _ = refl

-- swapAt-suc : (n : SLevel) (k : Fin (suc n)) → swapAt n k (fsuc k) ≡ finj k
-- swapAt-suc n fk@(k , ϕ) with discreteℕ k (suc k) | discreteℕ (suc k) (suc k)
-- ... | yes p | yes q = ⊥.rec (sucn≠n (sym p))
-- ... | yes p | no ¬q = ⊥.rec (sucn≠n (sym p))
-- ... | no ¬p | yes q = refl
-- ... | no ¬p | no ¬q = ⊥.rec (¬q refl)

-- swapAt-eq : (n : SLevel) (k : Fin (suc n)) → swapAt n k (finj k) ≡ fsuc k
-- swapAt-eq n fk@(k , ϕ) with discreteℕ k k | discreteℕ (suc k) k
-- ... | yes p | yes q = refl
-- ... | yes p | no ¬q = refl
-- ... | no ¬p | yes q = ⊥.rec (¬p refl)
-- ... | no ¬p | no ¬q = ⊥.rec (¬p refl)


-- swapAt² : (n : SLevel) (k : Fin (suc n)) → (l : Fin (suc (suc n))) → swapAt n k (swapAt n k l) ≡ l
-- swapAt² n fk@(k , ϕ) fl@(l , ψ) = ?


-- swapAt n (k , ϕ) (swapAt n (k , ϕ) (l , ψ)) ≡ (l , ψ)

-- encode : (n : SLevel) → Sym₂ n → Fin (2 + n) ≅ Fin (2 + n)
-- encode n nil = iso (idfun (Fin (2 + n))) (idfun (Fin (2 + n))) (λ _ → refl) λ _ → refl
-- encode n (k :: x) = iso (swapAt n k) (swapAt n k) (λ y → {!!}) {!!}
-- encode n (cancel k x i) = {!!}
-- encode n (swap k l p x i) = {!!}
-- encode n (braid k x i) = {!!}







-- Sym : (n : ℕ) → Type
-- Sym n = 1 ⊎ 1 ⊎ Sym n
