module En.Sn.Base where


open import En.Prelude

open import Cubical.Data.Fin.LehmerCode hiding ( encode ; decode ) renaming ( _∷_ to _▹_ )

SLevel = ℕ


infixr 30 _::_

data Sym₂ (n : SLevel) : Type where
    nil : Sym₂ n
    _::_ : (k : Fin (suc n)) → Sym₂ n → Sym₂ n

    cancel : (k : Fin (suc n)) (σ : Sym₂ n) → k :: k :: σ ≡ σ
    swap : (k l : Fin (suc n)) → {p : suc (k .fst) < l .fst} → (σ : Sym₂ n) → l :: k :: σ ≡ k :: l :: σ
    braid : (k : Fin n) → (σ : Sym₂ n)
        → fsuc k :: finj k :: fsuc k :: σ ≡ finj k :: fsuc k :: finj k :: σ

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


-- [] ++↙ τs = ys
-- (x ↙ n ∷ xs) ++↙ ys = x ↙ n ∷ (xs ++↙ ys)



infixr 40 _*

data _* {ℓ : Level} {A : Type ℓ} (R : Rel A A ℓ) : Rel A A ℓ where
    reflex : (w : A) → (R *) w w
    trans : ∀ u v w → R u v → (R *) v w → (R *) u w



-- Sym : (n : ℕ) → Type₀
-- Sym zero = Unit
-- Sym (suc zero) = Unit
-- Sym (suc (suc n)) = Sym₂ n

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














-- Sym : (n : ℕ) → Type
-- Sym n = 1 ⊎ 1 ⊎ Sym n


-- open import Cubical.HITs.SetQuotients public
-- open import Cubical.Data.Fin.LehmerCode hiding ( encode ; decode ) renaming ( _∷_ to _▹_ )




+-monotone : (a b c d : ℕ) → (a <ᵗ b) → (c <ᵗ d) → (a + c) <ᵗ (b + d)
+-monotone zero (suc b) zero d p q = tt
+-monotone zero (suc b) (suc c) (suc d) p q = tpt (c <ᵗ_) (sym (+-suc b d)) (+-monotone 0 (suc b) c d tt q)
+-monotone (suc a) (suc b) c d p q = +-monotone a b c d p q

infixr 4 _+ᶠ_

_+ᶠ_ : {n m : ℕ} → Fin n → Fin m → Fin (n + m)
-- _+ᶠ_ {n} {m} (a , p) (b , q) = b , +-monotone 0 n b m p q -- <ᵗ-trans {n = b}
_+ᶠ_ {n} {m} (a , p) (b , q) = a + b , +-monotone a n b m p q

