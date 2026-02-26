{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Prelude renaming (congS to ap ; cong to apd ; congP to apP; subst to tpt)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

module SList {ℓ} where

data SList (A : Type ℓ) : Type ℓ where
    nil : SList A
    _::_ : A → SList A → SList A

    swap : (x y : A) (xs : SList A) → x :: (y :: xs) ≡ y :: (x :: xs)
    swap² : (x y : A) (xs : SList A) → swap x y xs ≡ sym (swap y x xs)

    ⬡₌ : (x y z : A) (xs : SList A)
        → x :: (y :: (z :: xs)) ≡ z :: (y :: (x :: xs))
    ⬡₁ : (x y z : A) (xs : SList A)
        → Square (sym (swap x y (z :: xs))) (swap y z (x :: xs)) (ap (y ::_) (swap x z xs)) (⬡₌ x y z xs)
    ⬡₂ : (x y z : A) (xs : SList A)
        → Square (ap (x ::_) (swap y z xs)) (sym (ap (z ::_) (swap x y xs))) (⬡₌ x y z xs) (swap x z (y :: xs))

    is-groupoid : isGroupoid (SList A)

module SListElim {j} (A : Type ℓ) {P : SList A → Type j}
    (nil* : P nil)
    (_::*_ : (x : A) {xs : SList A} → (xs* : P xs) → P (x :: xs))

    (swap* : (x y : A) {xs : SList A} (xs* : P xs)
        → PathP (λ i → P (swap x y xs i)) (x ::* (y ::* xs*)) (y ::* (x ::* xs*)))

    (swap²* : (x y : A) {xs : SList A} (xs* : P xs)
        → SquareP (λ i j → P (swap² x y xs i j)) (swap* x y xs*) (symP (swap* y x xs*)) refl refl)

    (⬡₌* : (x y z : A) {xs : SList A} (xs* : P xs)
        → PathP (λ i → P (⬡₌ x y z xs i)) (x ::* (y ::* (z ::* xs*))) (z ::* (y ::* (x ::* xs*))))

    (⬡₁* : (x y z : A) {xs : SList A} (xs* : P xs)
        → SquareP (λ i j → P (⬡₁ x y z xs i j)) ((symP (swap* x y (z ::* xs*)))) (swap* y z (x ::* xs*)) (apP (λ i a → y ::* a) (swap* x z xs*)) (⬡₌* x y z xs*))

    (⬡₂* : (x y z : A) {xs : SList A} (xs* : P xs)
        → SquareP (λ i j → P (⬡₂ x y z xs i j)) (apP (λ i a → x ::* a) (swap* y z xs*)) (symP (apP (λ i a → z ::* a) (swap* x y xs*))) (⬡₌* x y z xs*) (swap* x z (y ::* xs*)))

    (is-groupoid* : (xs : SList A) → isGroupoid (P xs))
    where
    elim : (xs : SList A) → P xs
    elim nil = nil*
    elim (x :: xs) = x ::* elim xs
    elim (swap x y xs i) = swap* x y (elim xs) i
    elim (swap² x y xs i j) = swap²* x y (elim xs) i j
    elim (⬡₌ x y z xs i) = ⬡₌* x y z (elim xs) i
    elim (⬡₁ x y z xs i j) = ⬡₁* x y z (elim xs) i j
    elim (⬡₂ x y z xs i j) = ⬡₂* x y z (elim xs) i j
    elim (is-groupoid xs xs' p q r s i j k) = isGroupoid→CubeP (λ i j k → P (is-groupoid xs xs' p q r s i j k))
         (λ j k → elim (r j k)) (λ j k → elim (s j k)) (λ i k → elim (p k)) (λ i k → elim (q k)) (λ i j → elim xs) (λ i j → elim xs') (is-groupoid* xs') i j k



















-- data Foo : Type ℓ where
--   pt : Foo
--   loop : pt ≡ pt
--   loop2 : loop ∙ loop ≡ refl

-- -- module FooElim {p} {P : Foo → Type p}
-- --   (pt* : P pt)
-- --   (loop* : PathP (λ i → P (loop i)) pt* pt*)
-- --   (loop2* : PathP (λ i → PathP (λ j → {!P ?!}) (loop* i) (loop* i)) (compPathP loop* loop*) (refl {x = pt*}))
-- --   where

-- -- module FooElim2 {p} {P : Foo → Type p}
-- --   (pt* : P pt)
-- --   (loop* : tpt P loop pt* ≡ pt*)
-- --   (loop2* : tpt {!!} {!!} {!!} ≡ refl {x = pt*})
-- --   where

-- tcomp : {A : Type ℓ} {P : A → Type ℓ}
--       → {a b c : A} (p : a ≡ b) (q : b ≡ c)
--       → (u : P a) (v : P b) (w : P c)
--       → tpt P (p ∙ q) u ≡ tpt P q (tpt P p u)
-- tcomp {P = P} p q u v w = substComposite P p q u

-- dcomp : {A : Type ℓ} {P : A → Type ℓ}
--       → {a b c : A} (p : a ≡ b) (q : b ≡ c)
--       → (u : P a) (v : P b) (w : P c)
--       → (s : tpt P p u ≡ v) (t : tpt P q v ≡ w)
--       → tpt P (p ∙ q) u ≡ w
-- dcomp {P = P} p q u v w s t = tcomp p q u v w ∙ ap (tpt P q) s ∙ t
