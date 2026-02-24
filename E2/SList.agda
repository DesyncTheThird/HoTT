{-# OPTIONS --cubical --safe --guardedness #-}

open import Cubical.Foundations.Prelude renaming (congS to ap ; cong to apd ; subst to tpt)
open import Cubical.Foundations.HLevels

module SList {ℓ} where

data SList (A : Type ℓ) : Type ℓ where
    nil : SList A
    _::_ : A → SList A → SList A
    swap : (x y : A) (xs : SList A) → x :: (y :: xs) ≡ y :: (x :: xs)
    swap² : (x y : A) (xs : SList A) → swap x y xs ∙ swap y x xs ≡ refl

    ⬡ : (x y z : A) (xs : SList A)
        → swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ swap y z (x :: xs)
        ≡ ap (x ::_) (swap y z xs) ∙ swap x z (y :: xs) ∙ ap (z ::_) (swap x y xs)

    -- ⬡₌ : (x y z : A) (xs : SList)
    --     → x · (y · (z · xs)) ≡ z · (y · (x · xs))
    -- ⬡₁ : (x y z : A) (xs : SList)
    --     → Square ? ? ? ⬡₌
    -- ⬡₂ : (x y z : A) (xs : SList)
    --     → Square ? ? ⬡₌ ?


module SListElim {j} (A : Type ℓ) {P : SList A → Type j}
    (nil* : P nil)
    (_::*_ : (x : A) {xs : SList A} → (xs* : P xs) → P (x :: xs))
    (swap* : (x y : A) {xs : SList A} (xs* : P xs)
        → PathP (λ i → P (swap x y xs i)) (x ::* (y ::* xs*)) (y ::* (x ::* xs*)))
    (swap²* : (x y z : A) {xs : SList A} (xs* : P xs)
         → PathP (λ i →  PathP (λ j → {! ?!}) {!!} {!!}) ( compPathP (swap* x y xs*) (swap* y x xs*) ) refl)
        -- (swap* x y xs* ∙ᵈ swap* y x xs*) ≡ idp [ (λ p → (x ::* (y ::* xs*)) == (x ::* (y ::* xs*)) [ P ↓ p ]) ↓ swap² x y xs ])
    -- (⬡* : (x y z : A) {xs : SList A} (xs* : P xs)
    --     → let p1 = swap* x y (z ::* xs*) ∙ᵈ ($ (y ::*_) (swap* x z xs*) ∙ᵈ swap* y z (x ::* xs*))
    --        p2 = $ (x ::*_) (swap* y z xs*) ∙ᵈ (swap* x z (y ::* xs*) ∙ᵈ $ (z ::*_) (swap* x y xs*))
    --        in p1 == p2 [ (λ p → (x ::* (y ::* (z ::* xs*))) == (z ::* (y ::* (x ::* xs*))) [ P ↓ p ]) ↓ ⬡ x y z xs ])
    -- (trunc* : {xs : SList A} → has-level 1 (P xs))
    where