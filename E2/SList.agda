{-# OPTIONS --cubical --safe --guardedness #-}

open import Cubical.Foundations.Prelude renaming (congS to ap ; cong to apd ; subst to tpt)
open import Cubical.Foundations.HLevels

module SList {ℓ} (A : Type ℓ) (is-groupoid : isGroupoid A) where

data SList : Type ℓ where
    nil : SList
    _·_ : A → SList → SList
    swap : (x y : A) (xs : SList) → x · (y · xs) ≡ y · (x · xs)

    ⬡₌ : (x y z : A) (xs : SList)
        → x · (y · (z · xs)) ≡ z · (y · (x · xs))
    ⬡₁ : (x y z : A) (xs : SList)
        → Square ? ? ? ⬡₌
    ⬡₂ : (x y z : A) (xs : SList)
        → Square ? ? ⬡₌ ?