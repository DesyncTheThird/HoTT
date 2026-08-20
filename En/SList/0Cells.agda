module En.SList.0Cells where

open import En.Prelude
open import En.SList.Base
import En.SMG as S hiding (SMG* ; SMG*Fun)

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 20 _++_

_++_ : SList A → SList A → SList A
_++_ {A = A} xs ys =
  SListElim.elim
    (λ _ → SList A)
    ys
    (λ x xs → x :: xs)
    (λ x y xs → swap x y xs)
    (λ x y xs → swap² x y xs)
    (λ x y z xs → ⬡₌ x y z xs)
    (λ x y z xs → ⬡₁ x y z xs)
    (λ x y z xs → ⬡₂ x y z xs)
    (λ _ → is-groupoid)
    xs
