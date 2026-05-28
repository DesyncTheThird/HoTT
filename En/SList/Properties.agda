module En.SList.Properties where

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

++-Λ : (xs : SList A) → nil ++ xs ≡ xs
++-Λ xs = refl

++-ρ : (xs : SList A) → xs ++ nil ≡ xs
++-ρ =
  SListElimSet.elim
    (λ xs → xs ++ nil ≡ xs)
    refl
    (λ x → ap (x ::_))
    (λ x y p → compPath→Square (homotopyNatural (swap x y) p))
    (λ xs → is-groupoid (xs ++ nil) xs)

++-α : (xs ys zs : SList A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-α xs ys zs =
  SListElimSet.elim (λ xs → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs))
    refl
    (λ x → ap (x ::_))
    (λ x y p → compPath→Square (homotopyNatural (swap x y) p))
    (λ xs → is-groupoid ((xs ++ ys) ++ zs) (xs ++ ys ++ zs)) xs

-- swap-++ : (x y : A) (xs : SList A) → swap x y (xs ++ [ x ]) ≡ ap (_++ [ x ]) (swap x y xs)
-- swap-++ x y xs = refl

++-:: : (x : A) (xs : SList A) → x :: xs ≡ xs ++ ([ x ])
++-:: x =
  SListElimSet.elim (λ xs → x :: xs ≡ xs ++ [ x ])
    refl
    (λ y {xs} p → swap x y xs ∙ ap (y ::_) p)
    (λ y z {xs} p →
      ( tpt {!!} {!!} (⬡₁ y x z xs) ∙h {!!}

-- (⬡₁ y x z xs ∙h ⬡₂ y x z xs)
      -- ∙h ?
       -- tpt (λ s → Square (ap (λ zs → y :: z :: zs) p) (ap (λ zs → z :: y :: zs) p) (swap y z (x :: xs)) s)
       --     (ap (λ _ → swap y z {!!}) {!!})
       --     (compPath→Square (homotopyNatural {f = λ zs → y :: z :: zs}
       --                        {g = λ zs → z :: y :: zs} (λ xs → swap y z xs) p))
      )
      )
    (λ xs → is-groupoid (x :: xs) (xs ++ [ x ]))

++-β : (xs ys : SList A) → xs ++ ys ≡ ys ++ xs
++-β xs ys =
  SListElimSet.elim (λ xs → xs ++ ys ≡ ys ++ xs)
    (sym (++-ρ (ys)))
    (λ x {xs} p → ap (x ::_) p ∙∙ ap (_++ xs) (++-:: x ys) ∙∙ ++-α ys [ x ] xs)
    {!!}
    (λ xs → is-groupoid (xs ++ ys) (ys ++ xs))
    xs
