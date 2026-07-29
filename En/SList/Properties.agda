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

++-:: : (x : A) (xs ys : SList A) → (x :: xs) ++ ys ≡ xs ++ (x :: ys)
++-:: x xs ys =
  SListElimPaths.elim (λ _ → SList _) (λ xs → (x :: xs) ++ ys) (λ xs → xs ++ (x :: ys))
    refl
    (λ y {xs} p → swap x y (xs ++ ys) ∙ ap (y ::_) p)
    (λ y z {xs} p →
      let S = (compPath→Square (homotopyNatural (swap y z) p))
          T = invSquarev (compPath→Triangle₀ (sym (ap-∙ (y ::_) (swap x z (xs ++ ys)) (ap (z ::_) p))))
          U = invSquareh (compPath→Triangle₀ (sym (ap-∙ (z ::_) (swap x y (xs ++ ys)) (ap (y ::_) p))))
          V = T ∙h ⬡₁ x y z (xs ++ ys) ∙h ⬡₂ x y z (xs ++ ys)
          W = flipSquare (yaMorphSquare (S ∙v U))
          X = V ∙v W
          Y = tpt3 (λ p' q r → Square p' ( swap y z (xs ++ x :: ys)
                                         ∙ sym (ap (z ::_) (swap x y (xs ++ ys)
                                         ∙ (ap (y ::_) p)))) q r)
                   (sym (lUnit _)) (sym (rUnit _)) (sym (rUnit _)) X
      in flipSquare (yaaMorphSquare Y))
    (λ xs → is-groupoid)
    xs

++-β-aux : (x y : A) (xs ys : SList A)
         → (ap (x ::_) (++-:: y ys xs) ∙∙ ++-:: x ys (y :: xs) ∙∙ ap (ys ++_) (swap x y xs))
         ≡ (swap x y (ys ++ xs) ∙∙ ap (y ::_) (++-:: x ys xs) ∙∙ ++-:: y ys (x :: xs))
++-β-aux {A = A} x y xs ys = SListElim2Paths.elim (λ _ → SList A)
        (λ ys → x :: y :: ys ++ xs)
        (λ ys → ys ++ y :: x :: xs)
        (λ ys → (ap (_::_ x) (++-:: y ys xs) ∙∙ ++-:: x ys (y :: xs) ∙∙
             ap (_++_ ys) (swap x y xs)))
        (λ ys → (swap x y (ys ++ xs) ∙∙ ap (_::_ y) (++-:: x ys xs) ∙∙
             ++-:: y ys (x :: xs)))
        (refl ∙ (swap x y ([] ++ xs))
          ≡⟨ sym (lUnit (swap x y ([] ++ xs))) ⟩
        (swap x y ([] ++ xs))
          ≡⟨ (rUnit _ ∙ rUnit _)⟩
        (swap x y ([] ++ xs) ∙ refl) ∙ refl
          ≡⟨ sym (assoc (swap x y ([] ++ xs)) refl refl) ⟩
        (swap x y ([] ++ xs) ∙ refl ∙ refl)
          ≡⟨ sym (doubleCompPath≡compPath (swap x y ([] ++ xs)) refl refl) ⟩
        (swap x y ([] ++ xs) ∙∙ refl ∙∙ refl)
          ∎
        )

        (λ z {zs} p i j → let
            S : Square
                (swap z x (zs ++ y :: xs))
                refl
                (ap (z ::_) (++-:: x zs (y :: xs)))
                (++-:: x (z :: zs) (y :: xs))
            S i = refl j
            T : Square
                (swap z x (y :: zs ++ xs))
                (swap z x (zs ++ y :: xs))
                (ap (λ a → z :: x :: a) (++-:: y zs xs))
                (ap (λ a → x :: z :: a) (++-:: y zs xs))
            T = flipSquare (compPath→Square (homotopyNatural (swap z x) (++-:: y zs xs)))
            U : Square
                (ap (x ::_) (swap z y (zs ++ xs)))
                refl
                (ap (λ a → x :: z :: a) (++-:: y zs xs))
                (ap (x ::_) (++-:: y (z :: zs) xs))
            U i = refl j
            S' : Square
                (swap z y (zs ++ x :: ys))
                refl
                (ap (z ::_) (++-:: y zs (x :: ys)))
                (++-:: y (z :: zs) (x :: ys))
            S' i = refl j
            T' : Square
                (swap z y (x :: zs ++ ys))
                (swap z y (zs ++ x :: ys))
                (ap (λ a → z :: y :: a) (++-:: x zs ys))
                (ap (λ a → y :: z :: a) (++-:: x zs ys))
            T' = flipSquare (compPath→Square (homotopyNatural (swap z y) (++-:: x zs ys)))
            U' : Square
                (ap (y ::_) (swap z x (zs ++ ys)))
                refl --
                (ap (λ a → y :: z :: a) (++-:: x zs ys)) -- (ap (y ::_) (++-:: x (z :: zs) ys))
                (ap (y ::_) (++-:: x (z :: zs) ys))
            U' i = refl j
            V = HexagonRotate⁻ (⬡₌ z x y (zs ++ xs)) (⬡₁ z x y (zs ++ xs)) (⬡₂ z x y (zs ++ xs))
            down : Square
                   (swap z x (y :: zs ++ xs) ∙ ap (x ::_) (swap z y (zs ++ xs)))
                   (swap z y (x :: zs ++ xs) ∙ ap (y ::_) (swap z x (zs ++ xs)))
                   (ap (z ::_) (swap x y (zs ++ xs)))
                   (swap x y (z :: zs ++ xs))
            down = flipSquare (HexagonAssoc⁻ (V .Hexagon.⬡₁ ∙h V .Hexagon.⬡₂))
            -- left : {!!}
            -- left = {!!}
            -- right : {!!}
            -- rigft = {!!}
            in hcomp (λ k → (λ
                { (i = i0) → down j k
                ; (i = i1) → ap (z :: zs ++_) (swap x y xs) k
                ; (j = i0) → {!!}
                ; (j = i1) → {!!}
                })) ((z ::_) p i j)
            )
        (λ _ → is-groupoid)
        ys
        

++-β : (xs ys : SList A) → xs ++ ys ≡ ys ++ xs
++-β xs ys =
  SListElimPaths.elim (λ _ → SList _) (_++ ys) (ys ++_)
    (sym (++-ρ ys))
    (λ x {xs} p → ap (x ::_) p ∙ ++-:: x ys xs)
    (λ x y {xs} p → sorry)
    (λ _ → is-groupoid)
    xs
