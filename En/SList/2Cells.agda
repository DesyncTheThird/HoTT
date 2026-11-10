module En.SList.2Cells where

open import En.Prelude
open import En.SList.0Cells
open import En.SList.1Cells
open import En.SList.Base
import En.SMG as S hiding (SMG* ; SMG*Fun)

private
  variable
    A : Type ℓ

module _ (X Y : SList A) where

  ++-▽ : Square
        (ap (X ++_) (++-Λ Y))
        (ap (_++ Y) (++-ρ X))
        (sym (++-α X nil Y))
        refl
  ++-▽ =
    SListElimProp.elim
    (λ X →
      Square
        (ap (X ++_) (++-Λ Y))
        (ap (_++ Y) (++-ρ X))
        (sym (++-α X nil Y))
        refl
    )
    refl
    (λ x {xs} P i j → x :: P i j)
    (λ X → isOfHLevelPathP' 1 (is-groupoid ((X ++ nil) ++ Y) (X ++ Y)) (ap (X ++_) (++-Λ Y)) (ap (_++ Y) (++-ρ X)))
    X

++-⬠₌ : (W X Y Z : SList A) → ((W ++ X) ++ Y) ++ Z ≡ W ++ X ++ Y ++ Z
++-⬠₌ W X Y Z =
  SListElimSet.elim
    (λ W → ((W ++ X) ++ Y) ++ Z ≡ W ++ X ++ Y ++ Z)
    (++-α X Y Z)
    (λ x {xs} P i → x :: P i)
    (λ x y {xs} P → flipSquare (homotopyNaturalSq (swap x y) P))
    (λ xs → isOfHLevelPathP' 2 is-groupoid _ _)
    W

module _ (W X Y Z : SList A) where

  ++-⬠₁ : Square
          (sym (++-α (W ++ X) Y Z))
          (++-α W X (Y ++ Z))
          refl
          (++-⬠₌ W X Y Z)
  ++-⬠₁ =
    SListElimProp.elim
    (λ W →
      Square
      (sym (++-α (W ++ X) Y Z))
      (++-α W X (Y ++ Z))
      refl
      (++-⬠₌ W X Y Z)
    )
    (λ i j → ++-α X Y Z (i ∨ ~ j))
    (λ x {xs} P i j → x :: P i j)
    (λ xs → isOfHLevelPathP' 1 (is-groupoid ((xs ++ X) ++ Y ++ Z) (xs ++ X ++ Y ++ Z)) (sym (++-α (xs ++ X) Y Z)) (++-α xs X (Y ++ Z)))
    W

  ++-⬠₂ : Square
          (ap (_++ Z) (++-α W X Y))
          (sym (ap (_++_ W) (++-α X Y Z)))
          (++-⬠₌ W X Y Z) (++-α W (X ++ Y) Z)
  ++-⬠₂ =
    SListElimProp.elim
      (λ W →
        Square
        (ap (_++ Z) (++-α W X Y))
        (sym (ap (_++_ W) (++-α X Y Z)))
        (++-⬠₌ W X Y Z)
        (++-α W (X ++ Y) Z)
      )
      (λ i j → ++-α X Y Z (i ∧ ~ j))
      (λ x {xs} P i j → x :: P i j)
      (λ xs → isOfHLevelPathP' 1 (is-groupoid (xs ++ X ++ Y ++ Z) (xs ++ (X ++ Y) ++ Z)) _ _)
      W



-- ++-⬡₌
-- ++-⬡₁
-- ++-⬡₂
-- ++-β²
