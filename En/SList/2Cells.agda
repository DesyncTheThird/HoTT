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
      (λ X → Square
        (ap (X ++_) (++-Λ Y))
        (ap (_++ Y) (++-ρ X))
        (sym (++-α X nil Y))
        refl)
      refl
      (λ x {xs} P i j → x :: P i j)
      (λ X → isOfHLevelPathP' 1 (is-groupoid ((X ++ nil) ++ Y) (X ++ Y)) _ _)
      X

-- ++-⬠₌
-- ++-⬠₌
-- ++-⬠₁
-- ++-⬠₂
-- ++-⬡₌
-- ++-⬡₁
-- ++-⬡₂
-- ++-β²
