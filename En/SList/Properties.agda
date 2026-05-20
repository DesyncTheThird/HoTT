module En.SList.Properties where

open import En.Prelude
open import En.SList.Base
import En.SMG as S hiding (SMG* ; SMG*Fun)

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 20 _++_

-- _++_ : ∀ {ℓ} {A : Type ℓ} → SList A → SList A → SList A
-- _++_ {A = A} =
--   SListElim.elim
--     (λ _ → SList A → SList A)
--     (idfun (SList A))
--     (λ x {xs} f ys → x :: f ys)
--     (λ x y {xs} f i ys → swap x y (f ys) i)
--     (λ x y {xs} f i j ys → swap² x y (f ys) i j)
--     (λ x y z {xs} f i ys → ⬡₌ x y z (f ys) i)
--     (λ x y z {xs} f i j ys → ⬡₁ x y z (f ys) i j)
--     (λ x y z {xs} f i j ys → ⬡₂ x y z (f ys) i j)
--     (λ _ → isGroupoidΠ (λ _ → is-groupoid))

_++_ : ∀ {ℓ} {A : Type ℓ} → SList A → SList A → SList A
_++_ {A = A} xs ys =
  SListElim.elim
    (λ _ → SList A)
    ys
    (λ x {xs} zs → x :: zs)
    (λ x y {xs} zs i → swap x y zs i)
    (λ x y {xs} zs i j → swap² x y zs i j)
    (λ x y z {xs} zs i → ⬡₌ x y z zs i)
    (λ x y z {xs} zs i j → ⬡₁ x y z zs i j)
    (λ x y z {xs} zs i j → ⬡₂ x y z zs i j)
    (λ _ → is-groupoid)
    xs
