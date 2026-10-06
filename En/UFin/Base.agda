module En.UFin.Base where

open import En.Prelude
open SumFin
open import Cubical.Foundations.Pointed
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Properties
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.Induction using ( 𝟘 ; 𝟙 ) public
import Cubical.Data.FinSet.Induction as FS
open import En.Univ.Base

-- universe of finite types

UFin : Type₁
UFin = FinSet ℓ-zero

UFinSub : SubUniv ℓ-zero ℓ-zero
UFinSub = isFinSet , λ _ → isPropIsFinSet

FinU : ℕ → UFin
FinU n = Fin n , isFinSetFin

UFin∙ : ℕ → Pointed (ℓ-suc ℓ-zero)
UFin∙ n = UFin , FinU n

-- rig operations

infixl 6 _+ᶠ_
infixl 7 _×ᶠ_

_+ᶠ_ : UFin → UFin → UFin
_+ᶠ_ = FS._+_

_×ᶠ_ : UFin → UFin → UFin
(X ×ᶠ Y) .fst = X .fst × Y .fst
(X ×ᶠ Y) .snd = isFinSet× X Y
