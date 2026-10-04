module En.UFin.Properties where

open import En.Prelude
open SumFin
open import Cubical.Foundations.Pointed
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit
open import Cubical.Data.FinSet.Base
open import Cubical.Data.FinSet.Cardinality
open import Cubical.Data.Fin.LehmerCode
open import En.Univ
open import En.BAut
open import En.UFin.Base
import En.SMG as S hiding ( SMG* ; SMG*Fun )

isGroupoidUFin : isGroupoid UFin
isGroupoidUFin = isGroupoidFinSet

UFinUUniv : UUniv (ℓ-suc ℓ-zero) ℓ-zero
UFinUUniv = SubUUniv {P = isFinSet} λ _ → isPropIsFinSet

-- cardinality

UFin≃ΣBAut : UFin ≃ (Σ[ n ∈ ℕ ] BAut (Fin n))
UFin≃ΣBAut = isoToEquiv i
  where
    open Iso
    i : Iso UFin (Σ[ n ∈ ℕ ] BAut (Fin n))
    i .fun (X , n , t) = n , X , PT.map invEquiv t
    i .inv (n , X , t) = X , n , PT.map invEquiv t
    i .sec (n , X , t) j = n , X , squash₁ (PT.map invEquiv (PT.map invEquiv t)) t j
    i .ret (X , n , t) j = X , n , squash₁ (PT.map invEquiv (PT.map invEquiv t)) t j

Fin≃→≡ : {m n : ℕ} → Fin m ≃ Fin n → m ≡ n
Fin≃→≡ e = cardEquiv (FinU _) (FinU _) ∣ e ∣₁

ΩUFin≃Aut : (n : ℕ) → ⟨ Ω (UFin∙ n) ⟩ ≃ Aut (Fin n)
ΩUFin≃Aut n = El≡≃ UFinUUniv

ΩUFin≃LehmerCode : (n : ℕ) → ⟨ Ω (UFin∙ n) ⟩ ≃ LehmerCode n
ΩUFin≃LehmerCode n =
  ΩUFin≃Aut n ∙ₑ equivComp (SumFin≃Fin n) (SumFin≃Fin n) ∙ₑ lehmerEquiv

isContrAutFin0 : isContr (Aut (Fin 0))
isContrAutFin0 = idEquiv _ , λ e → equivEq (funExt λ ())
