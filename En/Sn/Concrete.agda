module En.Sn.Concrete where

open import En.Prelude hiding ( _·_ )
open import Cubical.Foundations.Pointed
open import Cubical.Algebra.Group.MorphismProperties
open import En.GroupPresentation
open import En.BAut
open import En.HigherGroup
open import En.Sn.Presentation renaming ( module Univ to SymUniv )
open import En.Sn.Permutation
open import En.Sn.Delooping

private
  variable
    n : ℕ

-- concrete symmetric group on m points

B𝔖 : ℕ → ConcreteGroup ℓ-zero
B𝔖 zero = UnitConcreteGroup
B𝔖 (suc n) = BSymConcrete n

-- permutation representation

B𝔖→BAut : (m : ℕ) → ∞GroupHom (B𝔖 m .fst) (BAutGroup (FS.Fin m))
B𝔖→BAut zero = (λ _ → pt (BAut∙ (FS.Fin 0))) , refl
B𝔖→BAut (suc n) = mapModel (GroupEquiv→GroupHom (invGroupEquiv (ΩBAut≃SymGroup _ FS.isSetFin))) τModel ♯
  where open Univ (BAutConcrete (FS.Fin (suc n)) FS.isSetFin)

-- points

El𝔖 : (m : ℕ) → B𝔖 m .fst .B → Type
El𝔖 m = ElBAut ∘ B𝔖→BAut m .fst

-- completeness

isEquivB𝔖→BAut : (m : ℕ) → isEquiv (B𝔖→BAut m .fst)
isEquivB𝔖→BAut = sorry
  -- TODO: completeness of B𝔖 (isEquivB𝔖→BAut)
  --  by induction on stabilisers of a point

B𝔖≃BAut : (m : ℕ) → ∞GroupEquiv (B𝔖 m .fst) (BAutGroup (FS.Fin m))
B𝔖≃BAut m .fst = _ , isEquivB𝔖→BAut m
B𝔖≃BAut m .snd = B𝔖→BAut m .snd
