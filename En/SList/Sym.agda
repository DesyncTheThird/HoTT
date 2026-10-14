module En.SList.Sym where

open import En.Prelude hiding ( _·_ )
open import En.Sn.Permutation
open import En.GroupAction.Base

-- vectors up to the coxeter groups acting on positions

Vec//𝔖 : Type ℓ → Type ℓ
Vec//𝔖 A = Σ[ m ∈ ℕ ] A ≀ 𝔖Action m
