module En.Sn.Permutation where

open import En.Prelude hiding ( _·_ )
open FN hiding ( fzero ; fsuc )
open FS using ( fzero ; fsuc )
open import Cubical.Data.Sum as ⊎ using ( _⊎_ ; inl ; inr )
open import Cubical.Functions.Involution
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.SymmetricGroup
open import En.BAut.Base
open import En.GroupPresentation
open import En.GroupAction.Base
open import En.Sn.Base
open import En.Sn.Properties
open import En.Sn.Presentation

private
  variable
    n : ℕ

-- adjacent transpositions

τ : Fin n → FS.Fin (suc n) → FS.Fin (suc n)
τ {zero} (_ , ())
τ {suc n} (zero , _) fzero = fsuc fzero
τ {suc n} (zero , _) (fsuc fzero) = fzero
τ {suc n} (zero , _) (fsuc (fsuc x)) = fsuc (fsuc x)
τ {suc n} (suc k , _) fzero = fzero
τ {suc n} (suc k , p) (fsuc x) = fsuc (τ {n} (k , p) x)

τInvol : (k : Fin n) → isInvolution (τ {n} k)
τInvol {zero} (_ , ())
τInvol {suc n} (zero , _) fzero = refl
τInvol {suc n} (zero , _) (fsuc fzero) = refl
τInvol {suc n} (zero , _) (fsuc (fsuc x)) = refl
τInvol {suc n} (suc k , _) fzero = refl
τInvol {suc n} (suc k , p) (fsuc x) = ap fsuc (τInvol {n} (k , p) x)

τ≃ : Fin n → Aut (FS.Fin (suc n))
τ≃ {n} k = involEquiv {f = τ {n} k} (τInvol k)

τ≃Cancel : (k : Fin n) → τ≃ {n} k ∙ₑ τ≃ {n} k ≡ idEquiv _
τ≃Cancel k = equivEq (funExt (τInvol k))

τ≃Comm : (k l : Fin n) → suc (k .fst) <ᵗ l .fst → τ≃ {n} l ∙ₑ τ≃ {n} k ≡ τ≃ {n} k ∙ₑ τ≃ {n} l
τ≃Comm = sorry
  -- TODO: far transpositions commute (τ≃Comm)
  --  by recursion on k and l

τ≃Braid : (k l : Fin n) → suc (k .fst) ≡ l .fst
  → τ≃ {n} l ∙ₑ τ≃ {n} k ∙ₑ τ≃ {n} l ≡ τ≃ {n} k ∙ₑ τ≃ {n} l ∙ₑ τ≃ {n} k
τ≃Braid = sorry
  -- TODO: adjacent transpositions braid (τ≃Braid)
  --  by recursion on k with l = suc k

-- permutation representation

τModel : FinSymGroup (suc n) ⊨ CoxeterPresentation n
τModel .gen = τ≃
τModel .rel (cancel k) = τ≃Cancel k
τModel .rel (comm k l p) = τ≃Comm k l p
τModel .rel (braid k l p) = τ≃Braid k l p

Sym→AutHom : GroupHom (CoxeterGroup n) (FinSymGroup (suc n))
Sym→AutHom {n} = τModel ♯
  where open Univ (FinSymGroup (suc n))

Sym→Aut : Sym n → Aut (FS.Fin (suc n))
Sym→Aut = Sym→AutHom .fst

-- the coxeter group on m points

𝔖 : ℕ → Group₀
𝔖 zero = UnitGroup₀
𝔖 (suc n) = CoxeterGroup n

𝔖→AutHom : (m : ℕ) → GroupHom (𝔖 m) (FinSymGroup m)
𝔖→AutHom zero .fst _ = idEquiv _
𝔖→AutHom zero .snd = makeIsGroupHom λ _ _ → equivEq (funExt λ ())
𝔖→AutHom (suc n) = Sym→AutHom

-- permutation actions on points

𝔖Action : (m : ℕ) → Action (𝔖 m) (FS.Fin m)
𝔖Action m = restrictAction (𝔖→AutHom m) (autAction (FS.Fin m) FS.isSetFin)
