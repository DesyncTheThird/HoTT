module En.Sn.Presentation where

open import En.Prelude hiding ( _·_ )
open FN
open import Cubical.HITs.FreeGroup as FG using ()
open import Cubical.HITs.PropositionalTruncation as PT using ( ∥_∥₁ ; ∣_∣₁ )
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import En.GroupPresentation
open import En.Sn.Base
open import En.Sn.Properties

private
  variable
    n : ℕ

-- the coxeter presentation

data CoxeterRel (n : ℕ) : Type where
  cancel : Fin n → CoxeterRel n
  comm : (k l : Fin n) → suc (k .fst) <ᵗ l .fst → CoxeterRel n
  braid : (k l : Fin n) → suc (k .fst) ≡ l .fst → CoxeterRel n

CoxeterPresentation : ℕ → Presentation ℓ-zero
CoxeterPresentation n = ⟨ Fin n ∣ coxeterRelation ⟩
  where
    open FG using ( η ; ε ; _·_ )
    coxeterRelation : CoxeterRel n → Relation (Fin n)
    coxeterRelation (cancel k) = η k · η k ≐ ε
    coxeterRelation (comm k l _) = η l · η k ≐ η k · η l
    coxeterRelation (braid k l _) = η l · (η k · η l) ≐ η k · (η l · η k)

symModel : CoxeterGroup n ⊨ CoxeterPresentation n
symModel .gen k = [ k ]
symModel .rel (cancel k) = cancel k nil
symModel .rel (comm k l p) = comm k l p nil
symModel .rel (braid k l p) = braid k l p nil

isGeneratedSym : isGenerated (symModel {n})
isGeneratedSym {n} =
  SymElimProp.elim (λ σ → ∥ fiber ((symModel .gen ♯) .fst) σ ∥₁)
    ∣ FG.ε , refl ∣₁
    (λ k → PT.map λ { (w , p) → FG.η k FG.· w , ap (k ::_) p })
    (λ _ → PT.squash₁)
  where open FreeGroupUniv (CoxeterGroup n) using ( _♯ )

-- universal property

module Univ (H : Group ℓ) {n : ℕ} where

  open GroupStr (H .snd)

  private
    ·Assoc3 : (x y z w : ⟨ H ⟩) → x · (y · (z · w)) ≡ (x · (y · z)) · w
    ·Assoc3 x y z w = ap (x ·_) (·Assoc y z w) ∙ ·Assoc x (y · z) w

  module _ (M : H ⊨ CoxeterPresentation n) where

    rec : Sym n → ⟨ H ⟩
    rec =
      SymElimSet.elim (λ _ → ⟨ H ⟩)
        1g
        (λ k h → M .gen k · h)
        (λ k h → ·Assoc _ _ h ∙ ap (_· h) (M .rel (cancel k)) ∙ ·IdL h)
        (λ k l p h → ·Assoc _ _ h ∙ ap (_· h) (M .rel (comm k l p)) ∙ sym (·Assoc _ _ h))
        (λ k l p h → ·Assoc3 _ _ _ h ∙ ap (_· h) (M .rel (braid k l p)) ∙ sym (·Assoc3 _ _ _ h))
        (λ _ → is-set)

    rec-++ : (σ ρ : Sym n) → rec (σ ++ ρ) ≡ rec σ · rec ρ
    rec-++ =
      SymElimProp.elim (λ σ → (ρ : Sym n) → rec (σ ++ ρ) ≡ rec σ · rec ρ)
        (λ ρ → sym (·IdL _))
        (λ k p ρ → ap (M .gen k ·_) (p ρ) ∙ ·Assoc _ _ _)
        (λ _ → isPropΠ λ _ → is-set _ _)

  _♯ : H ⊨ CoxeterPresentation n → GroupHom (CoxeterGroup n) H
  (M ♯) .fst = rec M
  (M ♯) .snd = makeIsGroupHom (rec-++ M)

  open Presented symModel isGeneratedSym H _♯ (λ M k → ·IdR (M .gen k)) public

-- ↑ shifts generators up

↑Model : CoxeterGroup (suc n) ⊨ CoxeterPresentation n
↑Model .gen k = [ fsuc k ]
↑Model .rel (cancel k) = cancel (fsuc k) nil
↑Model .rel (comm k l p) = comm (fsuc k) (fsuc l) p nil
↑Model .rel (braid k l p) = braid (fsuc k) (fsuc l) (ap suc p) nil

↑Hom : GroupHom (CoxeterGroup n) (CoxeterGroup (suc n))
↑Hom {n} = ↑Model ♯
  where open Univ (CoxeterGroup (suc n))

↑ : Sym n → Sym (suc n)
↑ = ↑Hom .fst

-- ι includes generators at the bottom

ιModel : CoxeterGroup (suc n) ⊨ CoxeterPresentation n
ιModel .gen k = [ finj k ]
ιModel .rel (cancel k) = cancel (finj k) nil
ιModel .rel (comm k l p) = comm (finj k) (finj l) p nil
ιModel .rel (braid k l p) = braid (finj k) (finj l) p nil

ιHom : GroupHom (CoxeterGroup n) (CoxeterGroup (suc n))
ιHom {n} = ιModel ♯
  where open Univ (CoxeterGroup (suc n))

ι : Sym n → Sym (suc n)
ι = ιHom .fst
