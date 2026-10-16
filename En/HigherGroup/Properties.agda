module En.HigherGroup.Properties where

open import En.Prelude
open import Cubical.Homotopy.Loopspace
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.SymmetricGroup
open import En.Univ
open import En.BAut
open import En.HigherGroup.Base

-- change of group

ActionType≃ : {B : Type ℓ} {B' : Type ℓ'} (e : B ≃ B') (X : B' → Type ℓ'')
  → ActionType (X ∘ –> e) ≃ ActionType X
ActionType≃ e X = Σ-cong-equiv-fst e

≀-cong : {A : Type ℓ'''} {B : Type ℓ} {B' : Type ℓ'} (e : B ≃ B') (X : B' → Type ℓ'')
  → A ≀ (X ∘ –> e) ≃ A ≀ X
≀-cong e X = Σ-cong-equiv-fst e

-- abstract groups from concrete

ConcreteGroup→Group : ConcreteGroup ℓ → Group ℓ
ConcreteGroup→Group (G , isGroupoidB) =
  makeGroup {G = Ωᵍ G} refl _∙_ sym (isGroupoidB _ _) assoc (sym ∘ rUnit) (sym ∘ lUnit) rCancel lCancel

ConcreteGroupHom→GroupHom : (G : ConcreteGroup ℓ) (H : ConcreteGroup ℓ')
  → ∞GroupHom (G .fst) (H .fst) → GroupHom (ConcreteGroup→Group G) (ConcreteGroup→Group H)
ConcreteGroupHom→GroupHom G H f .fst = Ω→ f .fst
ConcreteGroupHom→GroupHom G H f .snd = makeIsGroupHom (Ω→pres∙ f)

-- loopspace of BAut is symmetric group

ΩBAut≃SymGroup : (T : Type ℓ) (isSetT : isSet T)
  → GroupEquiv (ConcreteGroup→Group (BAutConcrete T isSetT)) (SymGroup T isSetT)
ΩBAut≃SymGroup T isSetT .fst = ΩBAut≃Aut T
ΩBAut≃SymGroup T isSetT .snd = makeIsGroupHom (pathToEquivEl-∙ (BAutUUniv T))
