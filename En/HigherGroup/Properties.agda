module En.HigherGroup.Properties where

open import En.Prelude
open import Cubical.Homotopy.Loopspace
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import En.HigherGroup.Base

-- abstract groups from concrete

ConcreteGroup→Group : ConcreteGroup ℓ → Group ℓ
ConcreteGroup→Group (G , isGroupoidB) =
  makeGroup {G = Ωᵍ G} refl _∙_ sym (isGroupoidB _ _) assoc (sym ∘ rUnit) (sym ∘ lUnit) rCancel lCancel

ConcreteGroupHom→GroupHom : (G : ConcreteGroup ℓ) (H : ConcreteGroup ℓ')
  → ∞GroupHom (G .fst) (H .fst) → GroupHom (ConcreteGroup→Group G) (ConcreteGroup→Group H)
ConcreteGroupHom→GroupHom G H f .fst = Ω→ f .fst
ConcreteGroupHom→GroupHom G H f .snd = makeIsGroupHom (Ω→pres∙ f)
