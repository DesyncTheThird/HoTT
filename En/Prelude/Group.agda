module En.Prelude.Group where

open import En.Prelude.Base hiding ( _·_ )
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

-- some useful group notation

module GroupNotation (G : Group ℓ) where

  open GroupStr (G .snd) public

  infix 40 _⁻¹ᵍ

  _⁻¹ᵍ : ⟨ G ⟩ → ⟨ G ⟩
  _⁻¹ᵍ = inv

-- composition of homomorphisms

infixr 9 _∘ᵍ_

_∘ᵍ_ : {F : Group ℓ} {G : Group ℓ'} {H : Group ℓ''} → GroupHom G H → GroupHom F G → GroupHom F H
g ∘ᵍ f = compGroupHom f g

-- underlying map and equivalence of a group equivalence

GroupEquiv→Equiv : {G : Group ℓ} {H : Group ℓ'} → GroupEquiv G H → ⟨ G ⟩ ≃ ⟨ H ⟩
GroupEquiv→Equiv ψ = ψ .fst

–>ᵍ : {G : Group ℓ} {H : Group ℓ'} → GroupEquiv G H → ⟨ G ⟩ → ⟨ H ⟩
–>ᵍ ψ = –> (GroupEquiv→Equiv ψ)
