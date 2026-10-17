module En.GroupPresentation.Base where

open import En.Prelude hiding ( _·_ )
open import En.Prelude.Group
open import Cubical.HITs.FreeGroup as FG using ( FreeGroup )
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms

-- free groups are free

module FreeGroupUniv (G : Group ℓ') {ℓX : Level} {X : Type ℓX} where

  _♯ : (X → ⟨ G ⟩) → GroupHom (FG.freeGroupGroup X) G
  g ♯ = FG.rec g

  _♭ : GroupHom (FG.freeGroupGroup X) G → X → ⟨ G ⟩
  f ♭ = f .fst ∘ FG.η

  ♭♯ : (g : X → ⟨ G ⟩) → (g ♯) ♭ ≡ g
  ♭♯ g = refl

  ♯♭ : (f : GroupHom (FG.freeGroupGroup X) G) → (f ♭) ♯ ≡ f
  ♯♭ f = FG.freeGroupHom≡ λ _ → refl

  univ : isEquiv _♭
  univ = isoToIsEquiv (iso _♭ _♯ ♭♯ ♯♭)

  ♭-inj : {f g : GroupHom (FG.freeGroupGroup X) G} → f ♭ ≡ g ♭ → f ≡ g
  ♭-inj {f} {g} p = sym (♯♭ f) ∙ ap _♯ p ∙ ♯♭ g

module _ {X : Type ℓ} {G : Group ℓ'} {H : Group ℓ''} where

  private
    module G = FreeGroupUniv G {X = X}
    module H = FreeGroupUniv H {X = X}

  ♯-natural : (f : GroupHom G H) (g : X → ⟨ G ⟩) → f ∘ᵍ (g G.♯) ≡ (f .fst ∘ g) H.♯
  ♯-natural f g = H.♭-inj refl

-- relations between words

infix 4 _≐_

record Relation (X : Type ℓ) : Type ℓ where
  constructor _≐_
  field
    lhs rhs : FreeGroup X

-- presentations by generators and relations

record Presentation (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor presentation
  field
    Gens : Type ℓ
    Rels : Type ℓ
    relation : Rels → Relation Gens

open Presentation public

⟨_∣_⟩ : (X : Type ℓ) {Rels : Type ℓ} → (Rels → Relation X) → Presentation ℓ
⟨ X ∣ R ⟩ = presentation X _ R

-- models of a presentation

record Model (P : Presentation ℓ) (G : Group ℓ') : Type (ℓ-max ℓ ℓ') where
  open FreeGroupUniv G using ( _♯ )
  field
    gen : Gens P → ⟨ G ⟩
    rel : (r : Rels P) → (gen ♯) .fst (relation P r .Relation.lhs) ≡ (gen ♯) .fst (relation P r .Relation.rhs)

open Model public

syntax Model P G = G ⊨ P

module _ {P : Presentation ℓ} {G : Group ℓ'} where

  open GroupStr (G .snd) using ( is-set )
  open FreeGroupUniv G using ( _♯ )

  Model≡ : {M M' : G ⊨ P} → M .gen ≡ M' .gen → M ≡ M'
  Model≡ p i .gen = p i
  Model≡ {M} {M'} p i .rel r =
    isProp→PathP (λ i → is-set ((p i ♯) .fst lhs) ((p i ♯) .fst rhs)) (M .rel r) (M' .rel r) i
    where open Relation (relation P r)

  mapModel : {H : Group ℓ''} → GroupHom G H → G ⊨ P → H ⊨ P
  mapModel f M .gen = f .fst ∘ M .gen
  mapModel {H = H} f M .rel r =
    ((f .fst ∘ M .gen) H.♯) .fst lhs
      ≡⟨ ap (λ φ → φ .fst lhs) (sym (♯-natural f (M .gen))) ⟩
    f .fst ((M .gen ♯) .fst lhs)
      ≡⟨ ap (f .fst) (M .rel r) ⟩
    f .fst ((M .gen ♯) .fst rhs)
      ≡⟨ ap (λ φ → φ .fst rhs) (♯-natural f (M .gen)) ⟩
    ((f .fst ∘ M .gen) H.♯) .fst rhs
      ∎
    where
      module H = FreeGroupUniv H
      open Relation (relation P r)
