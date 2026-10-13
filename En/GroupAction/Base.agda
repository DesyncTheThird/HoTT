module En.GroupAction.Base where

open import En.Prelude hiding ( _·_ )
open import En.Prelude.Group
open import Cubical.HITs.SetTruncation as ST using ( ∥_∥₂ ; ∣_∣₂ ; squash₂ )
open import Cubical.HITs.SetQuotients as SQ using ( _/_ ; [_] )
open import Cubical.HITs.GroupoidQuotients as GQ using ( _//_ ; eq// )
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.SymmetricGroup

-- right actions of a group on a type

record Action (G : Group ℓ) (Y : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor action
  open GroupNotation G
  infixl 20 _▹_
  field
    _▹_ : Y → ⟨ G ⟩ → Y
    ▹Assoc : (y : Y) (g h : ⟨ G ⟩) → y ▹ (g · h) ≡ (y ▹ g) ▹ h
    ▹IdR : (y : Y) → y ▹ 1g ≡ y

  ▹InvR : (y : Y) (g : ⟨ G ⟩) → (y ▹ g) ▹ g ⁻¹ᵍ ≡ y
  ▹InvR y g =
    (y ▹ g) ▹ g ⁻¹ᵍ
      ≡⟨ sym (▹Assoc y g (g ⁻¹ᵍ)) ⟩
    y ▹ (g · g ⁻¹ᵍ)
      ≡⟨ ap (y ▹_) (·InvR g) ⟩
    y ▹ 1g
      ≡⟨ ▹IdR y ⟩
    y
      ∎

open Action public using ( ▹Assoc ; ▹IdR ; ▹InvR )

infixl 20 _▹⟨_⟩_

_▹⟨_⟩_ : {G : Group ℓ} {Y : Type ℓ'} → Y → Action G Y → ⟨ G ⟩ → Y
y ▹⟨ φ ⟩ g = Action._▹_ φ y g

-- canonical action of an automorphism group, and restriction

module _ where

  open Action using ( _▹_ )

  autAction : (X : Type ℓ) (isSetX : isSet X) → Action (SymGroup X isSetX) X
  autAction X isSetX ._▹_ x e = –> e x
  autAction X isSetX .▹Assoc x e f = refl
  autAction X isSetX .▹IdR x = refl

  restrictAction : {G : Group ℓ} {H : Group ℓ''} {Y : Type ℓ'} → GroupHom H G → Action G Y → Action H Y
  restrictAction ψ φ ._▹_ y h = y ▹⟨ φ ⟩ ψ .fst h
  restrictAction ψ φ .▹Assoc y g h = ap (y ▹⟨ φ ⟩_) (IsGroupHom.pres· (ψ .snd) g h) ∙ ▹Assoc φ y _ _
  restrictAction ψ φ .▹IdR y = ap (y ▹⟨ φ ⟩_) (IsGroupHom.pres1 (ψ .snd)) ∙ ▹IdR φ y

-- actions on functions, by precomposition

module _ {G : Group ℓ} where

  open GroupNotation G
  open Action using ( _▹_ )

  preCompAction : {X : Type ℓ'} → Action G X → (A : Type ℓ'') → Action G (X → A)
  preCompAction φ A ._▹_ v g x = v (x ▹⟨ φ ⟩ g ⁻¹ᵍ)
  preCompAction φ A .▹Assoc v g h = funExt λ x →
    ap v (ap (x ▹⟨ φ ⟩_) (GroupTheory.invDistr G g h) ∙ ▹Assoc φ x _ _)
  preCompAction φ A .▹IdR v = funExt λ x →
    ap v (ap (x ▹⟨ φ ⟩_) (GroupTheory.inv1g G) ∙ ▹IdR φ x)

module _ {G : Group ℓ} {Y : Type ℓ'} (φ : Action G Y) where

  open GroupStr (G .snd)
  open Action φ using ( _▹_ )

  -- action groupoid

  ActionRel : Y → Y → Type (ℓ-max ℓ ℓ')
  ActionRel x y = Σ[ g ∈ ⟨ G ⟩ ] x ▹ g ≡ y

  isTransActionRel : BinaryRelation.isTrans ActionRel
  isTransActionRel x y z (g , p) (h , q) =
    g · h ,
      (x ▹ (g · h)
        ≡⟨ ▹Assoc φ x g h ⟩
      (x ▹ g) ▹ h
        ≡⟨ ap (_▹ h) p ⟩
      y ▹ h
        ≡⟨ q ⟩
      z
        ∎)

  ActionGroupoid : Type (ℓ-max ℓ ℓ')
  ActionGroupoid = Y // isTransActionRel

  -- set of orbits
  OrbitSet : Type (ℓ-max ℓ ℓ')
  OrbitSet = Y / ActionRel

  isSetOrbitSet : isSet OrbitSet
  isSetOrbitSet = SQ.squash/

  -- orbits are truncated action groupoid
  ∥ActionGroupoid∥₂≃OrbitSet : ∥ ActionGroupoid ∥₂ ≃ OrbitSet
  ∥ActionGroupoid∥₂≃OrbitSet = isoToEquiv (iso to from to-from from-to)
    where
      to : ∥ ActionGroupoid ∥₂ → OrbitSet
      to = ST.rec SQ.squash/
        (GQ.rec isTransActionRel (isSet→isGroupoid SQ.squash/) [_] (SQ.eq/ _ _)
          λ _ _ → isSet→SquareP (λ _ _ → SQ.squash/) _ _ _ _)

      from : OrbitSet → ∥ ActionGroupoid ∥₂
      from = SQ.rec squash₂ (λ y → ∣ GQ.[ y ] ∣₂) λ _ _ r → ap ∣_∣₂ (eq// r)

      to-from : (x : OrbitSet) → to (from x) ≡ x
      to-from = SQ.elimProp (λ _ → SQ.squash/ _ _) λ _ → refl

      from-to : (x : ∥ ActionGroupoid ∥₂) → from (to x) ≡ x
      from-to = ST.elim (λ _ → isProp→isSet (squash₂ _ _))
        (GQ.elimProp isTransActionRel (λ _ → squash₂ _ _) λ _ → refl)

  -- transitive action
  isTransitive : Type (ℓ-max ℓ ℓ')
  isTransitive = (x y : Y) → ∥ ActionRel x y ∥₁

  -- transversal of the orbit of x₀
  Transversal : Y → Type (ℓ-max ℓ ℓ')
  Transversal x₀ = Σ[ c ∈ (Y → ⟨ G ⟩) ] ((y : Y) → x₀ ▹ c y ≡ y)

-- transversals compose with homomorphisms

compTransversal : {G : Group ℓ} {H : Group ℓ''} {Y : Type ℓ'} (ψ : GroupHom G H) (φ : Action H Y) {x₀ : Y}
  → Transversal (restrictAction ψ φ) x₀ → Transversal φ x₀
compTransversal ψ φ (c , c-path) = ψ .fst ∘ c , c-path

-- stabilisers

module _ {G : Group ℓ} {X : Type ℓ} (isSetX : isSet X) (φ : Action G X) where

  open GroupNotation G
  open Action φ using ( _▹_ )
  open isSubgroup

  Stabiliser : X → Subgroup G
  Stabiliser x .fst g = (x ▹ g ≡ x) , isSetX _ _
  Stabiliser x .snd .id-closed = ▹IdR φ x
  Stabiliser x .snd .op-closed {g} {h} p q =
    x ▹ (g · h)
      ≡⟨ ▹Assoc φ x g h ⟩
    (x ▹ g) ▹ h
      ≡⟨ ap (_▹ h) p ⟩
    x ▹ h
      ≡⟨ q ⟩
    x
      ∎
  Stabiliser x .snd .inv-closed {g} p = sym (ap (_▹ g ⁻¹ᵍ) p) ∙ ▹InvR φ x g

-- wreath product groupoids

module _ {G : Group ℓ} {X : Type ℓ'} (φ : Action G X) (A : Type ℓ'') where

  WreathRel : (X → A) → (X → A) → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  WreathRel = ActionRel (preCompAction φ A)

  WreathGroupoid : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  WreathGroupoid = ActionGroupoid (preCompAction φ A)

infix 25 _≀_

_≀_ : {G : Group ℓ} {X : Type ℓ'} (A : Type ℓ'') → Action G X → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
A ≀ φ = WreathGroupoid φ A
