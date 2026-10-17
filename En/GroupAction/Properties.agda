module En.GroupAction.Properties where

open import En.Prelude hiding ( _·_ )
open import En.Prelude.Group
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import En.GroupoidQuotients.Properties
open import En.GroupAction.Base

-- orbit–stabiliser theorem

module _ {G : Group ℓ} {X : Type ℓ} (isSetX : isSet X) (φ : Action G X) (x₀ : X) (t : Transversal φ x₀) where

  open GroupNotation G
  open Action φ using ( _▹_ )

  private
    c = t .fst
    c-path = t .snd

  orbitStabiliser : ⟨ G ⟩ ≃ X × ⟨ Subgroup→Group G (Stabiliser isSetX φ x₀) ⟩
  orbitStabiliser = isoToEquiv (iso G→X×Stab X×Stab→G X×Stab→G→X×Stab G→X×Stab→G)
    where
      orbitMap : ⟨ G ⟩ → X
      orbitMap g = x₀ ▹ g

      stabPart : ⟨ G ⟩ → ⟨ Subgroup→Group G (Stabiliser isSetX φ x₀) ⟩
      stabPart g = g · c y ⁻¹ᵍ , fixes
        where
          y = orbitMap g
          fixes : x₀ ▹ (g · c y ⁻¹ᵍ) ≡ x₀
          fixes =
            x₀ ▹ (g · c y ⁻¹ᵍ)
              ≡⟨ ▹Assoc φ x₀ g (c y ⁻¹ᵍ) ⟩
            y ▹ c y ⁻¹ᵍ
              ≡⟨ ap (_▹ c y ⁻¹ᵍ) (sym (c-path y)) ⟩
            (x₀ ▹ c y) ▹ c y ⁻¹ᵍ
              ≡⟨ ▹InvR φ x₀ (c y) ⟩
            x₀
              ∎

      G→X×Stab : ⟨ G ⟩ → X × ⟨ Subgroup→Group G (Stabiliser isSetX φ x₀) ⟩
      G→X×Stab g = orbitMap g , stabPart g

      X×Stab→G : X × ⟨ Subgroup→Group G (Stabiliser isSetX φ x₀) ⟩ → ⟨ G ⟩
      X×Stab→G (y , s , _) = s · c y

      X×Stab→G→X×Stab : (u : X × ⟨ Subgroup→Group G (Stabiliser isSetX φ x₀) ⟩) → G→X×Stab (X×Stab→G u) ≡ u
      X×Stab→G→X×Stab (y , s , p) = ≡-× q (Σ≡Prop (λ _ → isSetX _ _) r)
        where
          q : x₀ ▹ (s · c y) ≡ y
          q =
            x₀ ▹ (s · c y)
              ≡⟨ ▹Assoc φ x₀ s (c y) ⟩
            (x₀ ▹ s) ▹ c y
              ≡⟨ ap (_▹ c y) p ⟩
            x₀ ▹ c y
              ≡⟨ c-path y ⟩
            y
              ∎
          r : (s · c y) · c (x₀ ▹ (s · c y)) ⁻¹ᵍ ≡ s
          r =
            (s · c y) · c (x₀ ▹ (s · c y)) ⁻¹ᵍ
              ≡⟨ ap (λ z → (s · c y) · c z ⁻¹ᵍ) q ⟩
            (s · c y) · c y ⁻¹ᵍ
              ≡⟨ sym (·Assoc s (c y) (c y ⁻¹ᵍ)) ⟩
            s · (c y · c y ⁻¹ᵍ)
              ≡⟨ ap (s ·_) (·InvR (c y)) ⟩
            s · 1g
              ≡⟨ ·IdR s ⟩
            s
              ∎

      G→X×Stab→G : (g : ⟨ G ⟩) → X×Stab→G (G→X×Stab g) ≡ g
      G→X×Stab→G g =
        (g · c y ⁻¹ᵍ) · c y
          ≡⟨ sym (·Assoc g (c y ⁻¹ᵍ) (c y)) ⟩
        g · (c y ⁻¹ᵍ · c y)
          ≡⟨ ap (g ·_) (·InvL (c y)) ⟩
        g · 1g
          ≡⟨ ·IdR g ⟩
        g
          ∎
        where y = orbitMap g

-- orbit–stabiliser along a homomorphism

module _ {G H : Group ℓ} {X : Type ℓ} (isSetX : isSet X) (ψ : GroupHom G H) (φ : Action H X)
  (x₀ : X) (t : Transversal (restrictAction ψ φ) x₀)
  where

  private
    φG : Action G X
    φG = restrictAction ψ φ
    c = t .fst
    module G = GroupNotation G
    module H = GroupNotation H
    open IsGroupHom (ψ .snd)

  stabiliserMap : ⟨ Subgroup→Group G (Stabiliser isSetX φG x₀) ⟩ → ⟨ Subgroup→Group H (Stabiliser isSetX φ x₀) ⟩
  stabiliserMap (g , p) = ψ .fst g , p

  -- orbit-stabiliser commutes with psi:
  --
  --              OSG
  --      G -----------> X x Stab_G(x0)
  --      |                   |
  --  psi |                   | id x stabiliserMap
  --      v                   v
  --      H -----------> X x Stab_H(x0)
  --              OSH

  orbitStabiliserNatural : (g : ⟨ G ⟩)
    → –> (orbitStabiliser isSetX φ x₀ (compTransversal ψ φ t)) (ψ .fst g)
    ≡ map-× (idfun X) stabiliserMap (–> (orbitStabiliser isSetX φG x₀ t) g)
  orbitStabiliserNatural g = ≡-× refl (Σ≡Prop (λ _ → isSetX _ _)
    (ψ .fst g H.· ψ .fst (c y) H.⁻¹ᵍ
      ≡⟨ ap (ψ .fst g H.·_) (sym (presinv (c y))) ⟩
    ψ .fst g H.· ψ .fst (c y G.⁻¹ᵍ)
      ≡⟨ sym (pres· g (c y G.⁻¹ᵍ)) ⟩
    ψ .fst (g G.· c y G.⁻¹ᵍ)
      ∎))
    where y = x₀ ▹⟨ φG ⟩ g

  -- equivalences on stabilisers lift to equivalences

  isEquivStabiliserMap→isEquiv : isEquiv stabiliserMap → isEquiv (ψ .fst)
  isEquivStabiliserMap→isEquiv e = tpt isEquiv (sym (funExt path)) (composite .snd)
    where
      OSG = orbitStabiliser isSetX φG x₀ t
      OSH = orbitStabiliser isSetX φ x₀ (compTransversal ψ φ t)
      composite =
        ⟨ G ⟩
          ≃⟨ OSG ⟩
        X × ⟨ Subgroup→Group G (Stabiliser isSetX φG x₀) ⟩
          ≃⟨ ≃-× (idEquiv X) (stabiliserMap , e) ⟩
        X × ⟨ Subgroup→Group H (Stabiliser isSetX φ x₀) ⟩
          ≃⟨ OSH ⁻¹ₑ ⟩
        ⟨ H ⟩
          ■
      path : (g : ⟨ G ⟩) → ψ .fst g ≡ –> composite g
      path g =
        ψ .fst g
          ≡⟨ sym (retEq OSH (ψ .fst g)) ⟩
        <– OSH (–> OSH (ψ .fst g))
          ≡⟨ ap (<– OSH) (orbitStabiliserNatural g) ⟩
        –> composite g
          ∎

-- change of group

module _ {G H : Group ℓ} {Y : Type ℓ'} (ψ : GroupEquiv G H) (φG : Action G Y) (φH : Action H Y)
  (h : (y : Y) (g : ⟨ G ⟩) → y ▹⟨ φG ⟩ g ≡ y ▹⟨ φH ⟩ –>ᵍ ψ g)
  where

  ActionRel≃ : {x y : Y} → ActionRel φG x y ≃ ActionRel φH x y
  ActionRel≃ {x} {y} = Σ-cong-equiv (GroupEquiv→Equiv ψ) λ g → compPathlEquiv (sym (h x g))

  ActionGroupoid≃ : ActionGroupoid φG ≃ ActionGroupoid φH
  ActionGroupoid≃ =
    //-cong (isTransActionRel φG) (isTransActionRel φH) (λ {x} {y} → ActionRel≃ {x} {y})
      (λ r s → sorry)
      -- TODO: ActionRel≃ preserves composition (ActionGroupoid≃)
      --  from pres· of ψ and naturality of h

-- change of group for wreath products

module _ {G H : Group ℓ} {X : Type ℓ'} (ψ : GroupEquiv G H) (φ : Action H X) (A : Type ℓ'') where

  WreathGroupoid≃ : A ≀ restrictAction (GroupEquiv→GroupHom ψ) φ ≃ A ≀ φ
  WreathGroupoid≃ =
    ActionGroupoid≃ ψ (preCompAction (restrictAction (GroupEquiv→GroupHom ψ) φ) A) (preCompAction φ A)
      λ v g → funExt λ x → ap v (ap (x ▹⟨ φ ⟩_) (IsGroupHom.presinv (ψ .snd) g))
