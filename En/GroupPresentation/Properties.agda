module En.GroupPresentation.Properties where

open import En.Prelude hiding ( _·_ )
open import En.Prelude.Group
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import En.GroupPresentation.Base

-- generated groups

isGenerated : {P : Presentation ℓ} {G : Group ℓ'} → G ⊨ P → Type (ℓ-max ℓ ℓ')
isGenerated {G = G} ηM = isSurjection ((ηM .gen ♯) .fst)
  where open FreeGroupUniv G using ( _♯ )

module _ {P : Presentation ℓ} {G : Group ℓ'} (ηM : G ⊨ P) (isGeneratedG : isGenerated ηM) where

  generatedHom≡ : {H : Group ℓ''} {f g : GroupHom G H}
    → ((x : Gens P) → f .fst (ηM .gen x) ≡ g .fst (ηM .gen x)) → f ≡ g
  generatedHom≡ {H = H} {f} {g} p =
    GroupHom≡ (funExt λ y → PT.rec (is-set _ _) (onFibre y) (isGeneratedG y))
    where
      open GroupStr (H .snd) using ( is-set )
      open FreeGroupUniv H using ( _♯ )
      module G = FreeGroupUniv G
      onWords : f ∘ᵍ (ηM .gen G.♯) ≡ g ∘ᵍ (ηM .gen G.♯)
      onWords =
        f ∘ᵍ (ηM .gen G.♯)
          ≡⟨ ♯-natural f (ηM .gen) ⟩
        (f .fst ∘ ηM .gen) ♯
          ≡⟨ ap _♯ (funExt p) ⟩
        (g .fst ∘ ηM .gen) ♯
          ≡⟨ sym (♯-natural g (ηM .gen)) ⟩
        g ∘ᵍ (ηM .gen G.♯)
          ∎
      onFibre : (y : ⟨ G ⟩) → fiber ((ηM .gen G.♯) .fst) y → f .fst y ≡ g .fst y
      onFibre y (w , q) =
        f .fst y
          ≡⟨ ap (f .fst) (sym q) ⟩
        (f ∘ᵍ (ηM .gen G.♯)) .fst w
          ≡⟨ ap (λ φ → φ .fst w) onWords ⟩
        (g ∘ᵍ (ηM .gen G.♯)) .fst w
          ≡⟨ ap (g .fst) q ⟩
        g .fst y
          ∎

-- equivalences between generated groups

module _ {P : Presentation ℓ} {Q : Presentation ℓ''} {G : Group ℓ'} {H : Group ℓ'''}
  (ηM : G ⊨ P) (ηN : H ⊨ Q) (isGeneratedG : isGenerated ηM) (isGeneratedH : isGenerated ηN)
  (φ : GroupHom G H) (ψ : GroupHom H G)
  where

  generatedEquiv : ((x : Gens P) → ψ .fst (φ .fst (ηM .gen x)) ≡ ηM .gen x)
    → ((y : Gens Q) → φ .fst (ψ .fst (ηN .gen y)) ≡ ηN .gen y) → GroupEquiv G H
  generatedEquiv p q .fst = isoToEquiv (iso (φ .fst) (ψ .fst) sec ret)
    where
      sec : (y : ⟨ H ⟩) → φ .fst (ψ .fst y) ≡ y
      sec = funExt⁻ (ap fst (generatedHom≡ ηN isGeneratedH {f = φ ∘ᵍ ψ} {g = idGroupHom} q))
      ret : (x : ⟨ G ⟩) → ψ .fst (φ .fst x) ≡ x
      ret = funExt⁻ (ap fst (generatedHom≡ ηM isGeneratedG {f = ψ ∘ᵍ φ} {g = idGroupHom} p))
  generatedEquiv p q .snd = φ .snd

-- universal property of a presented group

module Presented {P : Presentation ℓ} {G : Group ℓ'} (ηM : G ⊨ P) (isGeneratedG : isGenerated ηM)
  (H : Group ℓ'') (_♯ : H ⊨ P → GroupHom G H) (♯-η : (M : H ⊨ P) (x : Gens P) → (M ♯) .fst (ηM .gen x) ≡ M .gen x)
  where

  _♭ : GroupHom G H → H ⊨ P
  f ♭ = mapModel f ηM

  ♭♯ : (M : H ⊨ P) → (M ♯) ♭ ≡ M
  ♭♯ M = Model≡ (funExt (♯-η M))

  ♯♭ : (f : GroupHom G H) → (f ♭) ♯ ≡ f
  ♯♭ f = generatedHom≡ ηM isGeneratedG (♯-η (f ♭))

  univ : isEquiv _♭
  univ = isoToIsEquiv (iso _♭ _♯ ♭♯ ♯♭)

  ♭-inj : {f g : GroupHom G H} → f ♭ ≡ g ♭ → f ≡ g
  ♭-inj {f} {g} p = sym (♯♭ f) ∙ ap _♯ p ∙ ♯♭ g
