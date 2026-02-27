module En.Prelude where

open import Cubical.Foundations.Prelude renaming (congS to ap ; cong to apd ; congP to apP; subst to tpt) public
open import Cubical.Foundations.Transport public
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Path public
open import Cubical.Foundations.GroupoidLaws public

Square→Triangle₂ : ∀ {ℓ} {A : Type ℓ} {a b d : A} {q : b ≡ d} {r : a ≡ b} {s : a ≡ d} → Square r s refl q → s ≡ r ∙ q
Square→Triangle₂ {s = s} sq =
  lUnit s ∙ Square→compPath sq

Square→Triangle₃ : ∀ {ℓ} {A : Type ℓ} {a b c : A} {p : a ≡ c} {r : a ≡ b} {s : c ≡ b} → Square r s p refl → p ∙ s ≡ r
Square→Triangle₃ {r = r} sq =
  Square→compPath sq ∙ sym (rUnit r)
