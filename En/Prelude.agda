module En.Prelude where

open import Cubical.Foundations.Prelude renaming (congS to ap ; cong to apd ; congP to apP; subst to tpt) public
open import Cubical.Foundations.Transport public
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Path public
open import Cubical.Foundations.GroupoidLaws public
open import Cubical.Foundations.Function public

-- Triangle→compPath : ∀ {ℓ} {A : Type ℓ} {a b c d : A} {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d} → Square r s p q → p ∙ s ≡ r ∙ q
-- Triangle→compPath = Square→compPath

Triangle→compPath₀ : ∀ {ℓ} {A : Type ℓ} {a b d : A} {p : a ≡ b} {q : a ≡ d} {s : b ≡ d}
    → Square refl s p q → p ∙ s ≡ q
Triangle→compPath₀ {q = q} sq = Square→compPath sq ∙ sym (lUnit q)

Triangle→compPath₁ : ∀ {ℓ} {A : Type ℓ} {a b c d : A} {p : a ≡ b} {q : c ≡ b} {r : a ≡ c} → Square r refl p q → p ≡ r ∙ q
Triangle→compPath₁ {p = p} sq = rUnit p ∙ Square→compPath sq

Triangle→compPath₂ : ∀ {ℓ} {A : Type ℓ} {a b d : A} {q : b ≡ d} {r : a ≡ b} {s : a ≡ d}
    → Square r s refl q → s ≡ r ∙ q
Triangle→compPath₂ {s = s} sq = lUnit s ∙ Square→compPath sq

Triangle→compPath₃ : ∀ {ℓ} {A : Type ℓ} {a b c : A} {p : a ≡ c} {r : a ≡ b} {s : c ≡ b}
    → Square r s p refl → p ∙ s ≡ r
Triangle→compPath₃ {r = r} sq = Square→compPath sq ∙ sym (rUnit r)

--   b
-- a   c
--  d e

Pentagon→compPath : ∀ {ℓ} {A : Type ℓ} {a b c d e : A}
    {p : a ≡ b} {q : b ≡ c} {r : a ≡ d} {s : d ≡ e} {t : e ≡ c}
    (⬠₌ : a ≡ c)
    (⬠₁ : Square (sym p) q refl ⬠₌)
    (⬠₂ : Square r (sym t) ⬠₌ s)
    → p ∙ q ≡ r ∙ s ∙ t
Pentagon→compPath {p = p} {q = q} {r = r} {s = s} {t = t} ⬠₌ ⬠₁ ⬠₂ =
    let ⬠₁ = Triangle→compPath₂ ⬠₁
        ⬠₂ = Square→compPath ⬠₂
        P : p ∙ q ≡ ⬠₌
        P = ap (p ∙_) ⬠₁ ∙ assoc p (sym p) ⬠₌ ∙ ap (_∙ ⬠₌) (rCancel p) ∙ sym (lUnit ⬠₌)
        Q : ⬠₌ ≡ r ∙ (s ∙ t)
        Q = rUnit ⬠₌ ∙ ap (⬠₌ ∙_) (sym (lCancel t)) ∙ assoc ⬠₌ (sym t) t ∙ ap (_∙ t) ⬠₂ ∙ sym (assoc r s t)
    in P ∙ Q

--   b c
-- a     d
--   e f

Hexagon→compPath : ∀ {ℓ} {A : Type ℓ} {a b c d e f : A}
    {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
    (⬡₌ : a ≡ d)
    (⬡₁ : Square (sym p) r q ⬡₌)
    (⬡₂ : Square s (sym u) ⬡₌ t)
    → p ∙ q ∙ r ≡ s ∙ t ∙ u
Hexagon→compPath {p = p} {q = q} {r = r} {s = s} {t = t} {u = u} ⬡₌ ⬡₁ ⬡₂ =
    let ⬡₁ = Square→compPath ⬡₁
        ⬡₂ = Square→compPath ⬡₂
        P : p ∙ q ∙ r ≡ ⬡₌
        P = ap (p ∙_) ⬡₁ ∙ assoc p (sym p) ⬡₌ ∙ ap (_∙ ⬡₌) (rCancel p) ∙ sym (lUnit ⬡₌)
        Q : ⬡₌ ≡ s ∙ t ∙ u
        Q = rUnit ⬡₌ ∙ ap (⬡₌ ∙_) (sym (lCancel u)) ∙ assoc ⬡₌ (sym u) u ∙ ap (_∙ u) ⬡₂ ∙ sym (assoc s t u)
    in P ∙ Q
