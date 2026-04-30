module En.Prelude.Squares where

open import En.Prelude.Base public

private
  variable
    ℓ : Level
    A B C D E F G H : Type ℓ

postulate
    sorry : ∀ {l} {A : Type l} → A

foo : {a b c d : A}
      (p : a ≡ b)
      (q : c ≡ d)
      (r : a ≡ c)
      (s : b ≡ d)
      → Square p q r s → Square refl (r ∙ q) refl (p ∙ s)
foo p q r s sq = sorry
