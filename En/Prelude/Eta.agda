module En.Prelude.Eta where

open import En.Prelude.Base
open import Cubical.Data.Sum

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

-- useful eta laws instead of pattern matching

⊎-ηP : {P : I → A ⊎ B → Type ℓ''} {f : (x : A ⊎ B) → P i0 x} {g : (x : A ⊎ B) → P i1 x}
  → PathP (λ i → (a : A) → P i (inl a)) (λ a → f (inl a)) (λ a → g (inl a))
  → PathP (λ i → (b : B) → P i (inr b)) (λ b → f (inr b)) (λ b → g (inr b))
  → PathP (λ i → (x : A ⊎ B) → P i x) f g
⊎-ηP p q i (inl a) = p i a
⊎-ηP p q i (inr b) = q i b

⊎-η : {C : Type ℓ''} {f g : A ⊎ B → C}
  → (λ (a : A) → f (inl a)) ≡ (λ a → g (inl a)) → (λ (b : B) → f (inr b)) ≡ (λ b → g (inr b)) → f ≡ g
⊎-η p q i (inl a) = p i a
⊎-η p q i (inr b) = q i b

×-η : {C : Type ℓ''} {f g : A × B → C} → (λ (a : A) (b : B) → f (a , b)) ≡ (λ a b → g (a , b)) → f ≡ g
×-η p i (a , b) = p i a b

⊥*-ηP : {P : I → ⊥* {ℓ} → Type ℓ''} {f : (x : ⊥*) → P i0 x} {g : (x : ⊥*) → P i1 x}
  → PathP (λ i → (x : ⊥*) → P i x) f g
⊥*-ηP i (lift ())

⊥*-η : {C : Type ℓ''} {f g : ⊥* {ℓ} → C} → f ≡ g
⊥*-η i (lift ())
