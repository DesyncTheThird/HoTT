module En.Prelude.Except where

open import En.Prelude.Base
open import Cubical.Foundations.Equiv.Properties using ( preCompEquiv ; congEquiv )
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎ using ( _⊎_ ; inl ; inr )
open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Relation.Nullary.Properties using ( isProp¬ )

private
  variable
    A : Type ℓ
    B : Type ℓ'
    X : Type ℓ''

-- complement of a point

Except : (A : Type ℓ) → A → Type ℓ
Except A a = Σ[ x ∈ A ] ¬ a ≡ x

infix 10 _∖_

_∖_ : (A : Type ℓ) → A → Type ℓ
_∖_ = Except

∖-cong : (e : A ≃ B) (a : A) → A ∖ a ≃ B ∖ –> e a
∖-cong e a = Σ-cong-equiv e λ _ → preCompEquiv (invEquiv (congEquiv e))

-- adding and removing a point

∖inr≃ : X ≃ (X ⊎ Unit) ∖ inr tt
∖inr≃ {X = X} = isoToEquiv i
  where
    open Iso
    i : Iso X ((X ⊎ Unit) ∖ inr tt)
    i .fun x = inl x , ⊎.⊎Path.inl≢inr x tt ∘ sym
    i .inv (inl x , _) = x
    i .inv (inr _ , p) = ⊥.rec (p refl)
    i .sec (inl x , p) = Σ≡Prop (λ _ → isProp¬ _) refl
    i .sec (inr _ , p) = ⊥.rec (p refl)
    i .ret x = refl

∖⊎Unit≃ : Discrete A → (a : A) → (A ∖ a) ⊎ Unit ≃ A
∖⊎Unit≃ {A = A} _≟_ a = isoToEquiv i
  where
    open Iso
    insert : (A ∖ a) ⊎ Unit → A
    insert = ⊎.rec fst (λ _ → a)
    remove : (x : A) → Dec (a ≡ x) → (A ∖ a) ⊎ Unit
    remove x (yes _) = inr tt
    remove x (no p) = inl (x , p)
    insert∘remove : (x : A) (d : Dec (a ≡ x)) → insert (remove x d) ≡ x
    insert∘remove x (yes p) = p
    insert∘remove x (no _) = refl
    remove∘inl : (x : A) (p : ¬ a ≡ x) (d : Dec (a ≡ x)) → remove x d ≡ inl (x , p)
    remove∘inl x p (yes q) = ⊥.rec (p q)
    remove∘inl x p (no q) = ap inl (Σ≡Prop (λ _ → isProp¬ _) refl)
    remove∘inr : (d : Dec (a ≡ a)) → remove a d ≡ inr tt
    remove∘inr (yes _) = refl
    remove∘inr (no q) = ⊥.rec (q refl)
    i : Iso ((A ∖ a) ⊎ Unit) A
    i .fun = insert
    i .inv x = remove x (a ≟ x)
    i .sec x = insert∘remove x (a ≟ x)
    i .ret (inl (x , p)) = remove∘inl x p (a ≟ x)
    i .ret (inr _) = remove∘inr (a ≟ a)

-- equivalences with the image of the point

⊎Unit≃Σ∖ : Discrete B → ((X ⊎ Unit) ≃ B) ≃ (Σ[ b ∈ B ] (X ≃ B ∖ b))
⊎Unit≃Σ∖ {B = B} {X = X} _≟_ = isoToEquiv i
  where
    open Iso
    i : Iso ((X ⊎ Unit) ≃ B) (Σ[ b ∈ B ] (X ≃ B ∖ b))
    i .fun e = –> e (inr tt) , ∖inr≃ ∙ₑ ∖-cong e (inr tt)
    i .inv (b , g) = ⊎.⊎-equiv g (idEquiv Unit) ∙ₑ ∖⊎Unit≃ _≟_ b
    i .sec (b , g) = ΣPathP (refl , equivEq (funExt λ x → Σ≡Prop (λ _ → isProp¬ _) refl))
    i .ret e = equivEq (funExt λ { (inl x) → refl ; (inr _) → refl })
