module En.Prelude.Ap where

open import En.Prelude.Base public

ap₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  (f : A → B → C) {x x' : A} {y y' : B}
  (p : x ≡ x') (q : y ≡ y')
  → f x y ≡ f x' y'
ap₂ f p q i =
  f (p i) (q i)

ap₂-coh₁ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  (f : A → B → C) {x x' : A} {y y' : B}
  (p : x ≡ x') (q : y ≡ y')
  → Square (ap (λ x → f x y) p) refl (ap₂ f p q) (ap (λ b → f x' b) q)
ap₂-coh₁ f {x = x} {x'} {y} {y'} p q i j = f (p (i ∨ j)) (q i)

ap₂-coh₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  (f : A → B → C) {x x' : A} {y y' : B}
  (p : x ≡ x') (q : y ≡ y')
  → Square (ap (λ b → f x b) q) (ap₂ f p q) refl (ap (λ x → f x y') p)
ap₂-coh₂ f p q i j = f (p (i ∧ j)) (q j)

ap₃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
  (f : A → B → C → D) {x x' : A} {y y' : B} {z z' : C}
  (p : x ≡ x') (q : y ≡ y') (r : z ≡ z')
  → f x y z ≡ f x' y' z'
ap₃ f p q r i =
  f (p i) (q i) (r i)

ap₃-coh₁ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
  (f : A → B → C → D) {x x' : A} {y y' : B} {z z' : C}
  (p : x ≡ x') (q : y ≡ y') (r : z ≡ z')
  → Square (ap (λ x → f x y z) p) (sym (ap (λ z → f x' y' z) r)) (ap₃ f p q r) (ap (λ y → f x' y z) q)
ap₃-coh₁ f p q r i j = f (p (i ∨ j)) (q i) (r (i ∧ ~ j))

ap₃-coh₂ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
  (f : A → B → C → D) {x x' : A} {y y' : B} {z z' : C}
  (p : x ≡ x') (q : y ≡ y') (r : z ≡ z')
  → Square (ap (λ z → f x y z) r) (sym (ap (λ x → f x y' z') p)) (ap₃ f p q r) (ap (λ y → f x y z') q)
ap₃-coh₂ f p q r i j = f (p (i ∧ ~ j)) (q i) (r (i ∨ j))

-- ap₃-coh₃ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
--   (f : A → B → C → D) {x x' : A} {y y' : B} {z z' : C}
--   (p : x ≡ x') (q : y ≡ y') (r : z ≡ z')
--   → Square (ap (λ y → f x y z) q) (sym (ap (λ y → f x' y z') q)) (ap₃ f p q r) {! !}
-- ap₃-coh₃ f p q r i j = {!!} {!!} {!!} {!!}






private
  variable
    ℓ : Level
    A B C D E F G H : Type ℓ



ap₂-∙ : {X X' X'' : A} {Y Y' Y'' : B}
  (f : A → B → C)
  (p : X ≡ X')
  (q : X' ≡ X'')
  (r : Y ≡ Y')
  (s : Y' ≡ Y'')
  → ap₂ f (p ∙ q) (r ∙ s) ≡ (ap₂ f p r) ∙ (ap₂ f q s)
ap₂-∙ {X = X} {X'} {X''} {Y} {Y'} {Y''} f p q r s =
  let Q : ∀ {ℓ} {A : Type ℓ} {a b c d : A} {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d}
        (S : Square p q (refl ∙ r) (s ∙ refl)) → Square p q r s
      Q {p = p} {q} {r} {s} S i j = hcomp
        (λ k → λ { (i = i0) → p j
                 ; (i = i1) → q j
                 ; (j = i0) → (sym (lUnit r)) k i
                 ; (j = i1) → (sym (rUnit s)) k i
        })
        (S i j)
      P : {X X' : A} {Y Y' : B} {q : X ≡ X'} {r : Y ≡ Y'} (f : A → B → C) →
          Square (λ i → f X (r i)) (λ i → f X' (r i)) (λ i → f (q i) Y) (λ i → f (q i) Y')
      P {q = q} {r} f = Q ((ap₂-coh₂ f q r) ∙v flipSquare (ap₂-coh₁ f q r)) in
  ap₂ f (p ∙ q) (r ∙ s) ≡⟨ rUnit (ap₂ f (p ∙ q) (r ∙ s)) ⟩
  ap₂ f (p ∙ q) (r ∙ s) ∙ refl ≡⟨ Square→compPath (ap₂-coh₁ f (p ∙ q) (r ∙ s)) ⟩
  ap (λ X → f X Y) (p ∙ q) ∙ ap (f X'') (r ∙ s) ≡⟨ ap₂ (_∙_) (cong-∙ (λ X → f X Y) p q) (cong-∙ (f X'') r s) ⟩
  (ap (λ X → f X Y) p ∙ ap (λ X → f X Y) q) ∙ ap (f X'') r ∙ ap (f X'') s ≡⟨ assoc (ap (λ X → f X Y) p ∙ ap (λ X → f X Y) q) (ap (f X'') r) (ap (f X'') s) ∙ ap (_∙ ap (f X'') s) (sym (assoc (ap (λ X → f X Y) p) (ap (λ X → f X Y) q) (ap (λ Y → f X'' Y) r))) ⟩
  (ap (λ X → f X Y) p ∙ (ap (λ X → f X Y) q) ∙ ap (f X'') r) ∙ ap (f X'') s ≡⟨ ap (λ Z → ((λ i → f (p i) Y) ∙ Z) ∙ (λ i → f X'' (s i))) (Square→compPath (P f)) ⟩
  (ap (λ X → f X Y) p ∙ (ap (f X') r) ∙ (ap (λ X'' → f X'' Y') q)) ∙ ap (f X'') s ≡⟨ ap (_∙ ap (f X'') s) (assoc (ap (λ X → f X Y) p) (ap (f X') r)  ((ap (λ X'' → f X'' Y') q))) ∙ sym (assoc (ap (λ X → f X Y) p ∙ (ap (f X') r)) (ap (λ X'' → f X'' Y') q) (ap (λ Y → f X'' Y) s)) ⟩
  (ap (λ X → f X Y) p ∙ ap (f X') r) ∙ ap (λ X'' → f X'' Y') q ∙ ap (f X'') s ≡⟨ sym (ap₂ (_∙_) (rUnit (ap₂ f p r) ∙ Square→compPath (ap₂-coh₁ f p r)) (rUnit (ap₂ f q s) ∙ Square→compPath (ap₂-coh₁ f q s)) ) ⟩
  ap₂ f p r ∙ ap₂ f q s ∎

ap-lemma : {X Y Z W X' Y' Z' : B}
  (_⊗_ : B → B → B)
  (p : X ≡ X')
  (q : Y ≡ Y')
  (r : Z ≡ Z')
  (s : W ≡ X ⊗ Y)
  → ap₂ _⊗_ s r ∙ ap₂ (_⊗_) (ap₂ (_⊗_) p q) refl ≡ (ap₂ _⊗_ (s ∙ ap₂ _⊗_ p q) r)
ap-lemma _⊗_ p q r s = (lUnit (ap₂ _⊗_ s r ∙ ap₂ _⊗_ (ap₂ _⊗_ p q) refl) ∙ (Square→compPath (ap₂-∙ _⊗_ s (ap₂ _⊗_ p q) r refl)) ∙ ap (λ x → ap₂ _⊗_ (s ∙ ap₂ _⊗_ p q) x ∙ refl) (sym (rUnit r))) ∙ sym (rUnit (ap₂ _⊗_ (s ∙ (ap₂ _⊗_ p q)) r))
