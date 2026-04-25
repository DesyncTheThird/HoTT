module En.Prelude where

open import En.Prelude.Ap public
open import En.Prelude.Squares public
open import En.Prelude.Coherence public

-- postulate
--     sorry : ∀ {l} {A : Type l} → A

Eq→Square₂₃ : ∀ {ℓ} {A : Type ℓ} {a b : A} {p q : a ≡ b} (γ : p ∙ (sym q) ≡ refl)
    → Square p q refl refl
Eq→Square₂₃ {p = p} {q = q} γ = compPath→Square (sym ((ap (p ∙_) (sym (lCancel q))) ∙ assoc p (sym q) q ∙ ap (_∙ q) γ))

Eq→Square₀₃ : ∀ {ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b} {q : b ≡ a} (γ : p ∙ q ≡ refl)
    → Square refl p q refl
Eq→Square₀₃ {p = p} {q = q} γ = compPath→Square ((ap (_∙ p) (lUnit q)) ∙ (ap (_∙ p) ((ap (_∙ q) (sym (lCancel p))))) ∙ (ap (_∙ p) (sym (assoc (sym p) p q))) ∙ sym (assoc (sym p) (p ∙ q) p) ∙ ap ((sym p) ∙_) (ap (_∙ p) γ) ∙ sym (ap ((sym p) ∙_) (lUnit p)) ∙ lCancel p ∙ rUnit refl)


isSet→Square :
  ∀ {ℓ}
  {A : Type ℓ}
  (isSet : isSet A)
  (a₀₀ : A) (a₀₁ : A) (a₀₋ : PathP (λ j → A) a₀₀ a₀₁)
  (a₁₀ : A) (a₁₁ : A) (a₁₋ : PathP (λ j → A) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A) a₀₁ a₁₁)
  → Square a₀₋ a₁₋ a₋₀ a₋₁
isSet→Square isset _ _ a₀₋ _ _ a₁₋ a₋₀ a₋₁ =
  compPath→Square (isset (a₋₀ i0) (a₋₁ i1) ((λ i → a₋₀ i) ∙ a₁₋) (a₀₋ ∙ (λ i → a₋₁ i)))

doubleCompPath-square :
  ∀ {ℓ}
  {A : Type ℓ}
  {x y z w : A}
  (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → Square q (p ∙∙ q ∙∙ r) (sym p) r
doubleCompPath-square p q r j i =
  hfill (doubleComp-faces p r i) (inS (q i)) j

doubleCompPathP :
  ∀ {ℓ ℓ'}
  {A : Type ℓ} {B : A → Type ℓ'}
  {x y z w : A}
  {x* : B x} {y* : B y} {z* : B z} {w* : B w}
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w}
  (p* : PathP (λ i → B (p i)) x* y*) (q* : PathP (λ i → B (q i)) y* z*) (r* : PathP (λ i → B (r i)) z* w*)
  → PathP (λ i → B ((p ∙∙ q ∙∙ r) i)) x* w*
doubleCompPathP {B = B} {x* = x*} {p = p} {q = q} {r = r} p* q* r* i =
  comp (λ j → B (doubleCompPath-square p q r j i))
       (λ j → λ { (i = i0) → p* (~ j)
                ; (i = i1) → r* j })
       (q* i)

iterCompPath-square :
  ∀ {ℓ}
  {A : Type ℓ}
  {x y z w : A}
  (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → Square q (p ∙ q ∙ r) (sym p) r
iterCompPath-square p q r =
  compPath→Square (ap (sym p ∙_) (assoc p q r)
                  ∙ assoc (sym p) (p ∙ q) r
                  ∙ ap (_∙ r) (assoc (sym p) p q)
                  ∙ ap (_∙ r) (ap (_∙ q) (lCancel p)
                  ∙ sym (lUnit q)))

iterCompPathP :
  ∀ {ℓ ℓ'}
  {A : Type ℓ} {B : A → Type ℓ'}
  {x y z w : A}
  {x* : B x} {y* : B y} {z* : B z} {w* : B w}
  {p : x ≡ y} {q : y ≡ z} {r : z ≡ w}
  (p* : PathP (λ i → B (p i)) x* y*) (q* : PathP (λ i → B (q i)) y* z*) (r* : PathP (λ i → B (r i)) z* w*)
  → PathP (λ i → B ((p ∙ q ∙ r) i)) x* w*
iterCompPathP {B = B} {x* = x*} {p = p} {q = q} {r = r} p* q* r* i =
  comp (λ j → B (iterCompPath-square p q r j i))
       (λ j → λ { (i = i0) → p* (~ j)
                ; (i = i1) → r* j })
       (q* i)

invSquareh :
  ∀ {ℓ}
  {A : Type ℓ} {a b c d : A}
  {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d}
  → Square p q r s → Square q p (sym r) (sym s)
invSquareh {p = p} {q} {r} {s} sq i j = sq (~ i) j

invSquarev :
  ∀ {ℓ}
  {A : Type ℓ} {a b c d : A}
  {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d}
  → Square p q r s → Square (sym p) (sym q) s r
invSquarev {p = p} {q} {r} {s} sq i j = sq i (~ j)

-- shiftSquare :
--   ∀ {ℓ}
--   {A : Type ℓ} {a b c d : A}
--   {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d}
--   → Square p refl (r ∙ q) s → Square p q r s
-- shiftSquare {p = p} {q} {r} {s} sq i j =
--   hcomp
--     (λ k → (λ { (i = i0) → p j
--               ; (i = i1) → {!q (j ∨ k)!}
--               ; (j = i0) → {!!}
--               ; (j = i1) → {!s i!}
--              }))
--     (sq i j)

morphSquare :
  ∀ {ℓ}
  {A : Type ℓ}
  {a b c d e f : A}
  {p : a ≡ b} {q : b ≡ d} {r : d ≡ f} {s : a ≡ c} {t : c ≡ e} {u : e ≡ f}
  → Square p u (s ∙ t) (q ∙ r)
  → Square (p ∙ q ∙ r) t s (sym u)
morphSquare
  {a = a} {b} {c} {d} {e} {f}
  {p = p} {q} {r} {s} {t} {u} sq i j =
  hcomp
    (λ k → (λ { (i = i0) → compPath→Square (sym (lUnit (p ∙ q ∙ r))) k j
              ; (i = i1) → compPath→Square (lCancel t ∙ sym (rCancel u)) k j
              ; (j = i0) → compPath→Square (sym (lUnit s) ∙ rUnit s ∙ ap (s ∙_) (sym (rCancel t)) ∙ assoc s t (sym t)) k i
              ; (j = i1) → compPath→Square (refl {x = (q ∙ r) ∙ sym u}) k i
              }))
    (sq i j)

pqpq :
  ∀ {ℓ} {A : Type ℓ}
  {a b c : A}
  (p : a ≡ b) (q : b ≡ c)
  → Square p q p q
pqpq p q i j = hcomp
    (λ k →
       λ { (i = i0) → p j
         ; (i = i1) → q (j ∧ k)
         ; (j = i0) → p i
         ; (j = i1) → q (i ∧ k)
       })
    (p (i ∨ j))

squishSquare :
  ∀ {ℓ} {A : Type ℓ} {a b c d : A}
  {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d}
  → Square p q r s → Square refl refl (r ∙ q) (p ∙ s)
squishSquare {a = a} {b} {c} {d} {p} {q} {r} {s} P i j =
    let S : ∀ {ℓ} {A : Type ℓ} {a b c : A} (p : a ≡ b) (q : b ≡ c) → Square refl q p (p ∙ q)
        S {a = a} p q i j = hfill (λ k → λ
            { (i = i0) → a
            ; (i = i1) → q k
          })
          (inS (p i)) j
        R : ∀ {ℓ} {A : Type ℓ} {a b c : A} (p : a ≡ b) (q : b ≡ c) → Square p (p ∙ q) refl q
        R {a = a} p q i j = hfill (λ k → λ
            { (j = i0) → a
            ; (j = i1) → q k
          })
          (inS (p j)) i
        Q : ∀ {ℓ} {A : Type ℓ} {a b c : A} (p : a ≡ b) (q : b ≡ c) → Square (sym p) refl q (p ∙ q)
        Q p q i j = hcomp
          (λ k →
            λ { (i = i0) → p (k ∧ ~ j)
            ; (i = i1) → q k
            ; (j = i0) → pqpq p q i k
            ; (j = i1) → S p q i k
            })
          (p i)
    in
    hcomp
    (λ k →
    λ { (i = i0) → p (j ∧ ~ k)
      ; (i = i1) → q (j ∨ k)
      ; (j = i0) → hfill (λ l → λ
            { (i = i0) → a
            ; (i = i1) → q l
          })
        (inS (r i)) k
      ; (j = i1) → Q p s i k
      })
    (P i j)


cornerComp :
  ∀ {ℓ}
  {A : Type ℓ} {a b c d e f g : A}
  {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d}
  {t : e ≡ f} {u : c ≡ e} {v : d ≡ f}
  {w : b ≡ g} {x : g ≡ f}
  → Square p q r s → Square q t u v → Square w v s x
  → Square p t (r ∙ u) (w ∙ x)
cornerComp {p = p} {q} {r} {s} {t} {u} P Q R i j =
   hcomp (λ k → λ
  { (i = i0) → p j
  ; (i = i1) → t j
  ; (j = i0) → (r ∙ u) i
  ; (j = i1) → squishSquare R i k
  }) ((P ∙v Q) i j)




private
  variable
    ℓ : Level
    A B C D E F G H : Type ℓ

triple-⊗-leftHom : {_⊗A_ : A → A → A} {_⊗B_ : B → B → B} {h : A → B} {X Y Z : A} {X' Y' Z' : B}
  {p : h X ≡ X'}
  {q : h Y ≡ Y'}
  {r : h Z ≡ Z'}
  (f : ∀ x y → h (x ⊗A y) ≡ h x ⊗B h y)
  → Square (ap₂ _⊗B_ (f X Y) r) (ap₃ (λ x y z → (x ⊗B y) ⊗B z) p q r) (ap₂ _⊗B_ (f X Y) refl) (ap₂ _⊗B_ (ap₂ _⊗B_ p q) refl)
triple-⊗-leftHom {_⊗B_ = _⊗B_} {X = X} {Y} {p = p} {q} {r} f i j = pqpq (f X Y) (ap₂ _⊗B_ p q) i j ⊗B r j

triple-⊗-rightHom : (_⊗A_ : A → A → A) (_⊗B_ : B → B → B) {h : A → B} {X Y Z : A} {X' Y' Z' : B}
  {p : h X ≡ X'}
  {q : h Y ≡ Y'}
  {r : h Z ≡ Z'}
  (f : ∀ x y → h (x ⊗A y) ≡ h x ⊗B h y)
  → Square (ap₂ _⊗B_ p (f Y Z)) (ap₃ (λ x y z → x ⊗B (y ⊗B z)) p q r) (ap₂ _⊗B_ refl (f Y Z)) (ap₂ _⊗B_ refl (ap₂ _⊗B_ q r))
triple-⊗-rightHom _⊗A_ _⊗B_ {Y = Y} {Z} {p = p} {q} {r} f i j = (p j) ⊗B pqpq (f Y Z) (ap₂ _⊗B_ q r) i j

