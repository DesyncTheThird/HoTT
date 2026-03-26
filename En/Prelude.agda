module En.Prelude where


open import Cubical.Foundations.Prelude
  renaming ( congS to ap
           ; cong to apd
           ; congP to apP
           ; subst to tpt
           ) public
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Path public
open import Cubical.Foundations.GroupoidLaws public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Function public
open import Cubical.Data.Sigma public

-- postulate
--     sorry : ∀ {l} {A : Type l} → A

constᵢSquare : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → Square refl refl p p
constᵢSquare p = compPath→Square (sym (rUnit p) ∙ lUnit p)

constⱼSquare : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → Square p p refl refl
constⱼSquare p = compPath→Square (sym (lUnit p) ∙ rUnit p)

Eq→Square₂₃ : ∀ {ℓ} {A : Type ℓ} {a b : A} {p q : a ≡ b} (γ : p ∙ (sym q) ≡ refl)
    → Square p q refl refl
Eq→Square₂₃ {p = p} {q = q} γ = compPath→Square (sym ((ap (p ∙_) (sym (lCancel q))) ∙ assoc p (sym q) q ∙ ap (_∙ q) γ))

Eq→Square₀₃ : ∀ {ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b} {q : b ≡ a} (γ : p ∙ q ≡ refl)
    → Square refl p q refl
Eq→Square₀₃ {p = p} {q = q} γ = compPath→Square ((ap (_∙ p) (lUnit q)) ∙ (ap (_∙ p) ((ap (_∙ q) (sym (lCancel p))))) ∙ (ap (_∙ p) (sym (assoc (sym p) p q))) ∙ sym (assoc (sym p) (p ∙ q) p) ∙ ap ((sym p) ∙_) (ap (_∙ p) γ) ∙ sym (ap ((sym p) ∙_) (lUnit p)) ∙ lCancel p ∙ rUnit refl)

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

compPath→Triangle₃ : ∀ {ℓ} {A : Type ℓ} {a b c : A} {p : a ≡ c} {r : a ≡ b} {s : c ≡ b}
    (γ : p ∙ s ≡ r) → Square r s p refl
compPath→Triangle₃ {r = r} γ = compPath→Square (γ ∙ rUnit r)

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

compPath→Pentagon : ∀ {ℓ} {A : Type ℓ} {a b c d e : A}
    {p : a ≡ b} {q : b ≡ c} {r : a ≡ d} {s : d ≡ e} {t : e ≡ c}
    (γ : p ∙ q ≡ r ∙ s ∙ t)
    → Σ (a ≡ c) (λ ⬠₌ → (Square (sym p) q refl ⬠₌) × (Square r (sym t) ⬠₌ s))
compPath→Pentagon {p = p} {q = q} γ .fst = p ∙ q
compPath→Pentagon {p = p} {q = q} γ .snd .fst = compPath→Square ((ap (_∙ q) (sym (lCancel p)) ∙ sym (assoc (sym p) p q)))
compPath→Pentagon {r = r} {s = s} {t = t} γ .snd .snd =
    compPath→Square ((ap (_∙ (sym t)) γ
    ∙ sym (assoc r (s ∙ t) (sym t))
    ∙ ap (r ∙_) (sym (assoc s t (sym t))
    ∙ ap (s ∙_) (rCancel t) ∙ (sym (rUnit s)))))

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

compPath→Hexagon : ∀ {ℓ} {A : Type ℓ} {a b c d e f : A}
    {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
    (γ : p ∙ q ∙ r ≡ s ∙ t ∙ u)
    → Σ (a ≡ d) (λ ⬡₌ → (Square (sym p) r q ⬡₌) × (Square s (sym u) ⬡₌ t))
compPath→Hexagon {p = p} {q = q} {r = r} γ .fst = p ∙ q ∙ r
compPath→Hexagon {p = p} {q = q} {r = r} γ .snd .fst = compPath→Square (lUnit (q ∙ r) ∙ ap (_∙ (q ∙ r)) (sym (lCancel p)) ∙ sym (assoc (sym p) p (q ∙ r)) )
compPath→Hexagon {s = s} {t = t} {u = u} γ .snd .snd = compPath→Square (ap (_∙ (sym u)) γ ∙ sym (assoc s (t ∙ u) (sym u)) ∙ ap (s ∙_) (sym (assoc t u (sym u))) ∙ ap (s ∙_) (ap (t ∙_) (rCancel u)) ∙ assoc s t refl ∙ sym (rUnit (s ∙ t)))

hcomp3 : ∀ {ℓ} {A : Type ℓ} {a b c d : A} (p : a ≡ b) (q : c ≡ d) (r : a ≡ c) → b ≡ d
hcomp3 p q r i =
  hcomp (λ j → λ { (i = i0) → p j ; (i = i1) → q j })
        (r i)

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

compSquare :
  ∀ {ℓ}
  {A : Type ℓ} {a b c d e f : A}
  {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d}
  {p' : b ≡ e} {q' : d ≡ f} {t : e ≡ f}
  → Square p q r s → Square p' q' s t
  → Square (p ∙ p') (q ∙ q') r t
compSquare {p = p} {q} {r} {s} {p'} {q'} {t} u v =
  let H1 = Square→compPath u
      H2 = Square→compPath v
   in compPath→Square
     ( assoc r q q'
     ∙ ap (_∙ q') H1
     ∙ sym (assoc p s q')
     ∙ ap (p ∙_) H2
     ∙ assoc p p' t)

invSquare :
  ∀ {ℓ}
  {A : Type ℓ} {a b c d : A}
  {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d}
  → Square p q r s → Square q p (sym r) (sym s)
invSquare {p = p} {q} {r} {s} sq =
  let H = Square→compPath sq
    in compPath→Square
      ( rUnit (sym r ∙ p)
      ∙ ap ((sym r ∙ p) ∙_) (sym (rCancel s))
      ∙ sym (assoc (sym r) p (s ∙ sym s))
      ∙ ap (sym r ∙_) (assoc p s (sym s))
      ∙ ap (λ t → sym r ∙ t ∙ sym s) (sym H)
      ∙ ap (sym r ∙_) (sym (assoc r q (sym s)))
      ∙ assoc (sym r) r (q ∙ sym s)
      ∙ ap (_∙ q ∙ sym s) (lCancel r)
      ∙ sym (lUnit (q ∙ sym s)) )

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

naiveCompFaces :
  ∀ {ℓ} {A : Type ℓ}
  {a b c d : A}
  (p : a ≡ b) (q : c ≡ d) (r : a ≡ c)
  (i j : I) → Partial (i ∨ ~ i) A
naiveCompFaces p q r i j =
  λ { (i = i0) → p j
    ; (i = i1) → q j }

naiveComp :
  ∀ {ℓ} {A : Type ℓ}
  {a b c d : A}
  (p : a ≡ b) (q : c ≡ d) (r : a ≡ c)
  → b ≡ d
naiveComp p q r i =
  hcomp (naiveCompFaces p q r i)
        (r i)

naiveCompFiller :
  ∀ {ℓ} {A : Type ℓ}
  {a b c d : A}
  (p : a ≡ b) (q : c ≡ d) (r : a ≡ c)
  → Square p q r (naiveComp p q r)
naiveCompFiller p q r i j =
  hfill (naiveCompFaces p q r i)
        (inS (r i))
        j


andSquare :
  ∀ {ℓ} {A : Type ℓ}
  {a b : A}
  (p : a ≡ b)
  → Square refl p refl p
andSquare p i j = p (i ∧ j)

orSquare :
  ∀ {ℓ} {A : Type ℓ}
  {a b : A}
  (p : a ≡ b)
  → Square p refl p refl
orSquare p i j = p (i ∨ j)

nandSquare1 :
  ∀ {ℓ} {A : Type ℓ}
  {a b : A}
  (p : a ≡ b)
  → Square p refl refl (sym p)
nandSquare1 p i j = p (~ i ∧ j)

nandSquare2 :
  ∀ {ℓ} {A : Type ℓ}
  {a b : A}
  (p : a ≡ b)
  → Square refl (sym p) p refl
nandSquare2 p i j = p (i ∧ ~ j)

norSquare1 :
  ∀ {ℓ} {A : Type ℓ}
  {a b : A}
  (p : a ≡ b)
  → Square refl p (sym p) refl
norSquare1 p i j = p (~ i ∨ j)

norSquare2 :
  ∀ {ℓ} {A : Type ℓ}
  {a b : A}
  (p : a ≡ b)
  → Square (sym p) refl refl p
norSquare2 p i j = p (i ∨ ~ j)

constSquare1 :
  ∀ {ℓ} {A : Type ℓ}
  {a b : A}
  (p : a ≡ b)
  → Square refl refl p p
constSquare1 p i j = p i

constSquare2 :
  ∀ {ℓ} {A : Type ℓ}
  {a b : A}
  (p : a ≡ b)
  → Square p p refl refl
constSquare2 p i j = p j

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

bleh :
  ∀ {ℓ} {A : Type ℓ}
  {a b c : A}
  (p : a ≡ b) (q : b ≡ c)
  → Square refl q p (p ∙ q)
bleh {a = a} p q i j = hfill (λ k → λ
  { (i = i0) → a
  ; (i = i1) → q k }
  ) (inS (p i)) j


AAAA :
  ∀ {ℓ} {A : Type ℓ}
  {a b c : A}
  (p : a ≡ b) (q : b ≡ c)
  → Square p (p ∙ q) refl q
-- AAAA p q = flipSquare (bleh p q)
AAAA {a = a} p q i j = hfill (λ k → λ
  { (j = i0) → a
  ; (j = i1) → q k }
  ) (inS (p j)) i

BBBB :
  ∀ {ℓ} {A : Type ℓ}
  {a b c : A}
  (p : a ≡ b) (q : b ≡ c)
  → Square (sym p) refl q (p ∙ q)
BBBB p q i j = hcomp
    (λ k →
    λ { (i = i0) → p (k ∧ ~ j)
      ; (i = i1) → q k
      ; (j = i0) → pqpq p q i k
      ; (j = i1) → bleh p q i k
      }) (p i)

squishSquare :
  ∀ {ℓ} {A : Type ℓ} {a b c d : A}
  {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d}
  → Square p q r s → Square refl refl (r ∙ q) (p ∙ s)
squishSquare {a = a} {b} {c} {d} {p} {q} {r} {s} P i j = hcomp
    (λ k →
    λ { (i = i0) → nandSquare2 p j k
      ; (i = i1) → orSquare q j k
      ; (j = i0) → hfill (λ l → λ
            { (i = i0) → a
            ; (i = i1) → q l })
        (inS (r i)) k -- compPath→Square (ap (_∙ q) (lUnit r) ∙ sym (assoc refl r q)) i k
      ; (j = i1) → BBBB p s i k
      -- compPath→Square (sym (rUnit s) ∙ lUnit s ∙ ap (_∙ s) (sym (lCancel p)) ∙ sym (assoc (sym p) p s)) i k
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




naiveSquare :
  ∀ {ℓ} {A : Type ℓ}
  {a b c d : A}
  (p : a ≡ b) (q : c ≡ d) (r : a ≡ c)
  -- → PathP (λ i → r i ≡ naiveComp p q r i) p q
  → Square p q r (naiveComp p q r)
naiveSquare p q r i j =
  hfill (λ k → λ { (i = i0) → p (k)
                 ; (i = i1) → q (k)
                 })
        (inS (r i))
        j

naiveCompFiller' :
  ∀ {ℓ} {A : Type ℓ}
  {a b c d : A}
  (p : a ≡ b) (q : c ≡ d) (r : a ≡ c)
  → Square p q r (naiveComp p q r)
naiveCompFiller' p q r i j =
  hfill (naiveCompFaces p q r i)
        (inS (r i))
        j

crewSquare :
  ∀ {ℓ} {A : Type ℓ}
  {a : A}
  (p : a ≡ a)
  → Square p p p (naiveComp p p p)
crewSquare p i j =
  hcomp (λ k → λ { (i = i0) → p (j ∧ k)
                 ; (i = i1) → p (j ∧ k)
                 ; (j = i0) → p i
                 })
        (p i)

susSquare :
  ∀ {ℓ} {A : Type ℓ}
  {a : A}
  (p : a ≡ a)
  → Square p p p p
susSquare {a = a} p i j =
  hcomp (λ k → λ { (i = i0) → p (j ∨ ~ k)
                 ; (i = i1) → p (j ∧ k)
                 ; (j = i0) → p (i ∨ ~ k)
                 ; (j = i1) → p (i ∧ k)
                 })
        a

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






∙∙lCancel-fill' : ∀ {ℓ} {A : Type ℓ} {x y : A}
         → (p : x ≡ y)
         → I → I → I → A
∙∙lCancel-fill' p i j k =
  hfill (λ k → λ { (i = i1) → p k
                  ; (j = i0) → p k
                  ; (j = i1) → p k})
        (inS (p i0)) k

∙∙lCancel'' : ∀ {ℓ} {A : Type ℓ} {x y : A}
         → (p : x ≡ y)
         → Square (sym p ∙∙ refl ∙∙ p) (refl) refl refl
∙∙lCancel'' {x = x} {y} p i j =
  hfill {φ = i ∨ ~ j ∨ j}
        (λ k → λ { (i = i1) → constSquare2 p j k
                 ; (j = i0) → constSquare2 p i k
                 ; (j = i1) → constSquare2 p i k
                 })
        (inS x)
        i1

∙∙lCancel''' : ∀ {ℓ} {A : Type ℓ} {x y : A}
             → (p : x ≡ y)
             → PathP (λ i → refl {x = y} i ≡ refl {x = y} i) (sym p ∙∙ refl ∙∙ p) (refl)
∙∙lCancel''' p = ∙∙lCancel'' p

lUnit'
  : ∀ {ℓ} {A : Type ℓ} {x y : A}
  → (p : x ≡ y)
  → Square (refl ∙∙ refl ∙∙ p) p refl refl
lUnit' {x = x} {y = y} p i j =
  hcomp
    (λ k → λ { (i = i1) → norSquare1 p k j
             ; (j = i0) → nandSquare2 p i k
             ; (j = i1) → orSquare p i k
             })
    (constSquare2 p j i)

lUnit''
  : ∀ {ℓ} {A : Type ℓ} {x y : A}
  → (p : x ≡ y)
  → (refl ∙∙ refl ∙∙ p) ≡ p
lUnit'' p = lUnit' p


private
  variable
    ℓ : Level
    A B C D E F G H : Type ℓ

pain∙jpeg₁ : {_⊗A_ : A → A → A} {_⊗B_ : B → B → B} {h : A → B} {X Y Z : A} {X' Y' Z' : B}
  {p : h X ≡ X'}
  {q : h Y ≡ Y'}
  {r : h Z ≡ Z'}
  (f : ∀ x y → h (x ⊗A y) ≡ h x ⊗B h y)
  → Square (ap₂ _⊗B_ (f X Y) r) (ap₃ (λ x y z → (x ⊗B y) ⊗B z) p q r) (ap₂ _⊗B_ (f X Y) refl) (ap₂ _⊗B_ (ap₂ _⊗B_ p q) refl)
pain∙jpeg₁ {_⊗B_ = _⊗B_} {X = X} {Y} {p = p} {q} {r} f i j = pqpq (f X Y) (ap₂ _⊗B_ p q) i j ⊗B r j


pain∙jpeg₂ : {_⊗A_ : A → A → A} {_⊗B_ : B → B → B} {h : A → B} {X Y Z : A} {X' Y' Z' : B}
  {p : h X ≡ X'}
  {q : h Y ≡ Y'}
  {r : h Z ≡ Z'}
  (f : ∀ x y → h (x ⊗A y) ≡ h x ⊗B h y)
  → Square (ap₂ _⊗B_ p (f Y Z)) (ap₃ (λ x y z → x ⊗B (y ⊗B z)) p q r) (ap₂ _⊗B_ refl (f Y Z)) (ap₂ _⊗B_ refl (ap₂ _⊗B_ q r))
pain∙jpeg₂ {_⊗B_ = _⊗B_} {Y = Y} {Z} {p = p} {q} {r} f i j = (p j) ⊗B pqpq (f Y Z) (ap₂ _⊗B_ q r) i j


ree : {X X' X'' : A} {Y Y' Y'' : B}
  {p : X ≡ X'}
  {q : X' ≡ X''}
  {r : Y ≡ Y'}
  {s : Y' ≡ Y''}
  {f : A → B → C}
  → Square (λ i → f X' (r i)) (λ i → f X'' (r i)) (λ i → f (q i) Y) (λ i → f (q i) Y')
ree {X = X} {X'} {X''} {Y} {Y'} {Y''} {p} {q} {r} {s} {f} = {!ap₂-coh₁ f q r!}
    -- hcomp (λ k → {!λ
    --       { (i=i0) → ?
    --       ; (i=i1) → ?
    --       ; (j=i0) → ?
    --       ; (j=i1) → ?}!})
    -- {!!}

ap₂-∙ : {X X' X'' : A} {Y Y' Y'' : B}
  {p : X ≡ X'}
  {q : X' ≡ X''}
  {r : Y ≡ Y'}
  {s : Y' ≡ Y''}
  {f : A → B → C}
  → ap₂ f (p ∙ q) (r ∙ s) ≡ (ap₂ f p r) ∙ (ap₂ f q s)
ap₂-∙ {X = X} {X'} {X''} {Y} {Y'} {Y''} {p} {q} {r} {s} {f} =
  ap₂ f (p ∙ q) (r ∙ s) ≡⟨ rUnit (ap₂ f (p ∙ q) (r ∙ s)) ⟩
  ap₂ f (p ∙ q) (r ∙ s) ∙ refl ≡⟨ Square→compPath (ap₂-coh₁ f (p ∙ q) (r ∙ s)) ⟩
  ap (λ X → f X Y) (p ∙ q) ∙ ap (f X'') (r ∙ s) ≡⟨ ap₂ (_∙_) (cong-∙ (λ X → f X Y) p q) (cong-∙ (f X'') r s) ⟩
  (ap (λ X → f X Y) p ∙ ap (λ X → f X Y) q) ∙ ap (f X'') r ∙ ap (f X'') s ≡⟨ assoc (ap (λ X → f X Y) p ∙ ap (λ X → f X Y) q) (ap (f X'') r) (ap (f X'') s) ∙ ap (_∙ ap (f X'') s) (sym (assoc (ap (λ X → f X Y) p) (ap (λ X → f X Y) q) (ap (λ Y → f X'' Y) r))) ⟩
  (ap (λ X → f X Y) p ∙ (ap (λ X → f X Y) q) ∙ ap (f X'') r) ∙ ap (f X'') s ≡⟨ ap (λ Z → ((λ i → f (p i) Y) ∙ Z) ∙ (λ i → f X'' (s i))) (Square→compPath {!!}) ⟩
  (ap (λ X → f X Y) p ∙ (ap (f X') r) ∙ (ap (λ X'' → f X'' Y') q)) ∙ ap (f X'') s ≡⟨ {!!} ⟩
  (ap (λ X → f X Y) p ∙ ap (f X') r) ∙ ap (λ X'' → f X'' Y') q ∙ ap (f X'') s ≡⟨ sym (ap₂ (_∙_) (rUnit (ap₂ f p r) ∙ Square→compPath (ap₂-coh₁ f p r)) (rUnit (ap₂ f q s) ∙ Square→compPath (ap₂-coh₁ f q s)) ) ⟩
  ap₂ f p r ∙ ap₂ f q s ∎
