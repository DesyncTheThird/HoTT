module En.Prelude where

open import Cubical.Foundations.Prelude
  renaming ( congS to ap
           ; cong₂ to ap₂
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

postulate
    sorry : ∀ {l} {A : Type l} → A

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
