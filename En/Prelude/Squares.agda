module En.Prelude.Squares where

open import En.Prelude.Base public

private
  variable
    ℓ ℓ' : Level
    A B C D E F G H : Type ℓ

-- postulate
--     sorry : ∀ {l} {A : Type l} → A

record Hexagon {ℓ} {A : Type ℓ}
    {a b c d e f : A}
    (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
    (s : a ≡ e) (t : e ≡ f) (u : f ≡ d)
    : Type ℓ where
    constructor hexagon
    field ⬡₌ : a ≡ d
    field ⬡₁ : Square (sym p) r q ⬡₌
    field ⬡₂ : Square s (sym u) ⬡₌ t


-- b c d      c-->d
-- |   |  ->  b   f
-- a e f      a-->e

HexagonAssoc :
    {a b c d e f : A}
    {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
    → Square p u (s ∙ t) (q ∙ r) → Square (p ∙ q) (t ∙ u) s r
HexagonAssoc {p = p} {q} {r} {s} {t} {u} S = compPath→Square (assoc s t u ∙ Square→compPath S ∙ assoc p q r)
    -- hcomp (λ k → λ
    --   { (i = i0) → {!!}
    --   ; (i = i1) → {!!}
    --   ; (j = i0) → {!!}
    --   ; (j = i1) → {!!}
    --   }) (S i j)

HexagonAssoc⁻ :
    {a b c d e f : A}
    {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
    → Square (p ∙ q) (t ∙ u) s r → Square p u (s ∙ t) (q ∙ r)
HexagonAssoc⁻ {p = p} {q} {r} {s} {t} {u} S = compPath→Square ((sym (assoc s t u) ∙ Square→compPath S) ∙ sym (assoc p q r))


-- foo : {a b c d : A}
--     {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d}
--     →
--     (sym r ∙∙ p ∙∙ s) ≡ q → (r ∙ q ≡ p ∙ s)
-- foo {p = p} {q} {r} {s} P = ap (r ∙_) ((sym P) ∙ (doubleCompPath≡compPath (sym r) p s)) ∙ assoc r (sym r) (p ∙ s) ∙ ap (_∙ p ∙ s) (rCancel r) ∙ sym (lUnit (p ∙ s))

-- SquarePathIso :
--     {a b c d : A}
--     {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d}
--     → Iso (Square p q r s) (r ∙ q ≡ p ∙ s)
-- SquarePathIso {p = p} {q} {r} {s} = compIso (equivToIso (Square≃doubleComp p q r s)) (iso {!!} {!!} {!!} {!!})


-- HexagonAssocIso :
--     {a b c d e f : A}
--     {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
--     → Iso (Square p u (s ∙ t) (q ∙ r)) (Square (p ∙ q) (t ∙ u) s r)
-- HexagonAssocIso .Iso.fun = HexagonAssoc
-- HexagonAssocIso .Iso.inv = HexagonAssoc⁻
-- HexagonAssocIso .Iso.sec S = {!!}
-- HexagonAssocIso .Iso.ret S = {!!}

-- HexagonAssocEq :
--     {a b c d e f : A}
--     {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
--     → Square p u (s ∙ t) (q ∙ r) ≡ Square (p ∙ q) (t ∙ u) s r
-- HexagonAssocEq = isoToPath HexagonAssocIso

-- HexagonAssoc :
--     {a b c d e f : A}
--     {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
--     → Square p u (s ∙ t) (q ∙ r) ≡ Square (p ∙ q) (t ∙ u) s r
-- HexagonAssoc i = {!!}

invSides-fillerp :
    {a b c : A}
    (p : a ≡ b)
    (s : b ≡ a)
    (ps : p ≡ sym s)
    (q : c ≡ a)
    (r : a ≡ c)
    (qr : q ≡ sym r)
    → Square p q r s
invSides-fillerp {a = a} p s ps q r qr =
    tpt (λ x → Square p q r x) (ap sym ps)
        (tpt (λ y → Square p y r (sym p)) (sym qr)
            (invSides-filler p r))

--  e f        e f
-- a---d  ->  a \ d
--  b c        b c

HexagonRotate⁻ :
    {a b c d e f : A}
    {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
    (⬡ : Hexagon p q r s t u )
    → Hexagon (sym s) p q t u (sym r)
HexagonRotate⁻ {p = p} {q} {r} {s} {t} {u} ⬡ .Hexagon.⬡₌ =  t ∙ u ∙ sym r
HexagonRotate⁻ {p = p} {q} {r} {s} {t} {u} ⬡ .Hexagon.⬡₁ i j = 
    hcomp (λ k → λ
      { (i = i0) → compPath→Square (sym (rUnit (sym p ∙ s))) j k
      ; (i = i1) → invSides-fillerp (sym q) q refl (u ∙ sym r) (r ∙ sym u) (sym (symDistr r (sym u))) j k
      ; (j = i0) → invSides-filler (sym p) q i k
      ; (j = i1) → compPath→Square (lUnit (t ∙ u ∙ sym r)) i k
      })
      ((⬡ .Hexagon.⬡₁ ∙h ⬡ .Hexagon.⬡₂ ) i j)
HexagonRotate⁻ {p = p} {q} {r} {s} {t} {u} ⬡ .Hexagon.⬡₂ = compPath→Square (sym (assoc t (u ∙ sym r) r) ∙ ap (t ∙_) (sym (assoc u (sym r) r)) ∙ ap (λ x → t ∙ u ∙ x) (lCancel r) ∙ ap (t ∙_) (sym (rUnit u)))

doubleCompPath→Hexagon :
    {a b c d e f : A}
    {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
    → (p ∙∙ q ∙∙ r) ≡ (s ∙∙ t ∙∙ u) → Hexagon p q r s t u
doubleCompPath→Hexagon {p = p} {q} {r} {s} {t} {u} P .Hexagon.⬡₌ = p ∙ q ∙ r
doubleCompPath→Hexagon {p = p} {q} {r} {s} {t} {u} P .Hexagon.⬡₁ = compPath→Square (lUnit (q ∙ r) ∙ ap (_∙ q ∙ r) (sym (lCancel p)) ∙ sym (assoc (sym p) p (q ∙ r)))
doubleCompPath→Hexagon {p = p} {q} {r} {s} {t} {u} P .Hexagon.⬡₂ = compPath→Square (ap (_∙ sym u) (sym (doubleCompPath≡compPath p q r) ∙ P ∙ (doubleCompPath≡compPath s t u)) ∙ sym (assoc s (t ∙ u) (sym u)) ∙ ap (s ∙_) (sym (assoc t u (sym u))) ∙ ap (λ a → s ∙ t ∙ a) (rCancel u) ∙ ap (s ∙_) (sym (rUnit t)))

Hexagon→doubleCompPath :
    {a b c d e f : A}
    {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
    → Hexagon p q r s t u → (p ∙∙ q ∙∙ r) ≡ (s ∙∙ t ∙∙ u)
Hexagon→doubleCompPath {p = p} {q} {r} {s} {t} {u} ⬡ =
    doubleCompPath≡compPath p q r
    ∙ rUnit (p ∙ q ∙ r)
    ∙ (ap ((p ∙ q ∙ r) ∙_) (sym (lCancel u)))
    ∙ assoc (p ∙ q ∙ r) (sym u) u
    ∙ ap (_∙ u) (sym (assoc p (q ∙ r) (sym u)) ∙ ap (p ∙_) (sym (assoc q r (sym u)) ∙ Square→compPath (⬡. Hexagon.⬡₁ ∙h ⬡. Hexagon.⬡₂)))
    ∙ (ap (_∙ u) (assoc p (sym p ∙ s) t) ∙ ap (λ a → (a ∙ t) ∙ u ) (assoc p (sym p) s ∙ ap (_∙ s) (rCancel p) ∙ sym (lUnit s)) ∙ sym (assoc s t u))
    ∙ sym (doubleCompPath≡compPath s t u)

--  e f       e-->f
-- a---d  ->  a   d
--  b c       b-->c

Hexagon→Square :
    {a b c d e f : A}
    {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
    → Hexagon p q r s t u → Square (sym p ∙ s) (r ∙ sym u) q t
Hexagon→Square {p = p} {q} {r} {s} {t} {u} ⬡ = ⬡ .Hexagon.⬡₁ ∙h ⬡ .Hexagon.⬡₂


doubleCompPathEq→compPathEq :
    {a b c d e f : A}
    {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
    → (p ∙∙ q ∙∙ r) ≡ (s ∙∙ t ∙∙ u) → p ∙ q ∙ r ≡ s ∙ t ∙ u
doubleCompPathEq→compPathEq {p = p} {q} {r} {s} {t} {u} P = sym (doubleCompPath≡compPath p q r) ∙ P ∙ doubleCompPath≡compPath s t u

compPathEq→doubleCompPathEq :
    {a b c d e f : A}
    {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
    → p ∙ q ∙ r ≡ s ∙ t ∙ u → (p ∙∙ q ∙∙ r) ≡ (s ∙∙ t ∙∙ u)
compPathEq→doubleCompPathEq {p = p} {q} {r} {s} {t} {u} P = doubleCompPath≡compPath p q r ∙ P ∙ sym (doubleCompPath≡compPath s t u)
