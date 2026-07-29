module En.Prelude.Squares where

open import En.Prelude.Base public

private
  variable
    ℓ ℓ' : Level
    A B C D E F G H : Type ℓ

postulate
    sorry : ∀ {l} {A : Type l} → A

-- foo : {a b c d : A}
--       (p : a ≡ b)
--       (q : c ≡ d)
--       (r : a ≡ c)
--       (s : b ≡ d)
--       → Square p q r s → Square refl (r ∙ q) refl (p ∙ s)
-- foo p q r s sq = sorry


record Hexagon {ℓ} {A : Type ℓ}
    {a b c d e f : A}
    (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
    (s : a ≡ e) (t : e ≡ f) (u : f ≡ d)
    : Type ℓ where
    constructor hexagon
    field ⬡₌ : a ≡ d
    field ⬡₁ : Square (sym p) r q ⬡₌
    field ⬡₂ : Square s (sym u) ⬡₌ t


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

-- SquarePathIso :
--     {a b c d : A}
--     {p : a ≡ b} {q : c ≡ d} {r : a ≡ c} {s : b ≡ d}
--     → Iso (Square p q r s) (r ∙ q ≡ p ∙ s)
-- SquarePathIso .Iso.fun = Square→compPath
-- SquarePathIso .Iso.inv = compPath→Square
-- SquarePathIso .Iso.sec S i j k = hcomp (λ l → compPath→Square-faces _ _ _ _ _ _ _) (S j i)
-- SquarePathIso .Iso.ret S i j k = hcomp {!!} {!!}

HexagonAssocIso :
    {a b c d e f : A}
    {p : a ≡ b} {q : b ≡ c} {r : c ≡ d} {s : a ≡ e} {t : e ≡ f} {u : f ≡ d}
    → Iso (Square p u (s ∙ t) (q ∙ r)) (Square (p ∙ q) (t ∙ u) s r)
HexagonAssocIso .Iso.fun = HexagonAssoc
HexagonAssocIso .Iso.inv = HexagonAssoc⁻
HexagonAssocIso .Iso.sec S = sorry
HexagonAssocIso .Iso.ret S = sorry

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
    (⬡₌ : a ≡ d)
    (⬡₁ : Square (sym p) r q ⬡₌)
    (⬡₂ : Square s (sym u) ⬡₌ t)
    → Hexagon (sym s) p q t u (sym r)
HexagonRotate⁻ {p = p} {q} {r} {s} {t} {u} ⬡₌ ⬡₁ ⬡₂ .Hexagon.⬡₌ = t ∙ u ∙ sym r
HexagonRotate⁻ {p = p} {q} {r} {s} {t} {u} ⬡₌ ⬡₁ ⬡₂ .Hexagon.⬡₁ i j =
    hcomp (λ k → λ
      { (i = i0) → compPath→Square (sym (rUnit (sym p ∙ s))) j k
      ; (i = i1) → invSides-fillerp (sym q) q refl (u ∙ sym r) (r ∙ sym u) (sym (symDistr r (sym u))) j k
      ; (j = i0) → invSides-filler (sym p) q i k
      ; (j = i1) → compPath→Square (lUnit (t ∙ u ∙ sym r)) i k
      })
      ((⬡₁ ∙h ⬡₂) i j)
HexagonRotate⁻ {p = p} {q} {r} {s} {t} {u} ⬡₌ ⬡₁ ⬡₂ .Hexagon.⬡₂ = compPath→Square (sym (assoc t (u ∙ sym r) r) ∙ ap (t ∙_) (sym (assoc u (sym r) r)) ∙ ap (λ x → t ∙ u ∙ x) (lCancel r) ∙ ap (t ∙_) (sym (rUnit u)))
