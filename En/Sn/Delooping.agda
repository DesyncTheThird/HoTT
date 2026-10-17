module En.Sn.Delooping where

open import En.Prelude hiding ( _·_ )
open FN
open import Cubical.Foundations.Pointed
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as Trunc using ( ∣_∣ₕ ; isOfHLevelTrunc )
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import En.GroupPresentation
open import En.HigherGroup
open import En.Sn.Properties
open import En.Sn.Presentation renaming ( module Univ to SymUniv )

private
  variable
    n : ℕ

-- coxeter presentation of the delooping of the symmetric group on suc n points

data BSym (n : ℕ) : Type where
  base : BSym n
  loop : Fin n → base ≡ base
  cancel : (k : Fin n) → loop k ≡ sym (loop k)
  comm : (k l : Fin n) → suc (k .fst) <ᵗ l .fst → Square (loop l) (loop l) (loop k) (loop k)
  braid₌ : (k l : Fin n) → suc (k .fst) ≡ l .fst → base ≡ base
  braid₁ : (k l : Fin n) (p : suc (k .fst) ≡ l .fst) → Square (sym (loop k)) (loop k) (loop l) (braid₌ k l p)
  braid₂ : (k l : Fin n) (p : suc (k .fst) ≡ l .fst) → Square (loop l) (sym (loop l)) (braid₌ k l p) (loop k)
  trunc : isGroupoid (BSym n)

module BSymElim {ℓ} {n : ℕ} (P : BSym n → Type ℓ)
  (base* : P base)
  (loop* : (k : Fin n) → PathP (λ i → P (loop k i)) base* base*)
  (cancel* : (k : Fin n)
    → SquareP (λ i j → P (cancel k i j)) (loop* k) (symP (loop* k)) refl refl)
  (comm* : (k l : Fin n) (p : suc (k .fst) <ᵗ l .fst)
    → SquareP (λ i j → P (comm k l p i j)) (loop* l) (loop* l) (loop* k) (loop* k))
  (braid₌* : (k l : Fin n) (p : suc (k .fst) ≡ l .fst)
    → PathP (λ i → P (braid₌ k l p i)) base* base*)
  (braid₁* : (k l : Fin n) (p : suc (k .fst) ≡ l .fst)
    → SquareP (λ i j → P (braid₁ k l p i j)) (symP (loop* k)) (loop* k) (loop* l) (braid₌* k l p))
  (braid₂* : (k l : Fin n) (p : suc (k .fst) ≡ l .fst)
    → SquareP (λ i j → P (braid₂ k l p i j)) (loop* l) (symP (loop* l)) (braid₌* k l p) (loop* k))
  (isGroupoid* : (z : BSym n) → isGroupoid (P z))
  where

  elim : (z : BSym n) → P z
  elim base = base*
  elim (loop k i) = loop* k i
  elim (cancel k i j) = cancel* k i j
  elim (comm k l p i j) = comm* k l p i j
  elim (braid₌ k l p i) = braid₌* k l p i
  elim (braid₁ k l p i j) = braid₁* k l p i j
  elim (braid₂ k l p i j) = braid₂* k l p i j
  elim (trunc x y p q r s i j k) =
    isGroupoid→CubeP (λ i j k → P (trunc x y p q r s i j k))
      (λ j k → elim (r j k)) (λ j k → elim (s j k)) (λ i k → elim (p k)) (λ i k → elim (q k))
      (λ i j → elim x) (λ i j → elim y) (isGroupoid* y) i j k

module BSymRec {ℓ} {n : ℕ} {H : Type ℓ} (isGroupoidH : isGroupoid H)
  (base* : H)
  (loop* : Fin n → base* ≡ base*)
  (cancel* : (k : Fin n) → loop* k ≡ sym (loop* k))
  (comm* : (k l : Fin n) → suc (k .fst) <ᵗ l .fst → Square (loop* l) (loop* l) (loop* k) (loop* k))
  (braid₌* : (k l : Fin n) → suc (k .fst) ≡ l .fst → base* ≡ base*)
  (braid₁* : (k l : Fin n) (p : suc (k .fst) ≡ l .fst)
    → Square (sym (loop* k)) (loop* k) (loop* l) (braid₌* k l p))
  (braid₂* : (k l : Fin n) (p : suc (k .fst) ≡ l .fst)
    → Square (loop* l) (sym (loop* l)) (braid₌* k l p) (loop* k))
  where

  rec : BSym n → H
  rec =
    BSymElim.elim (λ _ → H)
      base*
      loop*
      cancel*
      comm*
      braid₌*
      braid₁*
      braid₂*
      (λ _ → isGroupoidH)

module BSymElimProp {ℓ} {n : ℕ} (P : BSym n → Type ℓ)
  (base* : P base)
  (isProp* : (z : BSym n) → isProp (P z))
  where

  elim : (z : BSym n) → P z
  elim =
    BSymElim.elim P
      base*
      (λ k → isProp→PathP (λ i → isProp* (loop k i)) _ _)
      (λ k → isProp→SquareP (λ i j → isProp* (cancel k i j)) _ _ _ _)
      (λ k l p → isProp→SquareP (λ i j → isProp* (comm k l p i j)) _ _ _ _)
      (λ k l p → isProp→PathP (λ i → isProp* (braid₌ k l p i)) _ _)
      (λ k l p → isProp→SquareP (λ i j → isProp* (braid₁ k l p i j)) _ _ _ _)
      (λ k l p → isProp→SquareP (λ i j → isProp* (braid₂ k l p i j)) _ _ _ _)
      (λ z → isOfHLevelSuc 2 (isProp→isSet (isProp* z)))

-- the concrete coxeter group

isConnectedBSym : isConnected 2 (BSym n)
isConnectedBSym = ∣ base ∣ₕ , Trunc.elim (λ _ → isOfHLevelSuc 1 (isOfHLevelTrunc 2 _ _))
  (BSymElimProp.elim (λ z → ∣ base ∣ₕ ≡ ∣ z ∣ₕ) refl (λ _ → isOfHLevelTrunc 2 _ _))

BSymConcrete : ℕ → ConcreteGroup ℓ-zero
BSymConcrete n .fst .B = BSym n
BSymConcrete n .fst .sh = base
BSymConcrete n .fst .isConnectedB = isConnectedBSym
BSymConcrete n .snd = trunc

-- models the coxeter presentation

loopModel : ConcreteGroup→Group (BSymConcrete n) ⊨ CoxeterPresentation n
loopModel .gen = loop
loopModel .rel (cancel k) = ap (_∙ loop k) (cancel k) ∙ lCancel (loop k)
loopModel .rel (comm k l p) = sym (Square→compPath (comm k l p))
loopModel .rel (braid k l p) = sym (Hexagon→compPath (braid₌ k l p) (braid₁ k l p) (braid₂ k l p))

module Univ (H : ConcreteGroup ℓ) {n : ℕ} where

  module _ (M : ConcreteGroup→Group H ⊨ CoxeterPresentation n) where

    rec : BSym n → H .fst .B
    rec =
      BSymRec.rec (H .snd)
        (H .fst .sh)
        (M .gen)
        (λ k → compPath≡refl→≡sym (M .rel (cancel k)))
        (λ k l p → compPath→Square (sym (M .rel (comm k l p))))
        (λ k l p → hex k l p .⬡₌)
        (λ k l p → hex k l p .⬡₁)
        (λ k l p → hex k l p .⬡₂)
      where
        open Hexagon
        hex : (k l : Fin n) → suc (k .fst) ≡ l .fst
          → Hexagon (M .gen k) (M .gen l) (M .gen k) (M .gen l) (M .gen k) (M .gen l)
        hex k l p = doubleCompPath→Hexagon (compPathEq→doubleCompPathEq (sym (M .rel (braid k l p))))

  _♯ : ConcreteGroup→Group H ⊨ CoxeterPresentation n → ∞GroupHom (BSymConcrete n .fst) (H .fst)
  (M ♯) .fst = rec M
  (M ♯) .snd = refl

  _♭ : ∞GroupHom (BSymConcrete n .fst) (H .fst) → ConcreteGroup→Group H ⊨ CoxeterPresentation n
  f ♭ = mapModel (ConcreteGroupHom→GroupHom (BSymConcrete n) H f) loopModel

  univ : isEquiv _♭
  univ = sorry
    -- TODO: universal property of BSym (univ)

-- shift up

↑loopModel : ConcreteGroup→Group (BSymConcrete (suc n)) ⊨ CoxeterPresentation n
↑loopModel .gen k = loop (fsuc k)
↑loopModel .rel (cancel k) = loopModel .rel (cancel (fsuc k))
↑loopModel .rel (comm k l p) = loopModel .rel (comm (fsuc k) (fsuc l) p)
↑loopModel .rel (braid k l p) = loopModel .rel (braid (fsuc k) (fsuc l) (ap suc p))

B↑ : ∞GroupHom (BSymConcrete n .fst) (BSymConcrete (suc n) .fst)
B↑ {n} = ↑loopModel ♯
  where open Univ (BSymConcrete (suc n))

-- symmetries of the delooping are the coxeter group

ΩBSym≃Sym : GroupEquiv (ConcreteGroup→Group (BSymConcrete n)) (CoxeterGroup n)
ΩBSym≃Sym = sorry
  -- TODO: symmetries of BSym are Sym (ΩBSym≃Sym)
  --  encode-decode with cover base ↦ Sym n, loop k ↦ ua (k ::_)
