module En.Sn.Properties where

open import En.Prelude hiding ( _·_ )
open import Cubical.Algebra.Group
open import En.Sn.Base

private
  variable
    n : ℕ

-- group structure

isSetSym : isSet (Sym n)
isSetSym = trunc

++-assoc : (σ ρ υ : Sym n) → σ ++ (ρ ++ υ) ≡ (σ ++ ρ) ++ υ
++-assoc σ ρ υ =
  SymElimProp.elim (λ σ → σ ++ (ρ ++ υ) ≡ (σ ++ ρ) ++ υ)
    refl
    (λ k p → ap (k ::_) p)
    (λ _ → trunc _ _)
    σ

++-unit-r : (σ : Sym n) → σ ++ nil ≡ σ
++-unit-r =
  SymElimProp.elim (λ σ → σ ++ nil ≡ σ)
    refl
    (λ k p → ap (k ::_) p)
    (λ _ → trunc _ _)

private
  ++-assoc3 : (σ ρ υ ψ : Sym n) → ((σ ++ ρ) ++ υ) ++ ψ ≡ σ ++ (ρ ++ (υ ++ ψ))
  ++-assoc3 σ ρ υ ψ = sym (++-assoc (σ ++ ρ) υ ψ) ∙ sym (++-assoc σ ρ (υ ++ ψ))

rev : Sym n → Sym n
rev =
  SymElimSet.elim (λ _ → Sym _)
    nil
    (λ k τ → τ ++ [ k ])
    (λ k τ →
      sym (++-assoc τ [ k ] [ k ])
      ∙ ap (τ ++_) (cancel k nil) ∙ ++-unit-r τ)
    (λ k l p τ →
      sym (++-assoc τ [ k ] [ l ])
      ∙ ap (τ ++_) (sym (comm k l p nil))
      ∙ ++-assoc τ [ l ] [ k ])
    (λ k l p τ →
      ++-assoc3 τ [ l ] [ k ] [ l ]
      ∙ ap (τ ++_) (braid k l p nil)
      ∙ sym (++-assoc3 τ [ k ] [ l ] [ k ]))
    (λ _ → trunc)

++-revr : (σ : Sym n) → σ ++ rev σ ≡ nil
++-revr =
  SymElimProp.elim (λ σ → σ ++ rev σ ≡ nil)
    refl
    (λ k {σ} p → ap (k ::_) (++-assoc σ (rev σ) [ k ] ∙ ap (_++ [ k ]) p) ∙ cancel k nil)
    (λ _ → trunc _ _)

++-revl : (σ : Sym n) → rev σ ++ σ ≡ nil
++-revl =
  SymElimProp.elim (λ σ → rev σ ++ σ ≡ nil)
    refl
    (λ k {σ} p → sym (++-assoc (rev σ) [ k ] (k :: σ)) ∙ ap (rev σ ++_) (cancel k σ) ∙ p)
    (λ _ → trunc _ _)

CoxeterGroup : ℕ → Group₀
CoxeterGroup n = makeGroup {G = Sym n} nil _++_ rev trunc ++-assoc ++-unit-r (λ _ → refl) ++-revr ++-revl

isContrSym0 : isContr (Sym 0)
isContrSym0 = nil , SymElimProp.elim (λ σ → nil ≡ σ) refl (λ { (_ , ()) }) (λ _ → trunc _ _)
