module En.SList.Sym where

open import En.Prelude hiding ( _·_ )
open FN hiding ( fzero ; fsuc )
open FS using ( fzero ; fsuc )
import Cubical.Data.Sum as ⊎
open import Cubical.HITs.GroupoidQuotients as GQ using ( _//_ ; [_] ; squash// )
open import Cubical.Algebra.Group.Morphisms
open import En.SList.Base
open import En.Sn.Base hiding ( nil ; _::_ ; [_] )
open import En.Sn.Properties
open import En.Sn.Permutation
open import En.GroupAction.Base

-- vectors up to the coxeter groups acting on positions

Vec//𝔖 : Type ℓ → Type ℓ
Vec//𝔖 A = Σ[ m ∈ ℕ ] A ≀ 𝔖Action m

module _ {A : Type ℓ} where

  -- vectors as lists

  FinVec→SList : {n : ℕ} → (FS.Fin n → A) → SList A
  FinVec→SList {zero} v = nil
  FinVec→SList {suc n} v = v fzero :: FinVec→SList (v ∘ fsuc)

  -- words act by paths

  permute : {n : ℕ} (σ : Sym n) (v : FS.Fin (suc n) → A) → FinVec→SList v ≡ FinVec→SList (v ∘ –> (Sym→Aut σ))
  permute = sorry
    -- TODO: words act by paths (permute)
    --  by SymElimSet; generators by swapAt, relations by cancel, comm and braid lemmas for swapAt

  permute-++ : {n : ℕ} (σ ρ : Sym n) (v : FS.Fin (suc n) → A)
    → PathP (λ i → FinVec→SList v ≡ FinVec→SList (v ∘ –> (IsGroupHom.pres· (Sym→AutHom .snd) σ ρ i)))
        (permute (σ ++ ρ) v) (permute ρ v ∙ permute σ (v ∘ –> (Sym→Aut ρ)))
  permute-++ = sorry
    -- TODO: permute is functorial (permute-++)
    --  by SymElimProp

  -- vectors up to the coxeter group as lists

  FinVecRel→Path : (m : ℕ) {v w : FS.Fin m → A} → WreathRel (𝔖Action m) A v w → FinVec→SList v ≡ FinVec→SList w
  FinVecRel→Path zero _ = refl
  FinVecRel→Path (suc n) {v} (σ , l) = permute (rev σ) v ∙ ap FinVec→SList l

  Vec//𝔖→SList : Vec//𝔖 A → SList A
  Vec//𝔖→SList (m , x) =
    GQ.rec (isTransActionRel (preCompAction (𝔖Action m) A))
      is-groupoid
      FinVec→SList
      (FinVecRel→Path m)
      (λ r s → sorry)
      -- TODO: comp// case of Vec//𝔖→SList
      --  from permute-++ and naturality of permute
      x

  consVec : {m : ℕ} → A → (FS.Fin m → A) → FS.Fin (suc m) → A
  consVec x v = ⊎.rec (λ _ → x) v

  consVec//𝔖 : (m : ℕ) → A → A ≀ 𝔖Action m → A ≀ 𝔖Action (suc m)
  consVec//𝔖 m x =
    GQ.rec (isTransActionRel (preCompAction (𝔖Action m) A))
      squash//
      (λ v → [ consVec x v ])
      sorry
      -- TODO: eq// case of consVec//𝔖
      --  lifting relabellings along ↑
      sorry
      -- TODO: comp// case of consVec//𝔖
      --  from ↑Hom preserving composition

  SList→Vec//𝔖 : SList A → Vec//𝔖 A
  SList→Vec//𝔖 =
    SListElim.elim (λ _ → Vec//𝔖 A)
      (zero , [ (λ ()) ])
      (λ x o → suc (o .fst) , consVec//𝔖 (o .fst) x (o .snd))
      sorry
      -- TODO: swap case of SList→Vec//𝔖
      --  eq// of the first generator
      sorry
      -- TODO: swap² case of SList→Vec//𝔖
      --  from comp// and cancel
      sorry
      -- TODO: ⬡₌ case of SList→Vec//𝔖
      --  eq// of the reversal 0 1 0
      sorry
      -- TODO: ⬡₁ case of SList→Vec//𝔖
      --  from comp// and braid
      sorry
      -- TODO: ⬡₂ case of SList→Vec//𝔖
      --  from comp// and braid
      (λ _ → isGroupoidΣ (isSet→isGroupoid isSetℕ) λ _ → squash//)

  SList→Vec//𝔖→SList : (xs : SList A) → Vec//𝔖→SList (SList→Vec//𝔖 xs) ≡ xs
  SList→Vec//𝔖→SList = sorry
    -- TODO: round trip SList→Vec//𝔖→SList
    --  Vec//𝔖→SList ∘ SList→Vec//𝔖 is the identity; by SListElimSet

  Vec//𝔖→SList→Vec//𝔖 : (x : Vec//𝔖 A) → SList→Vec//𝔖 (Vec//𝔖→SList x) ≡ x
  Vec//𝔖→SList→Vec//𝔖 = sorry
    -- TODO: round trip Vec//𝔖→SList→Vec//𝔖
    --  SList→Vec//𝔖 ∘ Vec//𝔖→SList is the identity; by GQ.elimSet and SymElimProp

  SList≃Vec//𝔖 : SList A ≃ Vec//𝔖 A
  SList≃Vec//𝔖 = isoToEquiv (iso SList→Vec//𝔖 Vec//𝔖→SList Vec//𝔖→SList→Vec//𝔖 SList→Vec//𝔖→SList)
