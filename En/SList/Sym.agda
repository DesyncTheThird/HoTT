module En.SList.Sym where

open import En.Prelude hiding ( _·_ )
open FN hiding ( fzero ; fsuc )
open FS using ( fzero ; fsuc )
import Cubical.Data.Sum as ⊎
import Cubical.Data.Empty as ⊥
open import Cubical.HITs.GroupoidQuotients as GQ using ( _//_ ; [_] ; squash// )
open import Cubical.Algebra.Group.Morphisms
open import En.SList.Base
open import En.SList.1Cells using ( swap-nat )
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

  -- relabelling positions

  relabel : {m : ℕ} {g h : FS.Fin m → FS.Fin m} (v : FS.Fin m → A) → g ≡ h → FinVec→SList (v ∘ g) ≡ FinVec→SList (v ∘ h)
  relabel v = ap (λ g → FinVec→SList (v ∘ g))

  relabel-uniq : {m : ℕ} {g h : FS.Fin m → FS.Fin m} (v : FS.Fin m → A) (e e' : g ≡ h) → relabel v e ≡ relabel v e'
  relabel-uniq v e e' = ap (relabel v) (isSetΠ (λ _ → FS.isSetFin) _ _ e e')

  -- generators act by swaps

  swapAt : {n : ℕ} (k : Fin n) (u : FS.Fin (suc n) → A) → FinVec→SList u ≡ FinVec→SList (u ∘ τ {n} k)
  swapAt {zero} (_ , ())
  swapAt {suc n} (zero , _) u = swap (u fzero) (u (fsuc fzero)) (FinVec→SList (u ∘S fsuc ∘S fsuc))
  swapAt {suc n} (suc k , φ) u = ap (u fzero ::_) (swapAt {n} (k , φ) (u ∘ fsuc))

  swapAt-cancel : {n : ℕ} (k : Fin n) (u : FS.Fin (suc n) → A)
    → swapAt k u ∙ swapAt k (u ∘ τ k) ≡ sym (relabel u (funExt (τInvol k)))
  swapAt-cancel {zero} (_ , ())
  swapAt-cancel {suc n} (zero , φ) u =
    swap x y xs ∙ swap y x xs
      ≡⟨ ap (_∙ swap y x xs) (swap² x y xs) ⟩
    sym (swap y x xs) ∙ swap y x xs
      ≡⟨ lCancel (swap y x xs) ⟩
    sym (relabel u (funExt (τInvol (zero , φ))))
      ∎
    where
      x = u fzero
      y = u (fsuc fzero)
      xs = FinVec→SList (u ∘S fsuc ∘S fsuc)
  swapAt-cancel {suc n} (suc k , φ) u =
    ap (x ::_) (swapAt (k , φ) v) ∙ ap (x ::_) (swapAt (k , φ) (v ∘ τ (k , φ)))
      ≡⟨ sym (ap-∙ (x ::_) (swapAt (k , φ) v) (swapAt (k , φ) (v ∘ τ (k , φ)))) ⟩
    ap (x ::_) (swapAt (k , φ) v ∙ swapAt (k , φ) (v ∘ τ (k , φ)))
      ≡⟨ ap (ap (x ::_)) (swapAt-cancel (k , φ) v) ⟩
    sym (relabel u (funExt (τInvol (suc k , φ))))
      ∎
    where
      x = u fzero
      v = u ∘ fsuc

  swapAt-comm : {n : ℕ} (k l : Fin n) (ψ : suc (k .fst) <ᵗ l .fst) (u : FS.Fin (suc n) → A)
    → swapAt k u ∙ swapAt l (u ∘ τ k)
    ≡ (swapAt l u ∙ swapAt k (u ∘ τ l)) ∙ sym (relabel u (funExt (τComm k l ψ)))
  swapAt-comm {zero} (_ , ())
  swapAt-comm {suc n} (zero , _) (zero , _) ()
  swapAt-comm {suc n} (zero , _) (suc zero , _) ()
  swapAt-comm {suc zero} (zero , _) (suc (suc l) , ()) ψ u
  swapAt-comm {suc (suc n)} (zero , φ₁) (suc (suc l) , φ₂) ψ u =
    swap x y xs ∙ ap (λ zs → y :: x :: zs) (swapAt (l , φ₂) v)
      ≡⟨ swap-nat x y (swapAt (l , φ₂) v) ⟩
    ap (λ zs → x :: y :: zs) (swapAt (l , φ₂) v) ∙ swap x y ys
      ≡⟨ rUnit _ ⟩
    (ap (λ zs → x :: y :: zs) (swapAt (l , φ₂) v) ∙ swap x y ys) ∙ sym (relabel u (funExt c))
      ≡⟨ ap₂ _∙_ refl (ap sym (relabel-uniq u (funExt c) (funExt (τComm (zero , φ₁) (suc (suc l) , φ₂) ψ)))) ⟩
    (ap (λ zs → x :: y :: zs) (swapAt (l , φ₂) v) ∙ swap x y ys) ∙ sym (relabel u (funExt (τComm (zero , φ₁) (suc (suc l) , φ₂) ψ)))
      ∎
    where
      x = u fzero
      y = u (fsuc fzero)
      v = u ∘S fsuc ∘S fsuc
      xs = FinVec→SList v
      ys = FinVec→SList (v ∘ τ (l , φ₂))
      c : (w : FS.Fin (suc (suc (suc n)))) → τ (zero , φ₁) (τ (suc (suc l) , φ₂) w) ≡ τ (suc (suc l) , φ₂) (τ (zero , φ₁) w)
      c fzero = refl
      c (fsuc fzero) = refl
      c (fsuc (fsuc w)) = refl
  swapAt-comm {suc n} (suc k , _) (zero , _) ()
  swapAt-comm {suc n} (suc k , φ₁) (suc l , φ₂) ψ u =
    ap (x ::_) (swapAt (k , φ₁) v) ∙ ap (x ::_) (swapAt (l , φ₂) (v ∘ τ (k , φ₁)))
      ≡⟨ sym (ap-∙ (x ::_) (swapAt (k , φ₁) v) (swapAt (l , φ₂) (v ∘ τ (k , φ₁)))) ⟩
    ap (x ::_) (swapAt (k , φ₁) v ∙ swapAt (l , φ₂) (v ∘ τ (k , φ₁)))
      ≡⟨ ap (ap (x ::_)) (swapAt-comm (k , φ₁) (l , φ₂) ψ v) ⟩
    ap (x ::_) ((swapAt (l , φ₂) v ∙ swapAt (k , φ₁) (v ∘ τ (l , φ₂))) ∙ sym (relabel v (funExt (τComm (k , φ₁) (l , φ₂) ψ))))
      ≡⟨ ap-∙ (x ::_) _ _ ∙ ap₂ _∙_ (ap-∙ (x ::_) _ _) refl ⟩
    (ap (x ::_) (swapAt (l , φ₂) v) ∙ ap (x ::_) (swapAt (k , φ₁) (v ∘ τ (l , φ₂)))) ∙ sym (relabel u (funExt c))
      ≡⟨ ap₂ _∙_ refl (ap sym (relabel-uniq u (funExt c) (funExt (τComm (suc k , φ₁) (suc l , φ₂) ψ)))) ⟩
    (ap (x ::_) (swapAt (l , φ₂) v) ∙ ap (x ::_) (swapAt (k , φ₁) (v ∘ τ (l , φ₂)))) ∙ sym (relabel u (funExt (τComm (suc k , φ₁) (suc l , φ₂) ψ)))
      ∎
    where
      x = u fzero
      v = u ∘ fsuc
      c : (w : FS.Fin (suc (suc n))) → τ (suc k , φ₁) (τ (suc l , φ₂) w) ≡ τ (suc l , φ₂) (τ (suc k , φ₁) w)
      c fzero = refl
      c (fsuc w) = ap fsuc (τComm (k , φ₁) (l , φ₂) ψ w)

  swapAt-braid : {n : ℕ} (k l : Fin n) (δ : suc (k .fst) ≡ l .fst) (u : FS.Fin (suc n) → A)
    → swapAt l u ∙ swapAt k (u ∘ τ l) ∙ swapAt l (u ∘ τ l ∘ τ k)
    ≡ (swapAt k u ∙ swapAt l (u ∘ τ k) ∙ swapAt k (u ∘ τ k ∘ τ l)) ∙ sym (relabel u (funExt (τBraid k l δ)))
  swapAt-braid {zero} (_ , ())
  swapAt-braid {suc n} (zero , _) (zero , _) δ = ⊥.rec (snotz δ)
  swapAt-braid {suc n} (zero , _) (suc (suc l) , _) δ = ⊥.rec (znots (injSuc δ))
  swapAt-braid {suc zero} (zero , _) (suc zero , ()) δ u
  swapAt-braid {suc (suc n)} (zero , φ₁) (suc zero , φ₂) δ u =
    ap (x ::_) (swap y z xs) ∙ swap x z (y :: xs) ∙ ap (z ::_) (swap x y xs)
      ≡⟨ sym (Hexagon→compPath (⬡₌ x y z xs) (⬡₁ x y z xs) (⬡₂ x y z xs)) ⟩
    swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ swap y z (x :: xs)
      ≡⟨ rUnit _ ⟩
    (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ swap y z (x :: xs)) ∙ sym (relabel u (funExt c))
      ≡⟨ ap₂ _∙_ refl (ap sym (relabel-uniq u (funExt c) (funExt (τBraid (zero , φ₁) (suc zero , φ₂) δ)))) ⟩
    (swap x y (z :: xs) ∙ ap (y ::_) (swap x z xs) ∙ swap y z (x :: xs)) ∙ sym (relabel u (funExt (τBraid (zero , φ₁) (suc zero , φ₂) δ)))
      ∎
    where
      x = u fzero
      y = u (fsuc fzero)
      z = u (fsuc (fsuc fzero))
      xs = FinVec→SList (u ∘S fsuc ∘S fsuc ∘S fsuc)
      c : (w : FS.Fin (suc (suc (suc n)))) → τ (suc zero , φ₂) (τ (zero , φ₁) (τ (suc zero , φ₂) w)) ≡ τ (zero , φ₁) (τ (suc zero , φ₂) (τ (zero , φ₁) w))
      c fzero = refl
      c (fsuc fzero) = refl
      c (fsuc (fsuc fzero)) = refl
      c (fsuc (fsuc (fsuc w))) = refl
  swapAt-braid {suc n} (suc k , _) (zero , _) δ = ⊥.rec (snotz δ)
  swapAt-braid {suc n} (suc k , φ₁) (suc l , φ₂) δ u =
    ap (x ::_) (swapAt (l , φ₂) v) ∙ ap (x ::_) (swapAt (k , φ₁) (v ∘ τ (l , φ₂))) ∙ ap (x ::_) (swapAt (l , φ₂) (v ∘ τ (l , φ₂) ∘ τ (k , φ₁)))
      ≡⟨ sym (ap-∙ (x ::_) _ _ ∙ ap₂ _∙_ refl (ap-∙ (x ::_) _ _)) ⟩
    ap (x ::_) (swapAt (l , φ₂) v ∙ swapAt (k , φ₁) (v ∘ τ (l , φ₂)) ∙ swapAt (l , φ₂) (v ∘ τ (l , φ₂) ∘ τ (k , φ₁)))
      ≡⟨ ap (ap (x ::_)) (swapAt-braid (k , φ₁) (l , φ₂) (injSuc δ) v) ⟩
    ap (x ::_) ((swapAt (k , φ₁) v ∙ swapAt (l , φ₂) (v ∘ τ (k , φ₁)) ∙ swapAt (k , φ₁) (v ∘ τ (k , φ₁) ∘ τ (l , φ₂))) ∙ sym (relabel v (funExt (τBraid (k , φ₁) (l , φ₂) (injSuc δ)))))
      ≡⟨ ap-∙ (x ::_) _ _ ∙ ap₂ _∙_ (ap-∙ (x ::_) _ _ ∙ ap₂ _∙_ refl (ap-∙ (x ::_) _ _)) refl ⟩
    (ap (x ::_) (swapAt (k , φ₁) v) ∙ ap (x ::_) (swapAt (l , φ₂) (v ∘ τ (k , φ₁))) ∙ ap (x ::_) (swapAt (k , φ₁) (v ∘ τ (k , φ₁) ∘ τ (l , φ₂)))) ∙ sym (relabel u (funExt c))
      ≡⟨ ap₂ _∙_ refl (ap sym (relabel-uniq u (funExt c) (funExt (τBraid (suc k , φ₁) (suc l , φ₂) δ)))) ⟩
    (ap (x ::_) (swapAt (k , φ₁) v) ∙ ap (x ::_) (swapAt (l , φ₂) (v ∘ τ (k , φ₁))) ∙ ap (x ::_) (swapAt (k , φ₁) (v ∘ τ (k , φ₁) ∘ τ (l , φ₂)))) ∙ sym (relabel u (funExt (τBraid (suc k , φ₁) (suc l , φ₂) δ)))
      ∎
    where
      x = u fzero
      v = u ∘ fsuc
      c : (w : FS.Fin (suc (suc n))) → τ (suc l , φ₂) (τ (suc k , φ₁) (τ (suc l , φ₂) w)) ≡ τ (suc k , φ₁) (τ (suc l , φ₂) (τ (suc k , φ₁) w))
      c fzero = refl
      c (fsuc w) = ap fsuc (τBraid (k , φ₁) (l , φ₂) (injSuc δ) w)

  -- paths over relabellings, up to a pointwise relabelling

  relabel→PathP : {m : ℕ} {g h : FS.Fin m → FS.Fin m} (v : FS.Fin m → A) (e e' : g ≡ h)
    {x : SList A} {p : x ≡ FinVec→SList (v ∘ g)} {q : x ≡ FinVec→SList (v ∘ h)}
    → p ≡ q ∙ sym (relabel v e')
    → PathP (λ i → x ≡ relabel v e i) p q
  relabel→PathP v e e' {q = q} pq =
    (pq ∙ ap (λ r → q ∙ sym r) (relabel-uniq v e' e)) ◁ symP (compPath-filler q (sym (relabel v e)))

  -- words act by paths

  permute : {n : ℕ} (σ : Sym n) (v : FS.Fin (suc n) → A) → FinVec→SList v ≡ FinVec→SList (v ∘ –> (Sym→Aut σ))
  permute {n} =
    SymElimSet.elim P
      (λ v → refl)
      _::*_
      cancel*
      comm*
      braid*
      (λ σ → isSetΠ λ v → is-groupoid _ _)
    where
      P : Sym n → Type ℓ
      P σ = (v : FS.Fin (suc n) → A) → FinVec→SList v ≡ FinVec→SList (v ∘ –> (Sym→Aut σ))

      _::*_ : (k : Fin n) {σ : Sym n} → P σ → P (Sym._::_ k σ)
      _::*_ k {σ} f v = f v ∙ swapAt k (v ∘ –> (Sym→Aut σ))

      cancel* : (k : Fin n) {σ : Sym n} (f : P σ) → PathP (λ i → P (cancel k σ i)) (_::*_ k {Sym._::_ k σ} (_::*_ k {σ} f)) f
      cancel* k {σ} f i v = relabel→PathP v (λ j → –> (Sym→Aut (cancel k σ j))) e' pq i
        where
          ρ : FS.Fin (suc n) → FS.Fin (suc n)
          ρ = –> (Sym→Aut σ)
          e' : ρ ∘ τ k ∘ τ k ≡ ρ
          e' = funExt λ x → ap ρ (τInvol k x)
          pq : (f v ∙ swapAt k (v ∘ ρ)) ∙ swapAt k (v ∘ ρ ∘ τ k) ≡ f v ∙ sym (relabel v e')
          pq =
            (f v ∙ swapAt k (v ∘ ρ)) ∙ swapAt k (v ∘ ρ ∘ τ k)
              ≡⟨ sym (assoc _ _ _) ⟩
            f v ∙ (swapAt k (v ∘ ρ) ∙ swapAt k (v ∘ ρ ∘ τ k))
              ≡⟨ ap (f v ∙_) (swapAt-cancel k (v ∘ ρ)) ⟩
            f v ∙ sym (relabel v e')
              ∎

      comm* : (k l : Fin n) (ψ : suc (k .fst) <ᵗ l .fst) {σ : Sym n} (f : P σ)
        → PathP (λ i → P (comm k l ψ σ i))
            (_::*_ l {Sym._::_ k σ} (_::*_ k {σ} f))
            (_::*_ k {Sym._::_ l σ} (_::*_ l {σ} f))
      comm* k l ψ {σ} f i v = relabel→PathP v (λ j → –> (Sym→Aut (comm k l ψ σ j))) e' pq i
        where
          ρ : FS.Fin (suc n) → FS.Fin (suc n)
          ρ = –> (Sym→Aut σ)
          e' : ρ ∘ τ k ∘ τ l ≡ ρ ∘ τ l ∘ τ k
          e' = funExt λ x → ap ρ (τComm k l ψ x)
          s : FinVec→SList (v ∘ ρ ∘ τ l ∘ τ k) ≡ FinVec→SList (v ∘ ρ ∘ τ k ∘ τ l)
          s = sym (relabel v e')
          pq : (f v ∙ swapAt k (v ∘ ρ)) ∙ swapAt l (v ∘ ρ ∘ τ k)
             ≡ ((f v ∙ swapAt l (v ∘ ρ)) ∙ swapAt k (v ∘ ρ ∘ τ l)) ∙ s
          pq =
            (f v ∙ swapAt k (v ∘ ρ)) ∙ swapAt l (v ∘ ρ ∘ τ k)
              ≡⟨ sym (assoc _ _ _) ⟩
            f v ∙ (swapAt k (v ∘ ρ) ∙ swapAt l (v ∘ ρ ∘ τ k))
              ≡⟨ ap (f v ∙_) (swapAt-comm k l ψ (v ∘ ρ)) ⟩
            f v ∙ ((swapAt l (v ∘ ρ) ∙ swapAt k (v ∘ ρ ∘ τ l)) ∙ s)
              ≡⟨ assoc _ _ _ ∙ ap (_∙ s) (assoc _ _ _) ⟩
            ((f v ∙ swapAt l (v ∘ ρ)) ∙ swapAt k (v ∘ ρ ∘ τ l)) ∙ s
              ∎

      braid* : (k l : Fin n) (δ : suc (k .fst) ≡ l .fst) {σ : Sym n} (f : P σ)
        → PathP (λ i → P (braid k l δ σ i))
            (_::*_ l {Sym._::_ k (Sym._::_ l σ)} (_::*_ k {Sym._::_ l σ} (_::*_ l {σ} f)))
            (_::*_ k {Sym._::_ l (Sym._::_ k σ)} (_::*_ l {Sym._::_ k σ} (_::*_ k {σ} f)))
      braid* k l δ {σ} f i v = relabel→PathP v (λ j → –> (Sym→Aut (braid k l δ σ j))) e' pq i
        where
          ρ : FS.Fin (suc n) → FS.Fin (suc n)
          ρ = –> (Sym→Aut σ)
          e' : ρ ∘ τ l ∘ τ k ∘ τ l ≡ ρ ∘ τ k ∘ τ l ∘ τ k
          e' = funExt λ x → ap ρ (τBraid k l δ x)
          s : FinVec→SList (v ∘ ρ ∘ τ k ∘ τ l ∘ τ k) ≡ FinVec→SList (v ∘ ρ ∘ τ l ∘ τ k ∘ τ l)
          s = sym (relabel v e')
          pq : ((f v ∙ swapAt l (v ∘ ρ)) ∙ swapAt k (v ∘ ρ ∘ τ l)) ∙ swapAt l (v ∘ ρ ∘ τ l ∘ τ k)
             ≡ (((f v ∙ swapAt k (v ∘ ρ)) ∙ swapAt l (v ∘ ρ ∘ τ k)) ∙ swapAt k (v ∘ ρ ∘ τ k ∘ τ l)) ∙ s
          pq =
            ((f v ∙ swapAt l (v ∘ ρ)) ∙ swapAt k (v ∘ ρ ∘ τ l)) ∙ swapAt l (v ∘ ρ ∘ τ l ∘ τ k)
              ≡⟨ sym (assoc _ _ _) ∙ sym (assoc _ _ _) ⟩
            f v ∙ (swapAt l (v ∘ ρ) ∙ swapAt k (v ∘ ρ ∘ τ l) ∙ swapAt l (v ∘ ρ ∘ τ l ∘ τ k))
              ≡⟨ ap (f v ∙_) (swapAt-braid k l δ (v ∘ ρ)) ⟩
            f v ∙ ((swapAt k (v ∘ ρ) ∙ swapAt l (v ∘ ρ ∘ τ k) ∙ swapAt k (v ∘ ρ ∘ τ k ∘ τ l)) ∙ s)
              ≡⟨ assoc _ _ _ ∙ ap (_∙ s) (assoc _ _ _ ∙ assoc _ _ _) ⟩
            (((f v ∙ swapAt k (v ∘ ρ)) ∙ swapAt l (v ∘ ρ ∘ τ k)) ∙ swapAt k (v ∘ ρ ∘ τ k ∘ τ l)) ∙ s
              ∎

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
