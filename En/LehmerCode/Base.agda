{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module En.LehmerCode.Base where

open import En.Prelude
open FS
open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Data.Bool using ( _and_ )
open import Cubical.Data.Fin.LehmerCode as LC public using ( LehmerCode ; [] ; _∷_ )
open import Cubical.Data.Sum as ⊎ using ( _⊎_ ; inl ; inr )
open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.Relation.Nullary.Properties using ( isProp¬ )
open import En.BAut.Base

private
  variable
    n : ℕ

isContrLehmerOne : isContr (LehmerCode 1)
isContrLehmerOne = isOfHLevelRespectEquiv 0 LC.lehmerSucEquiv (isContrΣ FN.isContrFin1 λ _ → LC.isContrLehmerZero)

punchIn : (k : Fin (suc n)) → Fin n → Fin (suc n)
punchIn (inl _) y = inr y
punchIn {zero} (inr ()) _
punchIn {suc n} (inr k) (inl _) = inl tt
punchIn {suc n} (inr k) (inr y) = inr (punchIn k y)

punchIn-≢ : (k : Fin (suc n)) (y : Fin n) → ¬ k ≡ punchIn k y
punchIn-≢ (inl _) y = ⊎.⊎Path.inl≢inr _ _
punchIn-≢ {zero} (inr ()) _
punchIn-≢ {suc n} (inr k) (inl _) = ⊎.⊎Path.inl≢inr _ _ ∘ sym
punchIn-≢ {suc n} (inr k) (inr y) = punchIn-≢ k y ∘ isEmbedding→Inj ⊎.isEmbedding-inr _ _

punchOut : (k x : Fin (suc n)) → ¬ k ≡ x → Fin n
punchOut (inl _) (inl _) p = ⊥.rec (p refl)
punchOut (inl _) (inr y) _ = y
punchOut {zero} (inr ()) _ _
punchOut {suc n} (inr k) (inl _) _ = inl tt
punchOut {suc n} (inr k) (inr y) p = inr (punchOut k y (p ∘ ap inr))

punchOut∘In : (k : Fin (suc n)) (y : Fin n) (p : ¬ k ≡ punchIn k y) → punchOut k (punchIn k y) p ≡ y
punchOut∘In (inl _) y p = refl
punchOut∘In {zero} (inr ()) _ _
punchOut∘In {suc n} (inr k) (inl _) p = refl
punchOut∘In {suc n} (inr k) (inr y) p = ap inr (punchOut∘In k y _)

punchIn∘Out : (k x : Fin (suc n)) (p : ¬ k ≡ x) → punchIn k (punchOut k x p) ≡ x
punchIn∘Out (inl _) (inl _) p = ⊥.rec (p refl)
punchIn∘Out (inl _) (inr y) _ = refl
punchIn∘Out {zero} (inr ()) _ _
punchIn∘Out {suc n} (inr k) (inl _) _ = refl
punchIn∘Out {suc n} (inr k) (inr y) p = ap inr (punchIn∘Out k y _)

punchOut≡ : {k k' x x' : Fin (suc n)} (p : k ≡ k') (q : x ≡ x') (u : ¬ k ≡ x) (v : ¬ k' ≡ x')
  → punchOut k x u ≡ punchOut k' x' v
punchOut≡ p q u v i = punchOut (p i) (q i) (isProp→PathP (λ i → isProp¬ (p i ≡ q i)) u v i)

punchOutEquiv : (k : Fin (suc n)) → Fin (suc n) ∖ k ≃ Fin n
punchOutEquiv k = isoToEquiv (iso (λ (x , p) → punchOut k x p) (λ y → punchIn k y , punchIn-≢ k y)
  (λ y → punchOut∘In k y _) (λ (x , p) → Σ≡Prop (λ _ → isProp¬ _) (punchIn∘Out k x p)))

punchIn-flast : (y : Fin n) → punchIn flast y ≡ finj y
punchIn-flast {suc n} (inl _) = refl
punchIn-flast {suc n} (inr y) = ap inr (punchIn-flast y)

insertAt : Fin (suc n) → Fin n ⊎ Unit → Fin (suc n)
insertAt k = ⊎.rec (punchIn k) (λ _ → k)

removeAt : Fin (suc n) → Fin (suc n) → Fin n ⊎ Unit
removeAt (inl _) (inl _) = inr tt
removeAt (inl _) (inr y) = inl y
removeAt {zero} (inr ()) _
removeAt {suc n} (inr k) (inl _) = inl (inl tt)
removeAt {suc n} (inr k) (inr y) = ⊎.map inr (idfun _) (removeAt k y)

private
  insertAt-inr : (k : Fin (suc n)) (u : Fin n ⊎ Unit) → insertAt (inr k) (⊎.map inr (idfun _) u) ≡ inr (insertAt k u)
  insertAt-inr k (inl _) = refl
  insertAt-inr k (inr _) = refl

insertAt∘removeAt : (k x : Fin (suc n)) → insertAt k (removeAt k x) ≡ x
insertAt∘removeAt (inl _) (inl _) = refl
insertAt∘removeAt (inl _) (inr y) = refl
insertAt∘removeAt {zero} (inr ()) _
insertAt∘removeAt {suc n} (inr k) (inl _) = refl
insertAt∘removeAt {suc n} (inr k) (inr y) = insertAt-inr k (removeAt k y) ∙ ap inr (insertAt∘removeAt k y)

removeAt∘punchIn : (k : Fin (suc n)) (y : Fin n) → removeAt k (punchIn k y) ≡ inl y
removeAt∘punchIn (inl _) y = refl
removeAt∘punchIn {zero} (inr ()) _
removeAt∘punchIn {suc n} (inr k) (inl _) = refl
removeAt∘punchIn {suc n} (inr k) (inr y) = ap (⊎.map inr (idfun _)) (removeAt∘punchIn k y)

removeAt-self : (k : Fin (suc n)) → removeAt k k ≡ inr tt
removeAt-self (inl _) = refl
removeAt-self {zero} (inr ())
removeAt-self {suc n} (inr k) = ap (⊎.map inr (idfun _)) (removeAt-self k)

insertAtEquiv : Fin (suc n) → (Fin n ⊎ Unit) ≃ Fin (suc n)
insertAtEquiv k = isoToEquiv (iso (insertAt k) (removeAt k) (insertAt∘removeAt k)
  λ { (inl y) → removeAt∘punchIn k y ; (inr _) → removeAt-self k })

opaque
  splitLastEquiv : Aut (Fin (suc n)) ≃ Fin (suc n) × Aut (Fin n)
  splitLastEquiv {n} =
    Aut (Fin (suc n))
      ≃⟨ equivComp (insertAtEquiv flast ⁻¹ₑ) (idEquiv _) ⟩
    ((Fin n ⊎ Unit) ≃ Fin (suc n))
      ≃⟨ ⊎Unit≃Σ∖ discreteFin ⟩
    (Σ[ k ∈ Fin (suc n) ] (Fin n ≃ Fin (suc n) ∖ k))
      ≃⟨ Σ-cong-equiv-snd (λ k → equivComp (idEquiv _) (punchOutEquiv k)) ⟩
    Fin (suc n) × Aut (Fin n)
      ■

-- running lehmer codes
-- 1 ∷ 1 ∷ 0 ∷ [] produces [0,2,1]: digits from the last, count smaller values to the left
-- cubical library produces [1,2,0]: digits from the first, count smaller values to the right

lehmerEquiv : Aut (Fin n) ≃ LehmerCode n
lehmerEquiv {zero} = isContr→Equiv (idEquiv _ , λ e → equivEq (funExt λ ())) LC.isContrLehmerZero
lehmerEquiv {suc n} =
  Aut (Fin (suc n))
    ≃⟨ splitLastEquiv ⟩
  Fin (suc n) × Aut (Fin n)
    ≃⟨ ≃-× (SumFin≃Fin _) lehmerEquiv ⟩
  FN.Fin (suc n) × LehmerCode n
    ≃⟨ LC.lehmerSucEquiv ⟩
  LehmerCode (suc n)
    ■

private
  digit : LehmerCode n → Fin n → ℕ
  digit (k ∷ c) x = ⊎.rec (digit c) (λ _ → k .fst) (removeAt flast x)

  smallerLeft : Aut (Fin n) → Fin n → ℕ
  smallerLeft e i = trueCount λ j → (toℕ j <ᵇ toℕ i) and (toℕ (–> e j) <ᵇ toℕ (–> e i))

  lehmerDigit : (e : Aut (Fin n)) (i : Fin n) → digit (–> lehmerEquiv e) i ≡ smallerLeft e i
  lehmerDigit = sorry
    -- TODO: lehmer digits count smaller values (lehmerDigit)
