{-# OPTIONS --allow-unsolved-metas #-}

module En.FSMG.Properties where

open import En.Prelude
open import En.FSMG.Base
import En.SMG as S hiding (SMG* ; SMG*Fun)

-- FSMG-has-SMG*Struct : ∀ {ℓ} (A : Type ℓ) → S.SMG*Struct (FSMG A)
-- FSMG-has-SMG*Struct A .S.𝕀 = 𝕀
-- FSMG-has-SMG*Struct A .S._⊗_ = _⊗_
-- FSMG-has-SMG*Struct A .S.α = α
-- FSMG-has-SMG*Struct A .S.Λ = Λ
-- FSMG-has-SMG*Struct A .S.ρ = ρ
-- FSMG-has-SMG*Struct A .S.β = β
-- FSMG-has-SMG*Struct A .S.▽ X Y = Triangle→compPath₃ (▽ X Y)
-- FSMG-has-SMG*Struct A .S.⬠ W X Y Z = Pentagon→compPath (⬠₌ W X Y Z) (⬠₁ W X Y Z) (⬠₂ W X Y Z)
-- FSMG-has-SMG*Struct A .S.⬡ X Y Z = Hexagon→compPath (⬡₌ X Y Z) (⬡₁ X Y Z) (⬡₂ X Y Z)
-- FSMG-has-SMG*Struct A .S.β² X Y = ap (_∙ β Y X) (β² X Y) ∙ lCancel (β Y X)
-- FSMG-has-SMG*Struct A .S.is-groupoid = is-groupoid

-- module Univ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) (SMGB : S.SMG*Struct B) where

--   module B = S.SMG*Struct SMGB

--   module _ (f : A → B) where

--     module F = FSMG*Rec A f B.𝕀 B._⊗_ B.α B.Λ B.ρ B.β
--         (λ X* Y* → compPath→Triangle₃ (B.▽ X* Y*))
--         (λ W* X* Y* Z* → B.α (W* B.⊗ X*) Y* Z* ∙ B.α W* X* (Y* B.⊗ Z*))
--         (λ W* X* Y* Z* → compPath→Pentagon (B.⬠ W* X* Y* Z*) .snd .fst)
--         (λ W* X* Y* Z* → compPath→Pentagon (B.⬠ W* X* Y* Z*) .snd .snd)
--         (λ X* Y* Z* → compPath→Hexagon (B.⬡ X* Y* Z*) .fst)
--         (λ X* Y* Z* → compPath→Hexagon (B.⬡ X* Y* Z*) .snd .fst)
--         (λ X* Y* Z* → compPath→Hexagon (B.⬡ X* Y* Z*) .snd .snd)
--         (λ X* Y* → Eq→Square₂₃ (B.β² X* Y*))
--         B.is-groupoid


--     _♯ : (FSMG A → B)
--     _♯ = F.f

--     ♯-SMG*Functor : S.SMG*Functor (FSMG A) (FSMG-has-SMG*Struct A) B SMGB (_♯)
--     ♯-SMG*Functor .S.f-𝕀 = refl
--     ♯-SMG*Functor .S.f-⊗ X Y = refl
--     ♯-SMG*Functor .S.f-α X Y Z = sorry
--     ♯-SMG*Functor .S.f-Λ X = sorry
--     ♯-SMG*Functor .S.f-ρ X = sorry
--     ♯-SMG*Functor .S.f-β X Y = sorry

FSMG* : ∀ {ℓ} (A : Type ℓ) → S.SMG*Sq (FSMG A)
FSMG* A .S.𝕀 = 𝕀
FSMG* A .S._⊗_ = _⊗_
FSMG* A .S.α = α
FSMG* A .S.Λ = Λ
FSMG* A .S.ρ = ρ
FSMG* A .S.β = β
FSMG* A .S.▽ = ▽
FSMG* A .S.⬠₌ = ⬠₌
FSMG* A .S.⬠₁ = ⬠₁
FSMG* A .S.⬠₂ = ⬠₂
FSMG* A .S.⬡₌ = ⬡₌
FSMG* A .S.⬡₁ = ⬡₁
FSMG* A .S.⬡₂ = ⬡₂
FSMG* A .S.β² = β²
FSMG* A .S.is-groupoid = is-groupoid

module Univ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) (B* : S.SMG*Sq B) where

  module B = S.SMG*Sq B*

  module _ (f : A → B) where

    module Rec = FSMG*Rec A f B.𝕀 B._⊗_ B.α B.Λ B.ρ B.β
                          B.▽ B.⬠₌ B.⬠₁ B.⬠₂ B.⬡₌ B.⬡₁ B.⬡₂ B.β² B.is-groupoid

    _♯ : FSMG A → B
    _♯ = Rec.rec

    _♯* : S.SMG*Fun*Sq (FSMG* A) B* _♯
    _♯* .S.f-𝕀 = refl
    _♯* .S.f-⊗ X Y = refl
    _♯* .S.f-α₌ X Y Z = ap _♯ (α X Y Z) -- B.α (X ♯) (Y ♯) (Z ♯)
    _♯* .S.f-α₁ X Y Z = constⱼSquare (ap _♯ (α X Y Z))
    _♯* .S.f-α₂ X Y Z = constⱼSquare (B.α (X ♯) (Y ♯) (Z ♯))
    _♯* .S.f-Λ X = Eq→Square₀₃ (lCancel (B.Λ (X ♯)))
    _♯* .S.f-ρ X = Eq→Square₀₃ (lCancel (B.ρ (X ♯)))
    _♯* .S.f-β X Y = constᵢSquare (B.β (X ♯) (Y ♯))

  _♭ : Σ (FSMG A → B) (S.SMG*Fun*Sq (FSMG* A) B*) → (A → B)
  _♭ (g , _) = g ∘ η

  ♯-uniq : (f : A → B) (h : FSMG A → B) (h* : S.SMG*Fun*Sq (FSMG* A) B* h) → (h ∘ η ≡ f) → ∀ xs → h xs ≡ (f ♯) xs
  ♯-uniq f h h* p = let open S in
    FSMG*Elim*Set.elim A
      (λ a → ap (_$ a) p)
      (h* .f-𝕀)
      (λ {X = X} {Y = Y} p q → h* .f-⊗ X Y ∙ ap₂ B._⊗_ p q ) -- h* .f-⊗ X Y ∙ ap (B._⊗ h Y) p  ∙ ap ((f ♯) X B.⊗_) q)
      (λ {X = X} {Y = Y} {Z = Z} p q r → compPath→Square (
      (ap h (FSMG.α X Y Z)) ∙ f-⊗ h* X (Y FSMG.⊗ Z) ∙ ap₂ B._⊗_ p (f-⊗ h* Y Z ∙ ap₂ B._⊗_ q r) ≡⟨ ap (λ x → (ap h (FSMG.α X Y Z)) ∙ f-⊗ h* X (Y FSMG.⊗ Z) ∙ ap₂ B._⊗_ x (f-⊗ h* Y Z ∙ ap₂ B._⊗_ q r)) (rUnit p) ⟩
      (ap h (FSMG.α X Y Z)) ∙ f-⊗ h* X (Y FSMG.⊗ Z) ∙ ap₂ B._⊗_ (p ∙ refl) (f-⊗ h* Y Z ∙ ap₂ B._⊗_ q r) ≡⟨ ap (λ x → (ap h (FSMG.α X Y Z)) ∙ f-⊗ h* X (Y FSMG.⊗ Z) ∙ x) (ap₂-∙ B._⊗_ p refl (f-⊗ h* Y Z) (ap₂ B._⊗_ q r)) ⟩
      (ap h (FSMG.α X Y Z)) ∙ f-⊗ h* X (Y FSMG.⊗ Z) ∙ (ap₂ B._⊗_ p (f-⊗ h* Y Z)) ∙ ap₂ (B._⊗_) refl (ap₂ B._⊗_ q r) ≡⟨ ap (λ z → (ap h (FSMG.α X Y Z)) ∙ f-⊗ h* X (Y FSMG.⊗ Z) ∙ z) (Square→compPath (flipSquare (λ i j → (p j) B.⊗ pqpq (f-⊗ h* Y Z) (ap₂ B._⊗_ q r) i j))) ⟩
      (ap h (FSMG.α X Y Z)) ∙ f-⊗ h* X (Y FSMG.⊗ Z) ∙ ap ((h X) B.⊗_) (f-⊗ h* Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r ≡⟨ assoc (ap h (FSMG.α X Y Z)) (f-⊗ h* X (Y FSMG.⊗ Z)) (ap ((h X) B.⊗_) (h* .f-⊗ Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r) ⟩
      ((ap h (FSMG.α X Y Z)) ∙ f-⊗ h* X (Y FSMG.⊗ Z)) ∙ ap ((h X) B.⊗_) (h* .f-⊗ Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r ≡⟨ ap (λ z → z ∙ ap ((h X) B.⊗_) (h* .f-⊗ Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r) (sym (Square→compPath (h* .f-α₁ X Y Z))) ⟩
      (h* .f-⊗ (X FSMG.⊗ Y) Z ∙ h* .f-α₌ X Y Z) ∙ ap ((h X) B.⊗_) (h* .f-⊗ Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r ≡⟨ sym (assoc (h* .f-⊗ (X FSMG.⊗ Y) Z) (h* .f-α₌ X Y Z) (ap ((h X) B.⊗_) (h* .f-⊗ Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r)) ⟩
      h* .f-⊗ (X FSMG.⊗ Y) Z ∙ h* .f-α₌ X Y Z ∙ ap ((h X) B.⊗_) (h* .f-⊗ Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r ≡⟨ ap ((h* .f-⊗ (X FSMG.⊗ Y) Z) ∙_) (assoc (h* .f-α₌ X Y Z) (ap ((h X) B.⊗_) (h* .f-⊗ Y Z)) (ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r)) ⟩
      h* .f-⊗ (X FSMG.⊗ Y) Z ∙ (h* .f-α₌ X Y Z ∙ ap ((h X) B.⊗_) (h* .f-⊗ Y Z)) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r ≡⟨ ap (λ z → h* .f-⊗ (X FSMG.⊗ Y) Z ∙ z ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r) (sym (Square→compPath (h* .f-α₂ X Y Z))) ⟩
      h* .f-⊗ (X FSMG.⊗ Y) Z ∙ (ap (B._⊗ h Z) (f-⊗ h* X Y) ∙ B.α (h X) (h Y) (h Z)) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r ≡⟨ ap (h* .f-⊗ (X FSMG.⊗ Y) Z ∙_ ) (sym (assoc (ap (B._⊗ h Z) (f-⊗ h* X Y)) (B.α (h X) (h Y) (h Z)) (ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r))) ⟩
      h* .f-⊗ (X FSMG.⊗ Y) Z ∙ ap (B._⊗ h Z) (f-⊗ h* X Y) ∙ B.α (h X) (h Y) (h Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r ≡⟨ ap (λ z → h* .f-⊗ (X FSMG.⊗ Y) Z ∙ ap (B._⊗ h Z) (f-⊗ h* X Y) ∙ z ) (sym (Square→compPath (B.α-nat p q r))) ⟩
      h* .f-⊗ (X FSMG.⊗ Y) Z ∙ ap (B._⊗ h Z) (f-⊗ h* X Y) ∙ ap₃ (λ x y z → (x B.⊗ y) B.⊗ z) p q r ∙ B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z) ≡⟨ ap (h* .f-⊗ (X FSMG.⊗ Y) Z ∙_) (assoc (ap (B._⊗ h Z) (f-⊗ h* X Y)) (ap₃ (λ x y z → (x B.⊗ y) B.⊗ z) p q r) (B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z))) ⟩
      h* .f-⊗ (X FSMG.⊗ Y) Z ∙ (ap (B._⊗ h Z) (f-⊗ h* X Y) ∙ ap₃ (λ x y z → (x B.⊗ y) B.⊗ z) p q r) ∙ B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z) ≡⟨ ap (λ z → h* .f-⊗ (X FSMG.⊗ Y) Z ∙ z ∙ B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z)) (Square→compPath (λ i j → pqpq (f-⊗ h* X Y) (ap₂ B._⊗_ p q) i j B.⊗ r j)) ⟩
      h* .f-⊗ (X FSMG.⊗ Y) Z ∙ (ap₂ B._⊗_ (h* .f-⊗ X Y) r ∙ ap₂ (B._⊗_) (ap₂ (B._⊗_) p q) refl) ∙ B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z) ≡⟨ ap (h* .f-⊗ (X FSMG.⊗ Y) Z ∙_) (sym (assoc (ap₂ B._⊗_ (h* .f-⊗ X Y) r) (ap₂ (B._⊗_) (ap₂ (B._⊗_) p q) refl) (B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z)))) ⟩
      h* .f-⊗ (X FSMG.⊗ Y) Z ∙ ap₂ B._⊗_ (h* .f-⊗ X Y) r ∙ ap₂ (B._⊗_) (ap₂ (B._⊗_) p q) refl ∙ B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z) ≡⟨  ap (h* .f-⊗ (X FSMG.⊗ Y) Z ∙_) (assoc (ap₂ B._⊗_ (h* .f-⊗ X Y) r) (ap₂ (B._⊗_) (ap₂ (B._⊗_) p q) refl) (B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z)))⟩
      h* .f-⊗ (X FSMG.⊗ Y) Z ∙ (ap₂ B._⊗_ (h* .f-⊗ X Y) r ∙ ap₂ (B._⊗_) (ap₂ (B._⊗_) p q) refl) ∙ B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z) ≡⟨  ap (λ x → (f-⊗ h* (X FSMG.⊗ Y) Z ∙ x ∙ B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z))) (ap-lemma B._⊗_ p q r (h* .f-⊗ X Y)) ⟩
      h* .f-⊗ (X FSMG.⊗ Y) Z ∙ (ap₂ B._⊗_ (h* .f-⊗ X Y ∙ ap₂ B._⊗_ p q) r) ∙ (λ i → (f ♯) (FSMG.α X Y Z i)) ≡⟨ assoc (f-⊗ h* (X FSMG.⊗ Y) Z)
                                                                                                                (ap₂ B._⊗_ (f-⊗ h* X Y ∙ ap₂ B._⊗_ p q) r)
                                                                                                                (λ i → (f ♯) (FSMG.α X Y Z i)) ⟩
      (h* .f-⊗ (X FSMG.⊗ Y) Z ∙ ap₂ B._⊗_ (h* .f-⊗ X Y ∙ ap₂ B._⊗_ p q) r) ∙ (λ i → (f ♯) (FSMG.α X Y Z i)) ∎
      ))
      (λ {X = X} p →
        let R : Square (h* .f-⊗ FSMG.𝕀 X) (sym (B.Λ (h X))) (ap h (FSMG.Λ X)) (ap (B._⊗ h X) (h* .f-𝕀))
            R = h* .f-Λ X
            S : Square (ap (B.𝕀 B.⊗_) p) p (B.Λ (h X)) (B.Λ ((f ♯) X))
            S = compPath→Square (S.Λ-nat*sq B* p)
            V : Square (h* .f-⊗ FSMG.𝕀 X) (sym (B.Λ ((f ♯) X))) (ap h (FSMG.Λ X) ∙ p) (ap (B._⊗ (h X)) (h* .f-𝕀) ∙ ap (B.𝕀 B.⊗_) p)
            V = R ∙v (flipSquare (invSquareh S))
            in tpt (λ x → Square (f-⊗ h* FSMG.𝕀 X ∙ x) p (ap h (FSMG.Λ X)) (ap (f ♯) (FSMG.Λ X)))
               (sym (Square→compPath (ap₂-coh₁ B._⊗_ (h* .f-𝕀) p)) ∙ sym (rUnit _)) (morphSquare V))
      (λ {X = X} q i j → hcomp
        (λ k →
           λ { (i = i0) → {!!}
             ; (i = i1) → {!constSquare1 q (~ j) k!}
             ; (j = i0) → {!invSquarev (h* .f-ρ X) i k!}
             ; (j = i1) → {!!}
           })
        {!!})
      {!!}
      λ X → B.is-groupoid (h X) ((f ♯) X)

  ♭-retract : retract _♭ (λ f → (f ♯) , (f ♯*))
  ♭-retract (f , f*) = let open S in
    ΣPathP (funExt (
      FSMG*Elim*Set.elim A (λ _ → refl)
        (sym (f* .f-𝕀))
        (λ {X = X} {Y = Y} p q → ap₂ B._⊗_ p q ∙ sym (f* .f-⊗ X Y))
        (λ {X = X} {Y = Y} {Z = Z} p q r → {!!})
        (λ {X = X} p → {!!})
        {!!} {!!} λ X → B.is-groupoid ((((f , f*) ♭) ♯) X) (f X))
      ,
      {!!}
    )

  univ : isEquiv _♭
  univ = isoToIsEquiv (
    iso _♭ (λ f → f ♯ , f ♯*)
      (λ _ → refl)
      ♭-retract
    )
      -- (λ { (g , g*) → let open S in

    --       ΣPathP (funExt (FSMG*Elim*Set.elim A (λ _ → refl) (sym (g* .f-𝕀))
    --         (λ {X = X} {Y = Y} p q → (ap₂ B._⊗_ p q ∙ sym (g* .f-⊗ X Y)))
    --         (λ {X = X} {Y = Y} {Z = Z} p q r → let q = B.α (g X) (g Y) (g Z) ; r = g* .f-α₌ X Y Z in {!!})
    --         (λ {X = X} p → {!!})
    --         {!!}
    --         {!!}
    --     })
    -- )
