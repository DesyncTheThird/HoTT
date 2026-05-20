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
--     ♯-SMG*Functor .S.hom-𝕀 = refl
--     ♯-SMG*Functor .S.-⊗ X Y = refl
--     ♯-SMG*Functor .S.-α X Y Z = sorry
--     ♯-SMG*Functor .S.-Λ X = sorry
--     ♯-SMG*Functor .S.-ρ X = sorry
--     ♯-SMG*Functor .S.-β X Y = sorry

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
    _♯* .S.-𝕀 = refl
    _♯* .S.-⊗ X Y = refl
    _♯* .S.-α₌ X Y Z = ap _♯ (α X Y Z) -- B.α (X ♯) (Y ♯) (Z ♯)
    _♯* .S.-α₁ X Y Z i j = (ap _♯ (α X Y Z)) j
    _♯* .S.-α₂ X Y Z i j = (B.α (X ♯) (Y ♯) (Z ♯)) j
    _♯* .S.-Λ X = Eq→Square₀₃ (lCancel (B.Λ (X ♯)))
    _♯* .S.-ρ X = Eq→Square₀₃ (lCancel (B.ρ (X ♯)))
    _♯* .S.-β X Y i j = (B.β (X ♯) (Y ♯)) i

  _♭ : Σ (FSMG A → B) (S.SMG*Fun*Sq (FSMG* A) B*) → (A → B)
  _♭ (g , _) = g ∘ η

  ♯-uniq : (f : A → B) (h : FSMG A → B) (h* : S.SMG*Fun*Sq (FSMG* A) B* h) → (h ∘ η ≡ f) → ∀ xs → h xs ≡ (f ♯) xs
  ♯-uniq f h h* p = let open S in
    FSMG*Elim*Set.elim A
      (λ a → ap (_$ a) p)
      (h* .-𝕀)
      (λ {X = X} {Y = Y} p q → h* .-⊗ X Y ∙ ap₂ B._⊗_ p q ) -- h* .-⊗ X Y ∙ ap (B._⊗ h Y) p  ∙ ap ((f ♯) X B.⊗_) q)
      (λ {X = X} {Y = Y} {Z = Z} p q r → compPath→Square (
          (ap h (FSMG.α X Y Z)) ∙ -⊗ h* X (Y FSMG.⊗ Z) ∙ ap₂ B._⊗_ p (-⊗ h* Y Z ∙ ap₂ B._⊗_ q r)
        ≡⟨ ap (λ x → (ap h (FSMG.α X Y Z)) ∙ -⊗ h* X (Y FSMG.⊗ Z) ∙ ap₂ B._⊗_ x (-⊗ h* Y Z ∙ ap₂ B._⊗_ q r)) (rUnit p) ⟩
          (ap h (FSMG.α X Y Z)) ∙ -⊗ h* X (Y FSMG.⊗ Z) ∙ ap₂ B._⊗_ (p ∙ refl) (-⊗ h* Y Z ∙ ap₂ B._⊗_ q r)
        ≡⟨ ap (λ x → (ap h (FSMG.α X Y Z)) ∙ -⊗ h* X (Y FSMG.⊗ Z) ∙ x) (ap₂-∙ B._⊗_ p refl (-⊗ h* Y Z) (ap₂ B._⊗_ q r)) ⟩
          (ap h (FSMG.α X Y Z)) ∙ -⊗ h* X (Y FSMG.⊗ Z) ∙ (ap₂ B._⊗_ p (-⊗ h* Y Z)) ∙ ap₂ (B._⊗_) refl (ap₂ B._⊗_ q r)
        ≡⟨ ap (λ z → (ap h (FSMG.α X Y Z)) ∙ -⊗ h* X (Y FSMG.⊗ Z) ∙ z) (Square→compPath (flipSquare (λ i j → (p j) B.⊗ pqpq (-⊗ h* Y Z) (ap₂ B._⊗_ q r) i j))) ⟩
          (ap h (FSMG.α X Y Z)) ∙ -⊗ h* X (Y FSMG.⊗ Z) ∙ ap ((h X) B.⊗_) (-⊗ h* Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r
        ≡⟨ assoc (ap h (FSMG.α X Y Z)) (-⊗ h* X (Y FSMG.⊗ Z)) (ap ((h X) B.⊗_) (h* .-⊗ Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r) ⟩
          ((ap h (FSMG.α X Y Z)) ∙ -⊗ h* X (Y FSMG.⊗ Z)) ∙ ap ((h X) B.⊗_) (h* .-⊗ Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r
        ≡⟨ ap (λ z → z ∙ ap ((h X) B.⊗_) (h* .-⊗ Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r) (sym (Square→compPath (h* .-α₁ X Y Z))) ⟩
          (h* .-⊗ (X FSMG.⊗ Y) Z ∙ h* .-α₌ X Y Z) ∙ ap ((h X) B.⊗_) (h* .-⊗ Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r
        ≡⟨ sym (assoc (h* .-⊗ (X FSMG.⊗ Y) Z) (h* .-α₌ X Y Z) (ap ((h X) B.⊗_) (h* .-⊗ Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r)) ⟩
          h* .-⊗ (X FSMG.⊗ Y) Z ∙ h* .-α₌ X Y Z ∙ ap ((h X) B.⊗_) (h* .-⊗ Y Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r
        ≡⟨ ap ((h* .-⊗ (X FSMG.⊗ Y) Z) ∙_) (assoc (h* .-α₌ X Y Z) (ap ((h X) B.⊗_) (h* .-⊗ Y Z)) (ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r)) ⟩
          h* .-⊗ (X FSMG.⊗ Y) Z ∙ (h* .-α₌ X Y Z ∙ ap ((h X) B.⊗_) (h* .-⊗ Y Z)) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r
        ≡⟨ ap (λ z → h* .-⊗ (X FSMG.⊗ Y) Z ∙ z ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r) (sym (Square→compPath (h* .-α₂ X Y Z))) ⟩
          h* .-⊗ (X FSMG.⊗ Y) Z ∙ (ap (B._⊗ h Z) (-⊗ h* X Y) ∙ B.α (h X) (h Y) (h Z)) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r
        ≡⟨ ap (h* .-⊗ (X FSMG.⊗ Y) Z ∙_ ) (sym (assoc (ap (B._⊗ h Z) (-⊗ h* X Y)) (B.α (h X) (h Y) (h Z)) (ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r))) ⟩
          h* .-⊗ (X FSMG.⊗ Y) Z ∙ ap (B._⊗ h Z) (-⊗ h* X Y) ∙ B.α (h X) (h Y) (h Z) ∙ ap₃ (λ x y z → x B.⊗ (y B.⊗ z)) p q r
        ≡⟨ ap (λ z → h* .-⊗ (X FSMG.⊗ Y) Z ∙ ap (B._⊗ h Z) (-⊗ h* X Y) ∙ z ) (sym (Square→compPath (B.α-nat p q r))) ⟩
          h* .-⊗ (X FSMG.⊗ Y) Z ∙ ap (B._⊗ h Z) (-⊗ h* X Y) ∙ ap₃ (λ x y z → (x B.⊗ y) B.⊗ z) p q r ∙ B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z)
        ≡⟨ ap (h* .-⊗ (X FSMG.⊗ Y) Z ∙_) (assoc (ap (B._⊗ h Z) (-⊗ h* X Y)) (ap₃ (λ x y z → (x B.⊗ y) B.⊗ z) p q r) (B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z))) ⟩
          h* .-⊗ (X FSMG.⊗ Y) Z ∙ (ap (B._⊗ h Z) (-⊗ h* X Y) ∙ ap₃ (λ x y z → (x B.⊗ y) B.⊗ z) p q r) ∙ B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z)
        ≡⟨ ap (λ z → h* .-⊗ (X FSMG.⊗ Y) Z ∙ z ∙ B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z)) (Square→compPath (λ i j → pqpq (-⊗ h* X Y) (ap₂ B._⊗_ p q) i j B.⊗ r j)) ⟩
          h* .-⊗ (X FSMG.⊗ Y) Z ∙ (ap₂ B._⊗_ (h* .-⊗ X Y) r ∙ ap₂ (B._⊗_) (ap₂ (B._⊗_) p q) refl) ∙ B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z)
        ≡⟨ ap (λ x → (-⊗ h* (X FSMG.⊗ Y) Z ∙ x ∙ B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z))) (ap-lemma B._⊗_ p q r (h* .-⊗ X Y)) ⟩
          h* .-⊗ (X FSMG.⊗ Y) Z ∙ (ap₂ B._⊗_ (h* .-⊗ X Y ∙ ap₂ B._⊗_ p q) r) ∙ (λ i → (f ♯) (FSMG.α X Y Z i))
        ≡⟨ assoc (-⊗ h* (X FSMG.⊗ Y) Z) (ap₂ B._⊗_ (-⊗ h* X Y ∙ ap₂ B._⊗_ p q) r) (λ i → (f ♯) (FSMG.α X Y Z i)) ⟩
          (h* .-⊗ (X FSMG.⊗ Y) Z ∙ ap₂ B._⊗_ (h* .-⊗ X Y ∙ ap₂ B._⊗_ p q) r) ∙ (λ i → (f ♯) (FSMG.α X Y Z i))
        ∎
      ))
      (λ {X = X} p →
        let R : Square (h* .-⊗ FSMG.𝕀 X) (sym (B.Λ (h X))) (ap h (FSMG.Λ X)) (ap (B._⊗ h X) (h* .-𝕀))
            R = h* .-Λ X
            S : Square (ap (B.𝕀 B.⊗_) p) p (B.Λ (h X)) (B.Λ ((f ♯) X))
            S = compPath→Square (S.Λ-nat*sq B* p)
            V : Square (h* .-⊗ FSMG.𝕀 X) (sym (B.Λ ((f ♯) X))) (ap h (FSMG.Λ X) ∙ p) (ap (B._⊗ (h X)) (h* .-𝕀) ∙ ap (B.𝕀 B.⊗_) p)
            V = R ∙v (flipSquare (invSquareh S))
            in tpt (λ x → Square (h* .-⊗ FSMG.𝕀 X ∙ x) p (ap h (FSMG.Λ X)) (ap (f ♯) (FSMG.Λ X)))
               (sym (Square→compPath (ap₂-coh₁ B._⊗_ (h* .-𝕀) p)) ∙ sym (rUnit _)) (morphSquare V)
               )
      (λ {X = X} q i j →
        let left1 : Square (sym (h* .-⊗ X FSMG.𝕀))
                           (refl {x = h X B.⊗ h FSMG.𝕀})
                           (refl {x = h X B.⊗ h FSMG.𝕀})
                           (h* .-⊗ X FSMG.𝕀)
            left1 i j = (h* .-⊗ X FSMG.𝕀) (i ∨ ~ j)
            left2 : Square (refl {x = h X B.⊗ h FSMG.𝕀})
                           (ap ((f ♯) X B.⊗_) (h* .-𝕀))
                           (ap (B._⊗ h FSMG.𝕀) q)
                           (ap₂ B._⊗_ q (h* .-𝕀))
            left2 i j = B._⊗_ (q i) (h* .-𝕀 (i ∧ j))
            left : Square (sym (h* .-⊗ X FSMG.𝕀))
                          (ap ((f ♯) X B.⊗_) (h* .-𝕀))
                          (ap (B._⊗ h FSMG.𝕀) q)
                          (h* .-⊗ X FSMG.𝕀 ∙ ap₂ B._⊗_ q (h* .-𝕀))
            left = tpt (λ x → Square (sym (h* .-⊗ X FSMG.𝕀))
                                     (ap ((f ♯) X B.⊗_) (h* .-𝕀))
                                     x
                                     (h* .-⊗ X FSMG.𝕀 ∙ ap₂ B._⊗_ q (h* .-𝕀))
                                     )
                       (sym (lUnit _)) (left1 ∙v left2)
            -- compPath→Square (assoc (sym (h* .-⊗ X FSMG.𝕀)) (h* .-⊗ X FSMG.𝕀) (ap₂ B._⊗_ q (h* .-𝕀)) ∙ ap (_∙ (ap₂ B._⊗_ q (h* .-𝕀))) (lCancel (h* .-⊗ X FSMG.𝕀)) ∙ Square→compPath (ap₂-coh₂ (flip B._⊗_) (h* .-𝕀) q))
            right : Square refl refl q q
            right i j = q i
            up' : Square (ap ((f ♯) X B.⊗_) (h* .-𝕀))
                         (B.ρ ((f ♯) X))
                         (ap ((f ♯) X B.⊗_) (h* .-𝕀))
                         (B.ρ ((f ♯) X))
            up' i j = pqpq (ap ((f ♯) X B.⊗_) (h* .-𝕀)) (B.ρ ((f ♯) X)) i j
            up : Square (ap ((f ♯) X B.⊗_) (h* .-𝕀))
                        (refl {x = (f ♯) X})
                        (ap ((f ♯) X B.⊗_) (h* .-𝕀) ∙ B.ρ ((f ♯) X))
                        (B.ρ ((f ♯) X))
            up = shiftSquare up'
            down' : Square (sym (h* .-⊗ X FSMG.𝕀))
                          (B.ρ (h X))
                          (ap (h X B.⊗_) (h* .-𝕀))
                          (ap h (FSMG.ρ X))
            down' i j = h* .-ρ X i (~ j)
            down : Square (sym (h* .-⊗ X FSMG.𝕀))
                          (refl {x = h X})
                          (ap (h X B.⊗_) (h* .-𝕀) ∙ B.ρ (h X))
                          (ap h (FSMG.ρ X))
            down = shiftSquare down'
            base1 : Square (ap (B._⊗ h FSMG.𝕀) q)
                           (ap (B._⊗ B.𝕀) q)
                           (ap ((h X) B.⊗_) (h* .-𝕀))
                           (ap ((f ♯) X B.⊗_) (h* .-𝕀))
            base1 = ⊗-bi B* q (h* .-𝕀)
            base2 : Square (ap (B._⊗ B.𝕀) q)
                           q
                           (B.ρ (h X))
                           (B.ρ ((f ♯) X))
            base2 = compPath→Square (ρ-nat*sq B* q)
            base : Square (ap (B._⊗ (h FSMG.𝕀)) q)
                          q
                          (ap (h X B.⊗_) (h* .-𝕀) ∙ B.ρ (h X))
                          (ap ((f ♯) X B.⊗_) (h* .-𝕀) ∙ B.ρ ((f ♯) X))
            base = base1 ∙v base2
            in
            hcomp
            (λ k →
               λ { (i = i0) → left j k
                 ; (i = i1) → right j k
                 ; (j = i0) → down i k
                 ; (j = i1) → up i k
               })
            (base i j)
            )
          (λ {X = X} {Y} q q' →
              let P : Square (h* .-⊗ X Y)
                             (h* .-⊗ Y X)
                             (ap h (FSMG.β X Y))
                             (B.β (h X) (h Y))
                  P = h*. -β X Y
                  Q : Square (ap₂ B._⊗_ q q')
                             (ap₂ B._⊗_ q' q)
                             (B.β (h X) (h Y))
                             (B.β ((f ♯) X) ((f ♯) Y))
                  Q = flipSquare (β-nat B* q q')
              in (P ∙h Q))
      λ X → B.is-groupoid (h X) ((f ♯) X)

  ♭-retract : retract _♭ (λ g → (g ♯) , (g ♯*))
  ♭-retract (g , g*) = ΣPathP ((funExt (λ x → sym (♯-uniq ((g , g*) ♭) g g* refl x)) , {!!}))

  univ : isEquiv _♭
  univ = isoToIsEquiv (
    iso _♭ (λ f → f ♯ , f ♯*)
      (λ _ → refl)
      ♭-retract
    )
