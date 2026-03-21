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
      (λ {X = X} {Y = Y} p q → h* .f-⊗ X Y ∙ ap₂ {!B._⊗_!} p q ) -- h* .f-⊗ X Y ∙ ap (B._⊗ h Y) p  ∙ ap ((f ♯) X B.⊗_) q)
      (λ {X = X} {Y = Y} {Z = Z} p q r → {!!})
        -- let T = h* .f-α₁ X Y Z
        --     P : Square (f-α₌ h* X Y Z)
        --                (B.α (h X) (h Y) (h Z))
        --                (ap (B._⊗ h Z) (f-⊗ h* X Y))
        --                (ap (h X B.⊗_) (f-⊗ h* Y Z))
        --     P = h* .f-α₂ X Y Z

        --     R : Square (ap (B._⊗ h (Y FSMG.⊗ Z)) p)
        --                (ap (B._⊗ (h Y B.⊗ h Z)) p)
        --                (ap (h X B.⊗_) (h* .f-⊗ Y Z))
        --                (ap (((f ♯) X) B.⊗_) (h* .f-⊗ Y Z))
        --     R = B.⊗-bi p (f-⊗ h* Y Z)

        --     Q : Square (B.α (h X) (h Y) (h Z))
        --                (B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z))
        --                (ap₃ (λ X Y → B._⊗_ (X B.⊗ Y)) p q r)
        --                (ap₃ (λ X Y Z → X B.⊗ (Y B.⊗ Z)) p q r)
        --     Q = B.α-nat p q r

        --     -- U : Square (ap (B._⊗ h Z) (h* .f-⊗ X Y) ∙ ap (B._⊗ h Z) (ap (B._⊗ h Y) p) ∙ ap (B._⊗ h Z) (ap ((f ♯) X B.⊗_) q) ∙ ap ((((f ♯) X) B.⊗ ((f ♯) Y)) B.⊗_) r)
        --     --   (ap (B._⊗ h (Y FSMG.⊗ Z)) p ∙ ap ((f ♯) X B.⊗_) (h* .f-⊗ Y Z) ∙ ap (((f ♯) X) B.⊗_) (ap (B._⊗ h Z) q) ∙ ap (((f ♯) X) B.⊗_) (ap (((f ♯) Y) B.⊗_) r))
        --     --   (h* . f-α₌ X Y Z)
        --     --   (B.α ((f ♯) X) ((f ♯) Y) ((f ♯) Z))
        --     U = flipSquare (cornerComp P {!!} R)

        -- in {!!})
        {!!}
      -- (λ {X = X} p →
      --   let R : Square (h* .f-⊗ FSMG.𝕀 X) (sym (B.Λ (h X))) (ap h (FSMG.Λ X)) (ap (B._⊗ h X) (h* .f-𝕀))
      --       R = h* .f-Λ X
      --       S : Square (ap (B.𝕀 B.⊗_) p) p (B.Λ (h X)) (B.Λ ((f ♯) X))
      --       S = compPath→Square (S.Λ-nat*sq B* p)
      --       U : Square (sym (B.Λ (h X))) (sym (B.Λ ((f ♯) X))) p (ap (B.𝕀 B.⊗_) p)
      --       U = flipSquare (invSquare S)
      --       V : Square (h* .f-⊗ FSMG.𝕀 X) (sym (B.Λ ((f ♯) X))) (ap h (FSMG.Λ X) ∙ p) (ap (B._⊗ (h X)) (h* .f-𝕀) ∙ ap (B.𝕀 B.⊗_) p)
      --       V = R ∙v U
      --       T : Square (h* .f-⊗ FSMG.𝕀 X ∙ (ap (B._⊗ (h X)) (h* .f-𝕀) ∙ ap (B.𝕀 B.⊗_) p)) p (ap h (FSMG.Λ X)) (ap (f ♯) (FSMG.Λ X))
      --       T = morphSquare V
      --    in T)
      {!!} {!!} λ X → B.is-groupoid (h X) ((f ♯) X)

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
