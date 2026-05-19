-- {-# OPTIONS --show-implicit #-}
module En.SMG where

open import En.Prelude
open import Cubical.Reflection.RecordEquiv

record SMG* {ℓ} (El : Type ℓ) : Type ℓ where
  constructor smg*
  field
    𝕀 : El
    _⊗_ : El → El → El
  field
    α : (X Y Z : El) → (X ⊗ Y) ⊗ Z ≡ X ⊗ (Y ⊗ Z)
    Λ : (X : El) → 𝕀 ⊗ X ≡ X
    ρ : (X : El) → X ⊗ 𝕀 ≡ X
    β : (X Y : El) → X ⊗ Y ≡ Y ⊗ X
  field
    ▽ : (X Y : El) → sym (α X 𝕀 Y) ∙ ap (_⊗ Y) (ρ X) ≡ ap (X ⊗_) (Λ Y)
    ⬠ : (W X Y Z : El)
      → α (W ⊗ X) Y Z ∙ α W X (Y ⊗ Z)
      ≡ ap (_⊗ Z) (α W X Y) ∙ α W (X ⊗ Y) Z ∙ ap (W ⊗_) (α X Y Z)
    ⬡ : (X Y Z : El)
      → α X Y Z ∙ β X (Y ⊗ Z) ∙ α Y Z X
      ≡ ap (_⊗ Z) (β X Y) ∙ α Y X Z ∙ ap (Y ⊗_) (β X Z)
    β² : (X Y : El) → β X Y ∙ β Y X ≡ refl
    is-groupoid : isGroupoid El

  ⊗-bi : {X X' Y Y' : El} (p : X ≡ X') (q : Y ≡ Y')
    → Square (ap (_⊗ Y) p) (ap (_⊗ Y') p) (ap (X ⊗_) q) ( ap (X' ⊗_) q)
  ⊗-bi p q i j = p j ⊗ q i

  Λ-nat : {X Y : El} (p : X ≡ Y) → Λ X ∙ p ≡ ap (𝕀 ⊗_) p ∙ Λ Y
  Λ-nat p = homotopyNatural {f = λ X → 𝕀 ⊗ X} {g = λ X → X} Λ p

  ρ-nat : {X Y : El} (p : X ≡ Y) → ρ X ∙ p ≡ ap (_⊗ 𝕀) p ∙ ρ Y
  ρ-nat p = homotopyNatural ρ p

  α-nat : {X X' Y Y' Z Z' : El}
    (p : X ≡ X') (q : Y ≡ Y') (r : Z ≡ Z')
    → Square (α X Y Z) (α X' Y' Z') (ap₃ (λ X Y Z → (X ⊗ Y) ⊗ Z) p q r) (ap₃ (λ X Y Z → X ⊗ (Y ⊗ Z)) p q r)
  α-nat p q r i j = α (p i) (q i) (r i) j

record SMG*Fun {ℓ₁ ℓ₂}
  {A : Type ℓ₁} (A* : SMG* A)
  {B : Type ℓ₂} (B* : SMG* B)
  (f : A → B) : Type (ℓ-max ℓ₁ ℓ₂) where
  constructor smg*fun
  private
    module A = SMG* A*
    module B = SMG* B*
  field
    -𝕀 : f A.𝕀 ≡ B.𝕀
    -⊗ : (X Y : A) → f (X A.⊗ Y) ≡ f X B.⊗ f Y
  field
    -α : (X Y Z : A)
        → ap f (A.α X Y Z) ∙ -⊗ X (Y A.⊗ Z) ∙ ap (f X B.⊗_) (-⊗ Y Z)
        ≡ -⊗ (X A.⊗ Y) Z ∙ ap (B._⊗ f Z) (-⊗ X Y) ∙ B.α (f X) (f Y) (f Z)
    -Λ : (X : A) → ap f (A.Λ X) ≡ -⊗ (A.𝕀) X ∙ ap (B._⊗ f X) -𝕀 ∙ B.Λ (f X)
    -ρ : (X : A) → ap f (A.ρ X) ≡ -⊗ X (A.𝕀) ∙ ap (f X B.⊗_) -𝕀 ∙ B.ρ (f X)
    -β : (X Y : A) → ap f (A.β X Y) ∙ -⊗ Y X ≡ -⊗ X Y ∙ B.β (f X) (f Y)

open SMG*Fun public

record SMG*Sq {ℓ} (El : Type ℓ) : Type ℓ where
  constructor smg*sq
  field
    𝕀 : El
    _⊗_ : El → El → El
  field
    α : (X Y Z : El) → (X ⊗ Y) ⊗ Z ≡ X ⊗ (Y ⊗ Z)
    Λ : (X : El) → 𝕀 ⊗ X ≡ X
    ρ : (X : El) → X ⊗ 𝕀 ≡ X
    β : (X Y : El) → X ⊗ Y ≡ Y ⊗ X
  field
    ▽ : (X Y : El) → Square (ap (X ⊗_) (Λ Y)) (ap (_⊗ Y) (ρ X)) (sym (α X 𝕀 Y)) refl

    ⬠₌ : (W X Y Z : El)
        → ((W ⊗ X) ⊗ Y) ⊗ Z ≡ W ⊗ (X ⊗ (Y ⊗ Z))
    ⬠₁ : (W X Y Z : El)
        → Square (sym (α (W ⊗ X) Y Z)) (α W X (Y ⊗ Z)) refl (⬠₌ W X Y Z)
    ⬠₂ : (W X Y Z : El)
        → Square (ap (_⊗ Z) (α W X Y)) (sym (ap (W ⊗_) (α X Y Z))) (⬠₌ W X Y Z) (α W (X ⊗ Y) Z)

    ⬡₌ : (X Y Z : El)
        → (X ⊗ Y) ⊗ Z ≡ Y ⊗ (Z ⊗ X)
    ⬡₁ : (X Y Z : El)
        → Square (sym (α X Y Z)) (α Y Z X) (β X (Y ⊗ Z)) (⬡₌ X Y Z)
    ⬡₂ : (X Y Z : El)
        → Square (ap (_⊗ Z) (β X Y)) (ap (Y ⊗_) (sym (β X Z))) (⬡₌ X Y Z) (α Y X Z)

    β² : (X Y : El) → β X Y ≡ sym (β Y X)

    is-groupoid : isGroupoid El

  Λ-nat*sq : {X Y : El} (p : X ≡ Y) → Square (Λ X) (Λ Y) (ap (𝕀 ⊗_) p) p
  Λ-nat*sq p = flipSquare (compPath→Square (homotopyNatural Λ p))

  ρ-nat*sq : {X Y : El} (p : X ≡ Y) → Square (ρ X) (ρ Y) (ap (_⊗ 𝕀) p) p
  ρ-nat*sq p = flipSquare (compPath→Square (homotopyNatural ρ p))

  ⊗-bi : {X X' Y Y' : El} (p : X ≡ X') (q : Y ≡ Y')
    → Square (ap (_⊗ Y) p) (ap (_⊗ Y') p) (ap (X ⊗_) q) (ap (X' ⊗_) q)
  ⊗-bi p q i j = p j ⊗ q i

  α-nat : {X X' Y Y' Z Z' : El}
    (p : X ≡ X') (q : Y ≡ Y') (r : Z ≡ Z')
    → Square (α X Y Z) (α X' Y' Z') (ap₃ (λ X Y Z → (X ⊗ Y) ⊗ Z) p q r) (ap₃ (λ X Y Z → X ⊗ (Y ⊗ Z)) p q r)
  α-nat p q r i j = α (p i) (q i) (r i) j

  β-nat : {X X' Y Y' : El} (p : X ≡ X') (q : Y ≡ Y')
    → Square (β X Y) (β X' Y') (ap₂ _⊗_ p q) (ap₂ _⊗_ q p)
  β-nat p q i j = β (p i) (q i) j



 -- (homotopyNatural {f = {!λ X → 𝕀 ⊗ X!}} {g = λ X → X} {!!} {!!}) -- (homotopyNatural {f = λ X → 𝕀 ⊗ X} {g = λ X → X} Λ p)

open SMG*Sq public

record SMG*Fun*Sq {ℓ₁ ℓ₂}
  {A : Type ℓ₁} (A* : SMG*Sq A)
  {B : Type ℓ₂} (B* : SMG*Sq B)
  (f : A → B) : Type (ℓ-max ℓ₁ ℓ₂) where
  constructor smg*fun*sq
  private
    module A = SMG*Sq A*
    module B = SMG*Sq B*
  field
    -𝕀 : f A.𝕀 ≡ B.𝕀
    -⊗ : (X Y : A) → f (X A.⊗ Y) ≡ f X B.⊗ f Y
  field
    -α₌ : (X Y Z : A)
        → f (X A.⊗ Y) B.⊗ f Z ≡ f X B.⊗ f (Y A.⊗ Z)
    -α₁ : (X Y Z : A)
        → Square
            (ap f (A.α X Y Z))
            (-α₌ X Y Z)
            (-⊗ (X A.⊗ Y) Z)
            (-⊗ X (Y A.⊗ Z))
    -α₂ : (X Y Z : A)
        → Square
            (-α₌ X Y Z)
            (B.α (f X) (f Y) (f Z))
            (ap (B._⊗ f Z) (-⊗ X Y))
            (ap (f X B.⊗_) (-⊗ Y Z))

    -Λ : (X : A)
        → Square
            (-⊗ A.𝕀 X)
            (sym (B.Λ (f X)))
            (ap f (A.Λ X))
            (ap (B._⊗ f X) -𝕀)

    -ρ : (X : A)
        → Square
            (-⊗ X A.𝕀)
            (sym (B.ρ (f X)))
            (ap f (A.ρ X))
            (ap (f X B.⊗_) -𝕀)

    -β : (X Y : A) → Square (-⊗ X Y) (-⊗ Y X) (ap f (A.β X Y)) (B.β (f X) (f Y))


open SMG*Fun*Sq public

unquoteDecl SMG*Fun*SqIsoΣ = declareRecordIsoΣ SMG*Fun*SqIsoΣ (quote SMG*Fun*Sq)

private
  isSetSquareFromGroupoid : ∀ {ℓ} {X : Type ℓ}
    (X-is-groupoid : isGroupoid X)
    {x₀₀ x₀₁ x₁₀ x₁₁ : X}
    (x₀₋ : x₀₀ ≡ x₀₁)
    (x₁₋ : x₁₀ ≡ x₁₁)
    (x₋₀ : x₀₀ ≡ x₁₀)
    (x₋₁ : x₀₁ ≡ x₁₁)
    → isSet (Square x₀₋ x₁₋ x₋₀ x₋₁)
  isSetSquareFromGroupoid X-is-groupoid {x₁₀ = x₁₀} {x₁₁ = x₁₁} x₀₋ x₁₋ x₋₀ x₋₁ =
    isOfHLevelPathP 2 (X-is-groupoid x₁₀ x₁₁) x₀₋ x₁₋

SMG*Fun*Sq-isSet : ∀ {ℓ} {A : Type ℓ} {A* : SMG*Sq A} {B : Type ℓ} {B* : SMG*Sq B} (f : A → B)
    → isSet (SMG*Fun*Sq A* B* f)
SMG*Fun*Sq-isSet {B* = B*} f =
  let module B = SMG*Sq B* in
  isOfHLevelRetractFromIso 2 SMG*Fun*SqIsoΣ
    (isSetΣ (B.is-groupoid _ _) λ _ →
    isSetΣ (isSetΠ2 λ _ _ → B.is-groupoid _ _) λ _ →
    isSetΣ (isSetΠ3 λ _ _ _ → B.is-groupoid _ _) λ _ →
    isSetΣ (isSetΠ3 λ _ _ _ → isSetSquareFromGroupoid B.is-groupoid _ _ _ _) λ _ →
    isSetΣ (isSetΠ3 λ _ _ _ → isSetSquareFromGroupoid B.is-groupoid _ _ _ _) λ _ →
    isSetΣ (isSetΠ λ _ → isSetSquareFromGroupoid B.is-groupoid _ _ _ _) λ _ →
    isSetΣ (isSetΠ λ _ → isSetSquareFromGroupoid B.is-groupoid _ _ _ _) λ _ →
    isSetΠ2 λ _ _ → isSetSquareFromGroupoid B.is-groupoid _ _ _ _)

record SMG*Nat*Sq {ℓ}
  {A : Type ℓ} {A* : SMG*Sq A}
  {B : Type ℓ} {B* : SMG*Sq B}
  {f g : A → B}
  (f* : SMG*Fun*Sq A* B* f)
  (g* : SMG*Fun*Sq A* B* g)
  : Type ℓ where
  constructor smg*nat*sq
  private
    module A = SMG*Sq A*
    module B = SMG*Sq B*
    module f* = SMG*Fun*Sq f*
    module g* = SMG*Fun*Sq g*
  field
    nat : (X : A) → f X ≡ g X
    nat-𝕀 : Square (f* .-𝕀) (g* .-𝕀) (nat A.𝕀) refl
    nat-⊗ : (X Y : A) → Square (f* .-⊗ X Y) (g* .-⊗ X Y) (nat (X A.⊗ Y)) (ap₂ B._⊗_ (nat X) (nat Y))

module _ {ℓ}
  {A : Type ℓ} {A* : SMG*Sq A}
  {B : Type ℓ} {B* : SMG*Sq B}
  {f g : A → B}
  (f* : SMG*Fun*Sq A* B* f)
  (g* : SMG*Fun*Sq A* B* g)
  where

  private
    module A = SMG*Sq A*
    module B = SMG*Sq B*

  open SMG*Nat*Sq

  -- _⊗A_ = SMG*Sq._⊗_
  -- _⊗B_ = B*._⊗_

  -- lemma2 : (s : SMG*Nat*Sq f* g*) (i : I) (X : A) → Square (s .nat-⊗ A.𝕀 X i) (sym (B.Λ (nat s X i)))
  --        (ap (λ x → nat s x i) (A.Λ X)) (ap (B._⊗ nat s X i) (s .nat-𝕀 i))
  -- lemma2 s i X = {!!}
  --   -- isGroupoid→Cube
  --   -- {c₀₀₀ = f (A.𝕀 A.⊗ X)} {c₀₀₁ = g (A.𝕀 A.⊗ X)} {c₀₁₀ = f A.𝕀 B.⊗ f X} {c₀₁₁ = g A.𝕀 B.⊗ g X}
  --   --   {c₁₀₀ = f X} {c₁₀₁ = g X} {c₁₁₀ = B.𝕀 B.⊗ f X} {c₁₁₁ = B.𝕀 B.⊗ g X}
  --   -- {c₀₀₋ = s .nat (A.𝕀 A.⊗ X)} {c₀₁₋ = ap₂ B._⊗_ (s .nat A.𝕀) (s .nat X)}
  --   -- {c₀₋₀ = s .nat-⊗ A.𝕀 X i0} {c₀₋₁ = s .nat-⊗ A.𝕀 X i1}
  --   -- {c₁₀₋ = s .nat X} {c₁₁₋ = ap (B.𝕀 B.⊗_) (s .nat X)}
  --   -- {c₁₋₀ = sym (B.Λ (f X))} {c₁₋₁ = sym (B.Λ (g X))}
  --   -- {c₋₀₀ = ap f (A.Λ X)} {c₋₀₁ = ap g (A.Λ X)}
  --   -- {c₋₁₀ = ap (B._⊗ f X) (f* .-𝕀)} {c₋₁₁ = ap (B._⊗ g X) (g* .-𝕀)}
  --   --   (flipSquare (s .nat-⊗ A.𝕀 X)) {!!} {!!} {!!} {!!} {!!} B.is-groupoid i j k

  lemma : (s : SMG*Nat*Sq f* g*) → PathP (λ i → SMG*Fun*Sq A* B* (λ x → SMG*Nat*Sq.nat s x i)) f* g*
  -- lemma s i =
  --   smg*fun*sq (s .nat-𝕀 i) (λ X Y → s .nat-⊗ X Y i) {!!} {!!} {!!} {!!} {!!} {!!}

  lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .-𝕀 = nat-𝕀 i
  lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .-⊗ X Y = nat-⊗ X Y i
  lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .-α₌ X Y Z = {!!}
  lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .-α₁ X Y Z = {!!}
  lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .-α₂ = {!!}
  lemma (smg*nat*sq nat nat-𝕀 nat-⊗) k .-Λ X i j =
    isGroupoid→Cube
      {c₀₀₀ = f (A.𝕀 A.⊗ X)} {c₀₀₁ = g (A.𝕀 A.⊗ X)} {c₀₁₀ = f A.𝕀 B.⊗ f X} {c₀₁₁ = g A.𝕀 B.⊗ g X}
      {c₁₀₀ = f X} {c₁₀₁ = g X} {c₁₁₀ = B.𝕀 B.⊗ f X} {c₁₁₁ = B.𝕀 B.⊗ g X}
    {c₀₀₋ = nat (A.𝕀 A.⊗ X)} {c₀₁₋ = ap₂ B._⊗_ (nat A.𝕀) (nat X)}
    {c₀₋₀ = nat-⊗ A.𝕀 X i0} {c₀₋₁ = nat-⊗ A.𝕀 X i1}
    {c₁₀₋ = nat X} {c₁₁₋ = ap (B.𝕀 B.⊗_) (nat X)}
    {c₁₋₀ = sym (B.Λ (f X))} {c₁₋₁ = sym (B.Λ (g X))}
    {c₋₀₀ = ap f (A.Λ X)} {c₋₀₁ = ap g (A.Λ X)}
    {c₋₁₀ = ap (B._⊗ f X) (f* .-𝕀)} {c₋₁₁ = ap (B._⊗ g X) (g* .-𝕀)}
      (flipSquare (nat-⊗ A.𝕀 X))
      {!!} -- (let q = B.Λ-nat*sq (nat X) in flipSquare (invSquarev {!q!}))
      {!!}
      {!!}
      (f* .-Λ X)
      (g* .-Λ X)
      (B* .is-groupoid) i j k
  lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .-ρ = {!!}
  lemma (smg*nat*sq nat nat-𝕀 nat-⊗) i .-β = {!!}

  -- (c₀₋₋ : Square c₀₀₋ c₀₁₋ c₀₋₀ c₀₋₁)
  -- (c₁₋₋ : Square c₁₀₋ c₁₁₋ c₁₋₀ c₁₋₁)
  -- (c₋₀₋ : Square c₀₀₋ c₁₀₋ c₋₀₀ c₋₀₁)
  -- (c₋₁₋ : Square c₀₁₋ c₁₁₋ c₋₁₀ c₋₁₁)
  -- (c₋₋₀ : Square c₀₋₀ c₁₋₀ c₋₀₀ c₋₁₀)
  -- (c₋₋₁ : Square c₀₋₁ c₁₋₁ c₋₀₁ c₋₁₁)

  -- SMG*Fun*Sq≡ : SMG*Nat*Sq f* g* → (f , f*) ≡ (g , g*)
  -- SMG*Fun*Sq≡ (smg*nat*sq nat nat-𝕀 nat-⊗) =
  --   ΣPathP (
  --     funExt nat ,
  --     {!!}
  --     -- λ i → smg*fun*sq (nat-𝕀 i) (λ X Y → nat-⊗ X Y i)
  --     -- (λ X Y Z → {!!}) {!!} {!!} {!!} {!!} {!!}
  --   )

-- Goal: Square (nat-⊗ (𝕀 A*) X i) (sym (Λ B* (nat X i)))
--       (ap (λ x → nat x i) (Λ A* X))
--       (ap (λ section₁ → (B* ⊗ section₁) (nat X i)) (nat-𝕀 i))
-- ———— Boundary (wanted) —————————————————————————————————————
-- i = i0 ⊢ -Λ f* X
-- i = i1 ⊢ -Λ g* X
-- ————————————————————————————————————————————————————————————
-- X     : A
-- i     : I
-- nat-⊗ : (X₁ Y : A) →
--         Square (-⊗ f* X₁ Y) (-⊗ g* X₁ Y) (nat ((A* ⊗ X₁) Y))
--         (ap₂ (_⊗_ B*) (nat X₁) (nat Y))
-- nat-𝕀 : Square (-𝕀 f*) (-𝕀 g*) (nat (𝕀 A*)) refl
-- nat   : (X₁ : A) → f X₁ ≡ g X₁
-- g*    : SMG*Fun*Sq A* B* g
-- f*    : SMG*Fun*Sq A* B* f
-- g     : A → B
-- f     : A → B
-- B*    : SMG*Sq B
-- B     : Type ℓ
-- A*    : SMG*Sq A
-- A     : Type ℓ
-- ℓ     : Level
