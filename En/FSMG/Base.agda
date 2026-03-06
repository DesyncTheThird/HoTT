module En.FSMG.Base where

open import En.Prelude

data FSMG {ℓ} (A : Type ℓ) : Type ℓ where
    𝕀 : FSMG A
    η : A → FSMG A
    _⊗_ : FSMG A → FSMG A → FSMG A

    α : (X Y Z : FSMG A) → (X ⊗ Y) ⊗ Z ≡ X ⊗ (Y ⊗ Z)
    Λ : (X : FSMG A) → 𝕀 ⊗ X ≡ X
    ρ : (X : FSMG A) → X ⊗ 𝕀 ≡ X
    β : (X Y : FSMG A) → X ⊗ Y ≡ Y ⊗ X

    ▽ : (X Y : FSMG A)
        → Square (ap (X ⊗_) (Λ Y)) (ap (_⊗ Y) (ρ X)) (sym (α X 𝕀 Y)) refl

    -- ▽ : (X Y : FSMG)
    --     → α (X) (𝕀) (Y) ∙ ap (X ⊗_) (Λ (Y)) ≡ ap (_⊗ Y) (ρ (X))

    ⬠₌ : (W X Y Z : FSMG A)
        → ((W ⊗ X) ⊗ Y) ⊗ Z ≡ W ⊗ (X ⊗ (Y ⊗ Z))
    ⬠₁ : (W X Y Z : FSMG A)
        → Square (sym (α (W ⊗ X) Y Z)) (α W X (Y ⊗ Z)) refl (⬠₌ W X Y Z)
    ⬠₂ : (W X Y Z : FSMG A)
        → Square (ap (_⊗ Z) (α W X Y)) (sym (ap (W ⊗_) (α X Y Z))) (⬠₌ W X Y Z) (α W (X ⊗ Y) Z)

    -- ⬠ : (W X Y Z : FSMG)
    --   → α (W ⊗ X) Y Z ∙ α W X (Y ⊗ Z)
    --   ≡ ap (_⊗ Z) (α W X Y) ∙ α W (X ⊗ Y) Z ∙ ap (W ⊗_) (α X Y Z)


    ⬡₌ : (X Y Z : FSMG A)
        → (X ⊗ Y) ⊗ Z ≡ Y ⊗ (Z ⊗ X)
    ⬡₁ : (X Y Z : FSMG A)
        → Square (sym (α X Y Z)) (α Y Z X) (β X (Y ⊗ Z)) (⬡₌ X Y Z)
    ⬡₂ : (X Y Z : FSMG A)
        → Square (ap (_⊗ Z) (β X Y)) (ap (Y ⊗_) (sym (β X Z))) (⬡₌ X Y Z) (α Y X Z)

    -- ⬡ : (X Y Z : FSMG A)
    --     → α (X) (Y) (Z) ∙ β (X) (Y ⊗ Z) ∙ α (Y) (Z) (X)
    --     ≡ ap (_⊗ Z) (β (X) (Y)) ∙ α (Y) (X) (Z) ∙ ap (Y ⊗_) (β (X) (Z))

    β² : (X Y : FSMG A) → β X Y ≡ sym (β Y X)

    is-groupoid : isGroupoid (FSMG A)

module FSMG*Elim {ℓ ℓ'} (A : Type ℓ) {P : FSMG A → Type ℓ'}
    (η* : (a : A) → P (η a))
    (𝕀* : P 𝕀)
    (_⊗*_ : {X Y : FSMG A} (X* : P X) → (Y* : P Y) → (P (X ⊗ Y)))

    (α* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → PathP (λ i → P (α X Y Z i)) ((X* ⊗* Y*) ⊗* Z*) (X* ⊗* (Y* ⊗* Z*)))

    (Λ* : {X : FSMG A} (X* : P X) → PathP (λ i → P (Λ X i)) (𝕀* ⊗* X*) X*)
    (ρ* : {X : FSMG A} (X* : P X) → PathP (λ i → P (ρ X i)) (X* ⊗* 𝕀*) X*)
    (β* : {X Y : FSMG A} (X* : P X) (Y* : P Y)
        → PathP (λ i → P (β X Y i)) (X* ⊗* Y*) (Y* ⊗* X*))

    (▽* : {X Y : FSMG A} (X* : P X) (Y* : P Y)
        → SquareP (λ i j → P (▽ X Y i j)) (apP (λ i a → X* ⊗* a) (Λ* Y*)) (apP (λ i a → a ⊗* Y*) (ρ* X*)) (symP (α* X* 𝕀* Y*)) refl)

    (⬠₌* : {W X Y Z : FSMG A} (W* : P W) (X* : P X) (Y* : P Y) (Z* : P Z)
        → PathP (λ i → P (⬠₌ W X Y Z i)) (((W* ⊗* X*) ⊗* Y*) ⊗* Z*) (W* ⊗* (X* ⊗* (Y* ⊗* Z*))))
    (⬠₁* : {W X Y Z : FSMG A} (W* : P W) (X* : P X) (Y* : P Y) (Z* : P Z)
        → SquareP (λ i j → P (⬠₁ W X Y Z i j))
            (symP (α* (W* ⊗* X*) Y* Z*))
            (α* W* X* (Y* ⊗* Z*))
            refl
            (⬠₌* W* X* Y* Z*))
    (⬠₂* : {W X Y Z : FSMG A} (W* : P W) (X* : P X) (Y* : P Y) (Z* : P Z)
        → SquareP (λ i j → P (⬠₂ W X Y Z i j))
            (apP (λ i a → a ⊗* Z*) (α* W* X* Y*))
            (symP (apP (λ i a → W* ⊗* a) (α* X* Y* Z*)))
            (⬠₌* W* X* Y* Z*)
            (α* W* (X* ⊗* Y*) Z*))

    (⬡₌* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → PathP (λ i → P (⬡₌ X Y Z i)) ((X* ⊗* Y*) ⊗* Z*) (Y* ⊗* (Z* ⊗* X*)))

    (⬡₁* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → SquareP (λ i j → P (⬡₁ X Y Z i j)) (symP (α* X* Y* Z*)) (α* Y* Z* X*) (β* X* (Y* ⊗* Z*)) (⬡₌* X* Y* Z*))
    (⬡₂* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → SquareP (λ i j → P (⬡₂ X Y Z i j)) (apP (λ i a → a ⊗* Z*) (β* X* Y*)) (apP (λ i a → Y* ⊗* a) (symP (β* X* Z*))) (⬡₌* X* Y* Z*) (α* Y* X* Z*))

    (β²* : {X Y : FSMG A} (X* : P X) (Y* : P Y) → SquareP (λ i j → P (β² X Y i j)) (β* X* Y*) (symP (β* Y* X*)) refl refl)

    (is-groupoid* : (X : FSMG A) → isGroupoid (P X))

    where
    elim : (xs : FSMG A) → P xs
    elim 𝕀 = 𝕀*
    elim (η x) = η* x
    elim (X ⊗ Y) = elim X ⊗* elim Y
    elim (α X Y Z i) = α* (elim X) (elim Y) (elim Z) i
    elim (Λ X i) = Λ* (elim X) i
    elim (ρ X i) = ρ* (elim X) i
    elim (β X Y i) = β* (elim X) (elim Y) i
    elim (▽ X Y i j) = ▽* (elim X) (elim Y) i j
    elim (⬠₌ W X Y Z i) = ⬠₌* (elim W) (elim X) (elim Y) (elim Z) i
    elim (⬠₁ W X Y Z i j) = ⬠₁* (elim W) (elim X) (elim Y) (elim Z) i j
    elim (⬠₂ W X Y Z i j) = ⬠₂* (elim W) (elim X) (elim Y) (elim Z) i j
    elim (⬡₌ X Y Z i) = ⬡₌* (elim X) (elim Y) (elim Z) i
    elim (⬡₁ X Y Z i j) = ⬡₁* (elim X) (elim Y) (elim Z) i j
    elim (⬡₂ X Y Z i j) = ⬡₂* (elim X) (elim Y) (elim Z) i j
    elim (β² X Y i j) = β²* (elim X) (elim Y) i j
    elim (is-groupoid X Y p q r s i j k) = isGroupoid→CubeP (λ i j k → P (is-groupoid X Y p q r s i j k))
        (λ j k → elim (r j k)) (λ j k → elim (s j k)) (λ i k → elim (p k)) (λ i k → elim (q k)) (λ i j → elim X) (λ i j → elim Y) (is-groupoid* Y) i j k

module FSMG*Rec {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'}
    (η* : (a : A) → B)
    (𝕀* : B)
    (_⊗*_ : B → B → B)

    (α* : (X* Y* Z* : B) → (X* ⊗* Y*) ⊗* Z* ≡ X* ⊗* (Y* ⊗* Z*))

    (Λ* : (X* : B) → 𝕀* ⊗* X* ≡ X*)
    (ρ* : (X* : B) → X* ⊗* 𝕀* ≡ X*)
    (β* : (X* Y* : B) → X* ⊗* Y* ≡ Y* ⊗* X*)

    (▽* : (X* Y* : B)
        → Square (ap (X* ⊗*_) (Λ* Y*)) (ap (_⊗* Y*) (ρ* X*)) (sym (α* X* 𝕀* Y*)) refl)

    (⬠₌* : (W* X* Y* Z* : B)
        → ((W* ⊗* X*) ⊗* Y*) ⊗* Z* ≡ W* ⊗* (X* ⊗* (Y* ⊗* Z*)))
    (⬠₁* : (W* X* Y* Z* : B)
        → Square (sym (α* (W* ⊗* X*) Y* Z*)) (α* W* X* (Y* ⊗* Z*)) refl (⬠₌* W* X* Y* Z*))
    (⬠₂* : (W* X* Y* Z* : B)
        → Square (ap (_⊗* Z*) (α* W* X* Y*)) (sym (ap (W* ⊗*_) (α* X* Y* Z*))) (⬠₌* W* X* Y* Z*) (α* W* (X* ⊗* Y*) Z*))

    (⬡₌* : (X* Y* Z* : B)
        → (X* ⊗* Y*) ⊗* Z* ≡ Y* ⊗* (Z* ⊗* X*))
    (⬡₁* : (X* Y* Z* : B)
        → Square (sym (α* X* Y* Z*)) (α* Y* Z* X*) (β* X* (Y* ⊗* Z*)) (⬡₌* X* Y* Z*))
    (⬡₂* : (X* Y* Z* : B)
        → Square (ap (_⊗* Z*) (β* X* Y*)) (ap (Y* ⊗*_) (sym (β* X* Z*))) (⬡₌* X* Y* Z*) (α* Y* X* Z*))

    (β²* : (X* Y* : B) → Square (β* X* Y*) (sym (β* Y* X*)) refl refl)

    (is-groupoid* : isGroupoid B)

    where

    private
      module Elim = FSMG*Elim A {P = λ _ → B}
        η* 𝕀* (λ x y → x ⊗* y) α* Λ* ρ* β* ▽* ⬠₌* ⬠₁* ⬠₂* ⬡₌* ⬡₁* ⬡₂* β²*
        (λ _ → is-groupoid*)

    rec : FSMG A → B
    rec = Elim.elim


module FSMG*Elim*Set {ℓ ℓ'} (A : Type ℓ) {P : FSMG A → Type ℓ'}
    (η* : (a : A) → P (η a))
    (𝕀* : P 𝕀)
    (_⊗*_ : {X Y : FSMG A} (X* : P X) → (Y* : P Y) → (P (X ⊗ Y)))

    (α* : {X Y Z : FSMG A} (X* : P X) (Y* : P Y) (Z* : P Z)
        → PathP (λ i → P (α X Y Z i)) ((X* ⊗* Y*) ⊗* Z*) (X* ⊗* (Y* ⊗* Z*)))

    (Λ* : {X : FSMG A} (X* : P X) → PathP (λ i → P (Λ X i)) (𝕀* ⊗* X*) X*)
    (ρ* : {X : FSMG A} (X* : P X) → PathP (λ i → P (ρ X i)) (X* ⊗* 𝕀*) X*)
    (β* : {X Y : FSMG A} (X* : P X) (Y* : P Y)
        → PathP (λ i → P (β X Y i)) (X* ⊗* Y*) (Y* ⊗* X*))

    (is-set* : (X : FSMG A) → isSet (P X))

    where

--     -- private
--     --   module Elim = FSMG*Elim A {P = P}
--     --     η* 𝕀* (λ x y → x ⊗* y) α* Λ* ρ* β*
--     --     (λ {X = X} {Y = Y} X* Y* → isSet→SquareP (λ i j → is-set* (▽ X Y i j)) (apP (λ i → X* ⊗*_) (Λ* Y*)) (apP (λ i → _⊗* Y*) (ρ* X*)) (symP (α* X* 𝕀* Y*)) refl)
--     --     (λ {W = W} {X = X} {Y = Y} {Z = Z} W* X* Y* Z* →
--     --       {!!}
--     --     )
--     --     (λ {W = W} {X = X} {Y = Y} {Z = Z} W* X* Y* Z* → isSet→SquareP (λ i j → is-set* (⬠₁ W X Y Z i j)) _ _ _ _)
--     --     (λ {W = W} {X = X} {Y = Y} {Z = Z} W* X* Y* Z* → isSet→SquareP (λ i j → is-set* (⬠₂ W X Y Z i j)) _ _ _ _)
--     --     {!!}
--     --     (λ {X = X} {Y = Y} {Z = Z} X* Y* Z* → isSet→SquareP (λ i j → is-set* (⬡₁ X Y Z i j)) _ _ _ _)
--     --     (λ {X = X} {Y = Y} {Z = Z} X* Y* Z* → isSet→SquareP (λ i j → is-set* (⬡₂ X Y Z i j)) _ _ _ _)

    private
      ⬠₌* : {W X Y Z : FSMG A} (W* : P W) (X* : P X) (Y* : P Y) (Z* : P Z)
          → PathP (λ i → P (⬠₌ W X Y Z i)) (((W* ⊗* X*) ⊗* Y*) ⊗* Z*) (W* ⊗* (X* ⊗* (Y* ⊗* Z*)))
      ⬠₌* {W = W} {X = X} {Y = Y} {Z = Z} W* X* Y* Z* i =
        {!!}
        -- compPathP' {B = {!!}}
        --   {x' = ((W* ⊗* X*) ⊗* Y*) ⊗* Z*} {y' = (W* ⊗* X*) ⊗* (Y* ⊗* Z*)} {z' = W* ⊗* (X* ⊗* (Y* ⊗* Z*))}
        --   {p = α (W ⊗ X) Y Z} {q = α W X (Y ⊗ Z)}
        --   (α* (W* ⊗* X*) Y* Z*) (α* W* X* (Y* ⊗* Z*))

    elim : (xs : FSMG A) → P xs
    elim 𝕀 = 𝕀*
    elim (η x) = η* x
    elim (X ⊗ Y) = elim X ⊗* elim Y
    elim (α X Y Z i) = α* (elim X) (elim Y) (elim Z) i
    elim (Λ X i) = Λ* (elim X) i
    elim (ρ X i) = ρ* (elim X) i
    elim (β X Y i) = β* (elim X) (elim Y) i
    elim (▽ X Y i j) =
      isSet→SquareP (λ i j → is-set* (▽ X Y i j))
        (apP (λ i → elim X ⊗*_) (Λ* (elim Y)))
        (apP (λ i → _⊗* (elim Y)) (ρ* (elim X)))
        (symP (α* (elim X) 𝕀* (elim Y)))
        refl i j
    elim (⬠₌ W X Y Z i) =
      {!!}

    elim (⬠₁ W X Y Z i j) =
      isSet→SquareP (λ i j → is-set* (⬠₁ W X Y Z i j))
        (symP (α* (elim W ⊗* elim X) (elim Y) (elim Z)))
        (α* (elim W) (elim X) (elim Y ⊗* elim Z))
        refl
        {!!} i j -- ⬠₁* (elim W) (elim X) (elim Y) (elim Z) i j
    elim (⬠₂ W X Y Z i j) = {!!} -- ⬠₂* (elim W) (elim X) (elim Y) (elim Z) i j
    elim (⬡₌ X Y Z i) = {!!} -- ⬡₌* (elim X) (elim Y) (elim Z) i
    elim (⬡₁ X Y Z i j) = {!!} -- ⬡₁* (elim X) (elim Y) (elim Z) i j
    elim (⬡₂ X Y Z i j) = {!!} -- ⬡₂* (elim X) (elim Y) (elim Z) i j
    elim (β² X Y i j) = {!!} -- β²* (elim X) (elim Y) i j
    elim (is-groupoid X Y p q r s i j k) = {!!}

-- isGroupoid→CubeP (λ i j k → P (is-groupoid X Y p q r s i j k))
--         (λ j k → elim (r j k)) (λ j k → elim (s j k)) (λ i k → elim (p k)) (λ i k → elim (q k)) (λ i j → elim X) (λ i j → elim Y) (is-groupoid* Y) i j k

module FSMG*Rec*Set {ℓ ℓ'} (A : Type ℓ) {P : Type ℓ'}
    (η* : (a : A) → P)
    (𝕀* : P)
    (_⊗*_ : (X* : P) → (Y* : P) → P)

    (α* : (X* : P) (Y* : P) (Z* : P)
        → Path P ((X* ⊗* Y*) ⊗* Z*) (X* ⊗* (Y* ⊗* Z*)))

    (Λ* : (X* : P) → Path P (𝕀* ⊗* X*) X*)
    (ρ* : (X* : P) → Path P (X* ⊗* 𝕀*) X*)
    (β* : (X* : P) (Y* : P)
        → Path P (X* ⊗* Y*) (Y* ⊗* X*))

    (is-set* : isSet P)
    where

    private
      ⬠₌* : (W* X* Y* Z* : P)
          → ((W* ⊗* X*) ⊗* Y*) ⊗* Z* ≡ W* ⊗* (X* ⊗* (Y* ⊗* Z*))
      ⬠₌* W* X* Y* Z* i = hcomp (λ j → λ { (i = i0) → α* (W* ⊗* X*) (Y*) (Z*) (~ j)
                                     ; (i = i1) → α* (W*) (X*) (Y* ⊗* Z*) j })
                            ((W* ⊗* X*) ⊗* (Y* ⊗* Z*))


    rec : FSMG A → P
    rec 𝕀 = 𝕀*
    rec (η x) = η* x
    rec (X ⊗ Y) = rec X ⊗* rec Y
    rec (α X Y Z i) = α* (rec X) (rec Y) (rec Z) i
    rec (Λ X i) = Λ* (rec X) i
    rec (ρ X i) = ρ* (rec X) i
    rec (β X Y i) = β* (rec X) (rec Y) i
    rec (▽ X Y i j) =
      isSet→Square is-set*
        (rec X ⊗* (𝕀* ⊗* rec Y))
        (rec X ⊗* rec Y)
        (ap (rec X ⊗*_) (Λ* (rec Y)))
        ((rec X ⊗* 𝕀*) ⊗* rec Y)
        (rec X ⊗* rec Y)
        (ap (_⊗* (rec Y)) (ρ* (rec X)))
        (sym (α* (rec X) 𝕀* (rec Y)))
        refl
        i j
    rec (⬠₌ W X Y Z i) =
      ⬠₌* (rec W) (rec X) (rec Y) (rec Z) i
    rec (⬠₁ W X Y Z i j) =
      isSet→Square is-set*
        ((rec W ⊗* rec X) ⊗* (rec Y ⊗* rec Z))
        (((rec W ⊗* rec X) ⊗* rec Y) ⊗* rec Z)
        (sym (α* (rec W ⊗* rec X) (rec Y) (rec Z)))
        ((rec W ⊗* rec X) ⊗* (rec Y ⊗* rec Z))
        (rec W ⊗* (rec X ⊗* (rec Y ⊗* rec Z)))
        (α* (rec W) (rec X) (rec Y ⊗* rec Z))
        refl
        (⬠₌* (rec W) (rec X) (rec Y) (rec Z))
        i j
    rec (⬠₂ W X Y Z i j) = {!!}
    rec (⬡₌ X Y Z i) = {!!}
    rec (⬡₁ X Y Z i j) = {!!}
    rec (⬡₂ X Y Z i j) = {!!}
    rec (β² X Y i j) = {!!}
    rec (is-groupoid X Y p q r s i j k) = {!!}

-- (apP (λ i → X* ⊗*_) (Λ* Y*)) (apP (λ i → _⊗* Y*) (ρ* X*)) (symP (α* X* 𝕀* Y*)) refl)

-- j = i0 ⊢ α* (rec X) 𝕀* (rec Y) (~ i)
-- j = i1 ⊢ rec X ⊗* rec Y
-- i = i0 ⊢ rec X ⊗* Λ* (rec Y) j
-- i = i1 ⊢ ρ* (rec X) j ⊗* rec Y

-- (a₀₀ : A) (a₀₁ : A) (a₀₋ : PathP (λ j → A) a₀₀ a₀₁)
-- (a₁₀ : A) (a₁₁ : A) (a₁₋ : PathP (λ j → A) a₁₀ a₁₁)
-- (a₋₀ : PathP (λ i → A) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A) a₀₁ a₁₁)
