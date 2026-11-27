{-# OPTIONS --lossy-unification #-}

module En.SList.2Cells where

open import En.Prelude
open import En.SList.0Cells
open import En.SList.1Cells
open import En.SList.Base
import En.SMG as S hiding (SMG* ; SMG*Fun)

private
  variable
    A : Type ℓ

module _ (X Y : SList A) where
  opaque
    unfolding ++-Λ ++-ρ ++-α ++-::

    ++-▽ : Square
          (ap (X ++_) (++-Λ Y))
          (ap (_++ Y) (++-ρ X))
          (sym (++-α X nil Y))
          refl
    ++-▽ =
      SListElimProp.elim
      (λ X →
        Square
          (ap (X ++_) (++-Λ Y))
          (ap (_++ Y) (++-ρ X))
          (sym (++-α X nil Y))
          refl
      )
      refl
      (λ x {xs} P i j → x :: P i j)
      (λ X → isOfHLevelPathP' 1 (is-groupoid ((X ++ nil) ++ Y) (X ++ Y)) (ap (X ++_) (++-Λ Y)) (ap (_++ Y) (++-ρ X)))
      X


module _ (W X Y Z : SList A) where
  opaque
    ++-⬠₌ : ((W ++ X) ++ Y) ++ Z ≡ W ++ X ++ Y ++ Z
    ++-⬠₌ =
      -- ++-α (W ++ X) Y Z ∙ ++-α W X (Y ++ Z)
      SListElimSet.elim
        (λ W → ((W ++ X) ++ Y) ++ Z ≡ W ++ X ++ Y ++ Z)
        (++-α X Y Z)
        (λ x {xs} P i → x :: P i)
        (λ x y {xs} P → flipSquare (homotopyNaturalSq (swap x y) P))
        (λ xs → isOfHLevelPathP' 2 is-groupoid _ _)
        W

module _ (W X Y Z : SList A) where
  opaque
    unfolding ++-⬠₌ ++-:: ++-α
    ++-⬠₁ : Square
            (sym (++-α (W ++ X) Y Z))
            (++-α W X (Y ++ Z))
            refl
            (++-⬠₌ W X Y Z)
    -- ++-⬠₁ =
    --   SListElimProp.elim
    --     (λ W →
    --       Square
    --       (sym (++-α (W ++ X) Y Z))
    --       (++-α W X (Y ++ Z))
    --       refl
    --       (++-⬠₌ W X Y Z)
    --     )
    --     {!λ i j → ++-α X Y Z (i ∨ ~ j)!}
    --     (λ x {xs} P i j → {!!})
    --     {!!}
    --     W

    ++-⬠₁ =
      SListElimProp.elim
      (λ W →
        Square
        (sym (++-α (W ++ X) Y Z))
        (++-α W X (Y ++ Z))
        refl
        (++-⬠₌ W X Y Z)
        )
      (λ i j → ++-α X Y Z (i ∨ ~ j))
      (λ x {xs} P i j → x :: P i j)
      (λ xs → isOfHLevelPathP' 1 (is-groupoid ((xs ++ X) ++ Y ++ Z) (xs ++ X ++ Y ++ Z)) (sym (++-α (xs ++ X) Y Z)) (++-α xs X (Y ++ Z)))
      W

    ++-⬠₂ : Square
            (ap (_++ Z) (++-α W X Y))
            (sym (ap (_++_ W) (++-α X Y Z)))
            (++-⬠₌ W X Y Z) (++-α W (X ++ Y) Z)
    ++-⬠₂ =
      SListElimProp.elim
        (λ W →
          Square
          (ap (_++ Z) (++-α W X Y))
          (sym (ap (_++_ W) (++-α X Y Z)))
          (++-⬠₌ W X Y Z)
          (++-α W (X ++ Y) Z)
        )
        (λ i j → ++-α X Y Z (i ∧ ~ j))
        (λ x {xs} P i j → x :: P i j)
        (λ xs → isOfHLevelPathP' 1 (is-groupoid (xs ++ X ++ Y ++ Z) (xs ++ (X ++ Y) ++ Z)) _ _)
        W




module _ (X Y Z : SList A) where
  opaque
    unfolding ++-:: ++-α ++-Λ ++-ρ
    ++-⬡₌ : (X ++ Y) ++ Z ≡ Y ++ (Z ++ X)
    ++-⬡₌ = ++-α X Y Z ∙ ++-β X (Y ++ Z) ∙ ++-α Y Z X

    -- ++-⬡₌ (x :: xs) Y Z
    -- x :: ++-α X Y Z ∙ x :: ++-β X (Y ++ Z) ∙ x :: ++-α Y Z X
    -- ++-α x :: X Y Z ∙ x :: ++-β X (Y ++ Z) ∙ ++-α Y Z X








module _ (x : A) (xs ys Z : SList A) where
  opaque
    unfolding ++-α -- ++-:: -- ++-β ++-ρ

    up : Square
         (ap (_++ Z) (++-:: x ys xs))
         (++-:: x ys (xs ++ Z))
         (ap (x ::_) (++-α ys xs Z))
         (++-α ys (x :: xs) Z)
    up = SListElimProp.elim
         (λ Y → Square
                (ap (_++ Z) (++-:: x Y xs))
                (++-:: x Y (xs ++ Z))
                (ap (x ::_) (++-α Y xs Z))
                (++-α Y (x :: xs) Z)
         )
         (compPath→Square
            (rUnit _ ∙
             sym (assoc _ _ _) ∙
             sym (lUnit _) ∙
             ap (_∙ refl) (++-::-nil x (xs ++ Z) ∙ sym (ap (ap (_++ Z)) (++-::-nil x xs)))))
         (λ y {ys} Q → sorry) -- TODO: big square
         (λ ys → isOfHLevelPathP' 1 (is-groupoid (x :: ys ++ xs ++ Z) (ys ++ (x :: xs) ++ Z )) (ap (_++ Z) (++-:: x ys xs)) (++-:: x ys (xs ++ Z)))
         ys

      -- compPath→Square (
      -- ap (x ::_) (++-α Y xs Z) ∙ ++-:: x Y (xs ++ Z)
      --   ≡⟨ sym (homotopyNatural {!!} {!!}) ⟩
      -- ap (_++ Z) (++-:: x Y xs) ∙ ++-α Y (x :: xs) Z
      -- ∎
      -- )

-- homotopyNatural : {B : Type ℓ'} {f g : A → B} (H : ∀ a → f a ≡ g a) {x y : A} (p : x ≡ y) →
--                   H x ∙ cong g p ≡ cong f p ∙ H y




module _ (x : A) (xs Y Z : SList A) where

  opaque
    unfolding ++-α ++-β -- ++-⬡₌ ++-α ++-:: ++-β ++-ρ
    down : Square
           refl
           ((++-:: x Y (Z ++ xs) ∙ ap (Y ++_) (++-:: x Z xs)))
           (ap (x ::_) (++-⬡₌ xs Y Z))
           (++-⬡₌ (x :: xs) Y Z)
    down = let
           P : Square
               refl
               refl
               (ap (x ::_) (++-α xs Y Z))
               (++-α (x :: xs) Y Z)
           P j k = ++-α (x :: xs) Y Z j
           Q : Square
               refl
               (++-:: x (Y ++ Z) xs)
               (ap (x ::_) (++-β xs (Y ++ Z)))
               (++-β (x :: xs) (Y ++ Z))
           Q = compPath→Square (
                 ap (x ::_) (++-β xs (Y ++ Z)) ∙ ++-:: x (Y ++ Z) xs
                 ≡⟨ refl ⟩
                 ++-β (x :: xs) (Y ++ Z)
                 ≡⟨ lUnit (++-β (x :: xs) (Y ++ Z)) ⟩
                 refl ∙ ++-β (x :: xs) (Y ++ Z)
                 ∎
               )
           R : Square
               (++-:: x (Y ++ Z) xs)
               (++-:: x Y (Z ++ xs) ∙ ap (Y ++_) (++-:: x Z xs))
               (++-α (x :: Y) Z xs)
               (++-α Y Z (x :: xs))
           R = {!!}

               --  compPath→Square (
               --   ++-α (x :: Y) Z xs ∙ ++-:: x Y (Z ++ xs) ∙ ap (Y ++_) (++-:: x Z xs)
               --   ≡⟨ {!!} ⟩
               --   {!!}
               --   ≡⟨ {!!} ⟩
               --   ++-:: x (Y ++ Z) xs ∙ ++-α Y Z (x :: xs)
               --   ∎
               -- )
         in {!!}

  opaque
    unfolding ++-β
    left : Square
           refl
           (ap (_++ Z) (++-:: x Y xs))
           (ap (x ::_) (ap (_++ Z) (++-β xs Y)))
           (ap (_++ Z) (++-β (x :: xs) Y))
    left = compPath→Square (
           ap (x ::_) (ap (_++ Z) (++-β xs Y)) ∙ ap (_++ Z) (++-:: x Y xs)
             ≡⟨ refl ⟩
           ap (_++ Z) (ap (x ::_) (++-β xs Y)) ∙ ap (_++ Z) (++-:: x Y xs)
             ≡⟨ sym (ap-∙ (_++ Z) (ap (x ::_) (++-β xs Y)) (++-:: x Y xs)) ⟩
           ap (_++ Z) (ap (x ::_) (++-β xs Y) ∙ ++-:: x Y xs)
             ≡⟨ refl ⟩
           ap (_++ Z) (++-β (x :: xs) Y)
             ≡⟨ lUnit (ap (_++ Z) (++-β (x :: xs) Y)) ⟩
           refl ∙ (ap (_++ Z) (++-β (x :: xs) Y))
           ∎
           )

  opaque
    unfolding ++-β

    right : Square
            (++-:: x Y (Z ++ xs) ∙ (ap (Y ++_) (++-:: x Z xs)))
            (++-:: x Y (xs ++ Z))
            (ap (x ::_) (ap (Y ++_) (sym (++-β xs Z))))
            (ap (Y ++_) (sym (++-β (x :: xs) Z)))
    right = compPath→Square (
            ap (x ::_) (ap (Y ++_) (sym (++-β xs Z))) ∙ (++-:: x Y (xs ++ Z))
              ≡⟨ sym (homotopyNatural (++-:: x Y) (sym (++-β xs Z))) ⟩
            ++-:: x Y (Z ++ xs) ∙ ap (Y ++_) (ap (x ::_) (sym (++-β xs Z)))
              ≡⟨ refl ⟩
            ++-:: x Y (Z ++ xs) ∙ ap (Y ++_) (sym (ap (x ::_) (++-β xs Z)))
              ≡⟨ ap (λ a → ++-:: x Y (Z ++ xs) ∙ ap (Y ++_) a) (rUnit (ap (x ::_) (sym (++-β xs Z)))) ⟩
            ++-:: x Y (Z ++ xs) ∙ ap (Y ++_) (sym (ap (x ::_) (++-β xs Z) ∙ refl))
              ≡⟨ ap (λ a → ++-:: x Y (Z ++ xs) ∙ ap (Y ++_) (sym (ap (x ::_) (++-β xs Z) ∙ a))) (sym (rCancel (++-:: x Z xs))) ⟩
            ++-:: x Y (Z ++ xs) ∙ ap (Y ++_) (sym (ap (x ::_) (++-β xs Z) ∙ ++-:: x Z xs ∙ sym (++-:: x Z xs)))
              ≡⟨ ap (λ a → ++-:: x Y (Z ++ xs) ∙ ap (Y ++_) (sym a)) (assoc (ap (x ::_) (++-β xs Z)) (++-:: x Z xs) (sym (++-:: x Z xs))) ⟩
            ++-:: x Y (Z ++ xs) ∙ ap (Y ++_) (sym ((ap (x ::_) (++-β xs Z) ∙ ++-:: x Z xs) ∙ sym (++-:: x Z xs)))
              ≡⟨ refl ⟩
            ++-:: x Y (Z ++ xs) ∙ ap (Y ++_) (sym (++-β (x :: xs) Z ∙ sym (++-:: x Z xs)))
              ≡⟨ ap (λ a → ++-:: x Y (Z ++ xs) ∙ ap (Y ++_) a) (sym-∙ (++-β (x :: xs) Z) (sym (++-:: x Z xs))) ⟩
            ++-:: x Y (Z ++ xs) ∙ ap (Y ++_) ((++-:: x Z xs) ∙ (sym (++-β (x :: xs) Z)))
              ≡⟨ ap (++-:: x Y (Z ++ xs) ∙_) (ap-∙ (Y ++_) _ _) ⟩
            ++-:: x Y (Z ++ xs) ∙ (ap (Y ++_) (++-:: x Z xs)) ∙ ap (Y ++_) (sym (++-β (x :: xs) Z))
              ≡⟨ assoc (++-:: x Y (Z ++ xs)) (ap (Y ++_) (++-:: x Z xs)) (ap (Y ++_) (sym (++-β (x :: xs) Z))) ⟩
            (++-:: x Y (Z ++ xs) ∙ (ap (Y ++_) (++-:: x Z xs))) ∙ ap (Y ++_) (sym (++-β (x :: xs) Z))
            ∎
            )

  -- opaque
  --   temp3 : (Square (ap (_++ Z) (++-β xs Y)) (ap (Y ++_) (sym (++-β xs Z))) (++-⬡₌ xs Y Z) (++-α Y xs Z)) → Square (ap (_++ Z) (++-β (x :: xs) Y)) (ap (Y ++_) (sym (++-β (x :: xs) Z))) (++-⬡₌ (x :: xs) Y Z) (++-α Y (x :: xs) Z)
  --   temp3 P i j =
  --       hcomp (λ k → λ
  --         { (i = i0) → left j k
  --         ; (i = i1) → right j k
  --         ; (j = i0) → down i k
  --         ; (j = i1) → up i k
  --         }) (x :: P i j)

    -- temp3 : (Square (ap (_++ Z) (++-β xs Y)) (ap (Y ++_) (sym (++-β xs Z))) (++-⬡₌ xs Y Z) (++-α Y xs Z)) → Square (ap (_++ Z) (++-β (x :: xs) Y)) (ap (Y ++_) (sym (++-β (x :: xs) Z))) (++-⬡₌ (x :: xs) Y Z) (++-α Y (x :: xs) Z)
    -- temp3 P i j =
    --     hcomp (λ k → λ
    --       { (i = i0) → compPath→Square (
    --         ap (x ::_) (ap (_++ Z) (++-β xs Y)) ∙ ap (_++ Z) (++-:: x Y xs)
    --           ≡⟨ sorry ⟩
    --         refl ∙ ap (_++ Z) (++-β (x :: xs) Y)
    --         ∎
    --         ) j k
    --       ; (i = i1) → compPath→Square (
    --         ap (x ::_) (ap (Y ++_) (sym (++-β xs Z))) ∙ (++-:: x Y (xs ++ Z))
    --           ≡⟨ sorry ⟩
    --         (++-:: x Y (Z ++ xs) ∙ (ap (Y ++_) (++-:: x Z xs))) ∙ ap (Y ++_) (sym (++-β (x :: xs) Z))
    --         ∎
    --         ) j k
    --       ; (j = i0) → compPath→Square (
    --         ap (x ::_) (++-⬡₌ xs Y Z) ∙ (++-:: x Y (Z ++ xs) ∙ ap (Y ++_) (++-:: x Z xs))
    --           ≡⟨ sorry ⟩
    --         refl ∙ ++-⬡₌ (x :: xs) Y Z
    --         ∎
    --         ) i k
    --       ; (j = i1) → compPath→Square (
    --         ap (x ::_) (++-α Y xs Z) ∙ ++-:: x Y (xs ++ Z)
    --           ≡⟨ sorry ⟩
    --         ap (_++ Z) (++-:: x Y xs) ∙ ++-α Y (x :: xs) Z
    --         ∎
    --         ) i k
    --       }) (x :: P i j)


module _ (X Y Z : SList A) where
  opaque
    unfolding ++-⬡₌ ++-:: ++-α ++-ρ ++-β

    ++-⬡₁ : Square
            (sym (++-α X Y Z))
            (++-α Y Z X)
            (++-β X (Y ++ Z))
            (++-⬡₌ X Y Z)
    -- ++-⬡₁ = sorry
    -- ++-⬡₁ = doubleCompPath-filler (++-α X Y Z) (++-β X (Y ++ Z)) (++-α Y Z X)

    -- ++-⬡₌ = ++-α X Y Z ∙∙ ++-β X (Y ++ Z) ∙∙ ++-α Y Z X


    ++-⬡₁ = compPath→Square (lUnit (++-β X (Y ++ Z) ∙ ++-α Y Z X) ∙ sym (ap (_∙ ++-β X (Y ++ Z) ∙ ++-α Y Z X) (lCancel (++-α X Y Z))) ∙ sym (assoc (sym (++-α X Y Z)) (++-α X Y Z) (++-β X (Y ++ Z) ∙ ++-α Y Z X)))

    ++-⬡₂ : Square
            (ap (_++ Z) (++-β X Y))
            (ap (_++_ Y) (sym (++-β X Z)))
            (++-⬡₌ X Y Z)
            (++-α Y X Z)
    ++-⬡₂ =
      SListElimProp.elim
        (λ X → Square
               (ap (_++ Z) (++-β X Y))
               (ap (_++_ Y) (sym (++-β X Z)))
               (++-⬡₌ X Y Z)
               (++-α Y X Z))
        (SListElimProp.elim
          (λ Y → Square
            (ap (_++ Z) (sym (++-ρ Y)))
            (ap (Y ++_ ) (++-ρ Z))
            (++-⬡₌ nil Y Z)
            (++-α Y nil Z))
          (tpt (λ a → Square
                      refl
                      (++-ρ Z)
                      a
                      refl)
                (rUnit (sym (++-ρ Z)) ∙ lUnit (sym (++-ρ Z) ∙ refl))
                (λ i j → ++-ρ Z (~ i ∨ j)))
          (λ y {ys} Q →
            tpt
              (λ a → Square
                     (ap (_++ Z) (sym (++-ρ (y :: ys))))
                     (ap (y :: ys ++_) (++-ρ Z))
                     a
                     (++-α (y :: ys) nil Z))
              (ap-∙ (y ::_) refl (sym (++-ρ (ys ++ Z)) ∙ ++-α ys Z nil)
               ∙ ap (ap (y ::_) refl ∙_) (ap-∙ (y ::_) (sym (++-ρ (ys ++ Z))) (++-α ys Z nil)))
              λ i j → y :: Q i j)
          (λ Y → isOfHLevelPathP' 1 (is-groupoid (Y ++ Z ++ nil) (++-α Y nil Z i1)) _ _)
          Y
        )
        -- x :: a (Y xs Z) = a (Y x :: xs Z)
        -- (λ x P i j → {!!})
        (λ x {xs} P i j →
          hcomp (λ k → λ
            { (i = i0) → left x xs Y Z j k
            ; (i = i1) → right x xs Y Z j k
            ; (j = i0) → down x xs Y Z i k
            ; (j = i1) → up x xs Y Z i k
            }) (x :: P i j))
        (λ X → isOfHLevelPathP' 1 (is-groupoid (++-⬡₌ X Y Z i1) (++-α Y X Z i1)) _ _)
        X

module _ (X Y : SList A) where
  opaque
    unfolding ++-β ++-ρ ++-::

    ++-β² : ++-β X Y ≡ sym (++-β Y X)
    ++-β² =
      SListElimProp.elim
        (λ X → ++-β X Y ≡ sym (++-β Y X))
        (SListElimProp.elim
          (λ Y → ++-β nil Y ≡ sym (++-β Y nil))
          refl
          (λ y {ys} Q →
            ++-β nil (y :: ys)
              ≡⟨ refl ⟩
            sym (++-ρ (y :: ys))
              ≡⟨ refl ⟩
            sym (ap (y ::_) (++-ρ ys))
              ≡⟨ refl ⟩
            ap (y ::_) (sym (++-ρ ys))
              ≡⟨ refl ⟩
            ap (y ::_) (++-β nil ys)
              ≡⟨ ap (ap (y ::_)) Q ⟩
            ap (y ::_) (sym (++-β ys nil))
              ≡⟨ refl ⟩
            sym (ap (y ::_) (++-β ys nil))
              ≡⟨ rUnit (ap (y ::_) (sym (++-β ys nil))) ⟩
            sym (++-β (y :: ys) nil)
            ∎
          )
          (λ xs → is-groupoid _ _ _ _)
          Y
          )
        (λ x {xs} P →
          SListElimProp.elim
          (λ Y → ++-β (x :: xs) Y ≡ sym (++-β Y (x :: xs)))
          sorry -- {!refl!}
          (λ y {ys} Q → {!!}
            -- ++-β (x :: xs) (y :: ys)
            --   ≡⟨ refl ⟩
            -- ap (x ::_) (++-β xs (y :: ys)) ∙ ++-:: x (y :: ys) xs
            --   ≡⟨ ap (λ a → ap (x ::_) a ∙ ++-:: x (y :: ys) xs) {!P !} ⟩
            -- ap (x ::_) {!!} ∙ ++-:: x (y :: ys) xs
            --   ≡⟨ {!!} ⟩
            -- {!!}
            --   ≡⟨ {!!} ⟩
            -- {!!}
            --   ≡⟨ {!!} ⟩
            -- sym (++-:: y (x :: xs) ys) ∙ sym (ap (y ::_) (++-β ys (x :: xs)))
            --   ≡⟨ sym (symDistr (ap (y ::_) (++-β ys (x :: xs))) (++-:: y (x :: xs) ys)) ⟩
            -- sym (ap (y ::_) (++-β ys (x :: xs)) ∙ ++-:: y (x :: xs) ys)
            --   ≡⟨ refl ⟩
            -- sym (++-β (y :: ys) (x :: xs))
            -- ∎
          )
          (λ ys → is-groupoid (x :: xs ++ ys) (ys ++ x :: xs) (++-β (x :: xs) ys) (sym (++-β ys (x :: xs))))
          Y
        )
        (λ xs → is-groupoid (xs ++ Y) (Y ++ xs) (++-β xs Y) (sym (++-β Y xs)))
        X

-- let
      -- p = sorry in

        -- (λ X → ++-β X Y ≡ sym (++-β Y X))s
        -- {!sym ρ Y ≡!}
        -- (λ x {xs} P → tpt (λ X → {!!}) {!++-:: x xs Y!} λ i j → x :: P i j)
        -- {!is-groupoid!}
        -- X
