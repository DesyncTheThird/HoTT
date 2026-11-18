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
    unfolding ++-α
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

++-⬠₌ : (W X Y Z : SList A) → ((W ++ X) ++ Y) ++ Z ≡ W ++ X ++ Y ++ Z
++-⬠₌ W X Y Z =
  SListElimSet.elim
    (λ W → ((W ++ X) ++ Y) ++ Z ≡ W ++ X ++ Y ++ Z)
    (++-α X Y Z)
    (λ x {xs} P i → x :: P i)
    (λ x y {xs} P → flipSquare (homotopyNaturalSq (swap x y) P))
    (λ xs → isOfHLevelPathP' 2 is-groupoid _ _)
    W

module _ (W X Y Z : SList A) where

  opaque
    unfolding ++-α
    ++-⬠₁ : Square
            (sym (++-α (W ++ X) Y Z))
            (++-α W X (Y ++ Z))
            refl
            (++-⬠₌ W X Y Z)
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
    ++-⬡₌ : (X ++ Y) ++ Z ≡ Y ++ (Z ++ X)
    ++-⬡₌ = ++-α X Y Z ∙ ++-β X (Y ++ Z) ∙ ++-α Y Z X

module _ (X Y Z : SList A) where
  opaque
    unfolding ++-⬡₌ ++-:: ++-α

    ++-⬡₁ : Square
            (sym (++-α X Y Z))
            (++-α Y Z X)
            (++-β X (Y ++ Z))
            (++-⬡₌ X Y Z)
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
        (λ x {xs} P i j → {!x :: P i j!})
        (λ X → isOfHLevelPathP' 1 (is-groupoid (++-⬡₌ X Y Z i1) (++-α Y X Z i1)) _ _)
        X

module _ (X Y : SList A) where
  opaque
    unfolding ++-:: ++-α

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
          sorry -- TODO: β² cons-nil case for SList
          (λ y {ys} Q →
            ++-β (x :: xs) (y :: ys)
              ≡⟨ refl ⟩
            ap (x ::_) (++-β xs (y :: ys)) ∙ ++-:: x (y :: ys) xs
              ≡⟨ ap (λ a → ap (x ::_) a ∙ ++-:: x (y :: ys) xs) {!P !} ⟩
            ap (x ::_) {!!} ∙ ++-:: x (y :: ys) xs
              ≡⟨ {!!} ⟩
            {!!}
              ≡⟨ {!!} ⟩
            {!!}
              ≡⟨ {!!} ⟩
            sym (++-:: y (x :: xs) ys) ∙ sym (ap (y ::_) (++-β ys (x :: xs)))
              ≡⟨ sym (symDistr (ap (y ::_) (++-β ys (x :: xs))) (++-:: y (x :: xs) ys)) ⟩
            sym (ap (y ::_) (++-β ys (x :: xs)) ∙ ++-:: y (x :: xs) ys)
              ≡⟨ refl ⟩
            sym (++-β (y :: ys) (x :: xs))
            ∎
          )
          sorry -- TODO: β² cons case is-prop for SList
          Y
        )
        sorry -- TODO: β² is-prop for SList
        X
