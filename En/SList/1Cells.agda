module En.SList.1Cells where

open import En.Prelude
open import En.SList.0Cells
open import En.SList.Base
import En.SMG as S hiding (SMG* ; SMG*Fun)

private
  variable
    A : Type ℓ

++-Λ : (xs : SList A) → nil ++ xs ≡ xs
++-Λ xs = refl

++-ρ : (xs : SList A) → xs ++ nil ≡ xs
++-ρ =
  SListElimSet.elim
    (λ xs → xs ++ nil ≡ xs)
    refl
    (λ x → ap (x ::_))
    (λ x y p → compPath→Square (homotopyNatural (swap x y) p))
    (λ xs → is-groupoid (xs ++ nil) xs)

++-α : (xs ys zs : SList A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-α xs ys zs =
  SListElimSet.elim (λ xs → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs))
    refl
    (λ x → ap (x ::_))
    (λ x y p → compPath→Square (homotopyNatural (swap x y) p))
    (λ xs → is-groupoid ((xs ++ ys) ++ zs) (xs ++ ys ++ zs)) xs

++-:: : (x : A) (xs ys : SList A) → (x :: xs) ++ ys ≡ xs ++ (x :: ys)
++-:: x xs ys =
  SListElimPaths.elim (λ _ → SList _) (λ xs → (x :: xs) ++ ys) (λ xs → xs ++ (x :: ys))
    refl
    (λ y {xs} p → swap x y (xs ++ ys) ∙ ap (y ::_) p)
    (λ y z {xs} p →
      let S = (compPath→Square (homotopyNatural (swap y z) p))
          T = invSquarev (compPath→Triangle₀ (sym (ap-∙ (y ::_) (swap x z (xs ++ ys)) (ap (z ::_) p))))
          U = invSquareh (compPath→Triangle₀ (sym (ap-∙ (z ::_) (swap x y (xs ++ ys)) (ap (y ::_) p))))
          V = T ∙h ⬡₁ x y z (xs ++ ys) ∙h ⬡₂ x y z (xs ++ ys)
          W = flipSquare (yaMorphSquare (S ∙v U))
          X = V ∙v W
          Y = tpt3 (λ p' q r → Square p' ( swap y z (xs ++ x :: ys)
                                         ∙ sym (ap (z ::_) (swap x y (xs ++ ys)
                                         ∙ (ap (y ::_) p)))) q r)
                   (sym (lUnit _)) (sym (rUnit _)) (sym (rUnit _)) X
      in flipSquare (yaaMorphSquare Y))
    (λ xs → is-groupoid)
    xs



swap²-++-:: : (x y : A) (xs ys : SList A) → swap x y (xs ++ ys) ∙ swap y x (xs ++ ys) ≡ refl
swap²-++-:: x y xs ys = ap ((swap x y (xs ++ ys)) ∙_) (swap² y x (xs ++ ys)) ∙ rCancel (swap x y (xs ++ ys))

module _ (x y : A) (xs ys : SList A) (z : A) (zs : SList A) where
  abstract
    private
      S : Square
          (swap z x (zs ++ y :: xs))
          refl
          (ap (z ::_) (++-:: x zs (y :: xs)))
          (++-:: x (z :: zs) (y :: xs))
      S = compPath→Square (sym (rUnit (ap (z ::_) (++-:: x zs (y :: xs))))
          ∙ lUnit (ap (z ::_) (++-:: x zs (y :: xs))) ∙ (ap ( _∙ (ap (z ::_) (++-:: x zs (y :: xs)))) (sym (swap²-++-:: z x zs (y :: xs)))) ∙ sym (assoc (swap z x (zs ++ y :: xs)) (swap x z (zs ++ y :: xs)) (ap (z ::_) (++-:: x zs (y :: xs))))
          )
      T : Square
          (swap z x (y :: zs ++ xs))
          (swap z x (zs ++ y :: xs))
          (ap (λ a → z :: x :: a) (++-:: y zs xs))
          (ap (λ a → x :: z :: a) (++-:: y zs xs))
      T = flipSquare (compPath→Square (homotopyNatural (swap z x) (++-:: y zs xs)))
      U : Square
          (ap (x ::_) (swap z y (zs ++ xs)))
          refl
          (ap (λ a → x :: z :: a) (++-:: y zs xs))
          (ap (x ::_) (++-:: y (z :: zs) xs))
      U = compPath→Square (sym ((rUnit (ap (λ a → x :: z :: a) (++-:: y zs xs))))
          ∙ ap (ap (x ::_)) (lUnit _ ∙ ap (_∙ (ap (z ::_) (++-:: y zs xs))) (sym (swap²-++-:: z y zs xs))
          ∙ sym (assoc (swap z y (zs ++ xs)) (swap y z (zs ++ xs)) (ap (z ::_) (++-:: y zs xs))))
          ∙ ap-∙ (x ::_) (swap z y (zs ++ xs)) (++-:: y (z :: zs) xs))
      S' : Square
          (swap z y (zs ++ x :: xs))
          refl
          (ap (z ::_) (++-:: y zs (x :: xs)))
          (++-:: y (z :: zs) (x :: xs))
      S' = compPath→Square ((sym (rUnit (ap (z ::_) (++-:: y zs (x :: xs))))) ∙ lUnit (ap (z ::_) (++-:: y zs (x :: xs))) ∙ (ap ( _∙ (ap (z ::_) (++-:: y zs (x :: xs)))) (sym (swap²-++-:: z y zs (x :: xs)))) ∙ sym (assoc (swap z y (zs ++ x :: xs)) (swap y z (zs ++ x :: xs)) (ap (z ::_) (++-:: y zs (x :: xs)))))
      T' : Square
          (swap z y (x :: zs ++ xs))
          (swap z y (zs ++ x :: xs))
          (ap (λ a → z :: y :: a) (++-:: x zs xs))
          (ap (λ a → y :: z :: a) (++-:: x zs xs))
      T' = flipSquare (compPath→Square (homotopyNatural (swap z y) (++-:: x zs xs)))
      U' : Square
          (ap (y ::_) (swap z x (zs ++ xs)))
          refl
          (ap (λ a → y :: z :: a) (++-:: x zs xs))
          (ap (y ::_) (++-:: x (z :: zs) xs))
      U' = compPath→Square (sym (rUnit (ap (λ a → y :: z :: a) (++-:: x zs xs)))
           ∙ ap (ap (y ::_)) (lUnit _ ∙ ap (_∙ (ap (z ::_) (++-:: x zs xs))) (sym (swap²-++-:: z x zs xs)) ∙ sym (assoc (swap z x (zs ++ xs)) (swap x z (zs ++ xs)) (ap (z ::_) (++-:: x zs xs))))
           ∙ ap-∙ (y ::_) (swap z x (zs ++ xs)) (++-:: x (z :: zs) xs))
      V : Hexagon (sym (ap (z ::_) (swap x y (zs ++ xs)))) (swap z x (y :: zs ++ xs)) (ap (x ::_) (swap z y (zs ++ xs))) (swap z y (x :: zs ++ xs)) (ap (y ::_) (swap z x (zs ++ xs))) (sym (swap x y (z :: zs ++ xs)))
      V = HexagonRotate⁻ (hexagon (⬡₌ z x y (zs ++ xs)) (⬡₁ z x y (zs ++ xs)) (⬡₂ z x y (zs ++ xs)))
      down : Square
             (swap z x (y :: zs ++ xs) ∙ ap (x ::_) (swap z y (zs ++ xs)))
             (swap z y (x :: zs ++ xs) ∙ ap (y ::_) (swap z x (zs ++ xs)))
             (ap (z ::_) (swap x y (zs ++ xs)))
             (swap x y (z :: zs ++ xs))
      down = flipSquare (HexagonAssoc⁻ (V .Hexagon.⬡₁ ∙h V .Hexagon.⬡₂))
      left : Square
             (swap z x (y :: zs ++ xs) ∙ ap (x ::_) (swap z y (zs ++ xs)))
             refl
             (ap (λ a → z :: x :: a) (++-:: y zs xs) ∙ ap (z ::_) (++-:: x zs (y :: xs)))
               (ap (x ::_) (++-:: y (z :: zs) xs) ∙ ++-:: x (z :: zs) (y :: xs))
      left = tpt (λ a →
                      Square
                      (swap z x (y :: zs ++ xs) ∙ ap (x ::_) (swap z y (zs ++ xs)))
                      a
                      (ap (λ a → z :: x :: a) (++-:: y zs xs) ∙ ap (z ::_) (++-:: x zs (y :: xs)))
                      (ap (x ::_) (++-:: y (z :: zs) xs) ∙ ++-:: x (z :: zs) (y :: xs))
                  )
                  (sym (lUnit refl))
                  (((T ∙v S) ∙h (U ∙v (λ i j → (++-:: x (z :: zs) (y :: xs) ) i))))
      right : Square
              (swap z y (x :: zs ++ xs) ∙ ap (y ::_) (swap z x (zs ++ xs)))
              refl
              (ap (λ a → z :: y :: a) (++-:: x zs xs) ∙ ap (z ::_) (++-:: y zs (x :: xs)))
              (ap (y ::_) (++-:: x (z :: zs) xs) ∙ ++-:: y (z :: zs) (x :: xs))
      right = tpt (λ a →
                      Square
                      (swap z y (x :: zs ++ xs) ∙ ap (y ::_) (swap z x (zs ++ xs)))
                      a
                      (ap (λ a → z :: y :: a) (++-:: x zs xs) ∙ ap (z ::_) (++-:: y zs (x :: xs)))
                      (ap (y ::_) (++-:: x (z :: zs) xs) ∙ ++-:: y (z :: zs) (x :: xs))
                  )
                  (sym (lUnit refl))
                  ((T' ∙v S') ∙h (U' ∙v (λ i j → (++-:: y (z :: zs) (x :: xs) ) i)))


    module _ (p : ((λ i → x :: ++-:: y zs xs i) ∙∙ ++-:: x zs (y :: xs) ∙∙ (λ i → zs ++ swap x y xs i))
                  ≡ (swap x y (zs ++ xs) ∙∙ (λ i → y :: ++-:: x zs xs i) ∙∙ ++-:: y zs (x :: xs))) where
      E : Square
          (ap (x ::_) (++-:: y (z :: zs) xs) ∙ ++-:: x (z :: zs) (y :: xs))
          (ap (y ::_) (++-:: x (z :: zs) xs) ∙ ++-:: y (z :: zs) (x :: xs))
          (swap x y (z :: zs ++ xs))
          (ap (z :: zs ++_) (swap x y xs))

      E i j = hcomp ((λ k → (λ
            { (i = i0) → left j k
            ; (i = i1) → right j k
            ; (j = i0) → down i k
            ; (j = i1) → ap (z :: zs ++_) (swap x y xs) i
            }))) ((compPath→Square ((lUnit _) ∙ Square→compPath (doubleCompPathEq→compPathEq P) ∙ sym (rUnit _) ∙ assoc _ _ _)) i j)
                where P = sym (ap-∙∙ (z ::_) ((λ i → x :: ++-:: y zs xs i)) (++-:: x zs (y :: xs)) (ap (zs ++_) (swap x y xs)))
                                            ∙ ap (ap (z ::_)) p ∙
                                            ap-∙∙ (z ::_) (swap x y (zs ++ xs)) (ap (y ::_) (++-:: x zs xs)) (++-:: y zs (x :: xs))



module _ (x y : A) (xs ys : SList A) (z : A) (zs : SList A) (p : xs ++ ys ≡ ys ++ xs) where
  abstract
    ++-β-aux : (ap (x ::_) (++-:: y ys xs) ∙∙ ++-:: x ys (y :: xs) ∙∙ ap (ys ++_) (swap x y xs))
      ≡ (swap x y (ys ++ xs) ∙∙ ap (y ::_) (++-:: x ys xs) ∙∙ ++-:: y ys (x :: xs))
    ++-β-aux = SListElim2Paths.elim
      (λ _ → SList A)
      (λ ys → x :: y :: ys ++ xs)
      (λ ys → ys ++ y :: x :: xs)
      (λ ys → (ap (_::_ x) (++-:: y ys xs) ∙∙ ++-:: x ys (y :: xs) ∙∙
             ap (_++_ ys) (swap x y xs)))
      (λ ys → (swap x y (ys ++ xs) ∙∙ ap (_::_ y) (++-:: x ys xs) ∙∙
            ++-:: y ys (x :: xs)))
      (
        refl ∙ (swap x y (nil ++ xs))
          ≡⟨ sym (lUnit (swap x y (nil ++ xs))) ⟩
        (swap x y (nil ++ xs))
          ≡⟨ (rUnit _ ∙ rUnit _)⟩
        (swap x y (nil ++ xs) ∙ refl) ∙ refl
          ≡⟨ sym (assoc (swap x y (nil ++ xs)) refl refl) ⟩
        (swap x y (nil ++ xs) ∙ refl ∙ refl)
          ≡⟨ sym (doubleCompPath≡compPath (swap x y (nil ++ xs)) refl refl) ⟩
        (swap x y (nil ++ xs) ∙∙ refl ∙∙ refl)
        ∎
      )
      (λ z {zs} p → doubleCompPath≡compPath (ap (x ::_) (++-:: y (z :: zs) xs)) (++-:: x (z :: zs) (y :: xs)) (ap (z :: zs ++_ ) (swap x y xs))
                  ∙ ((assoc (ap (x ::_ ) (++-:: y (z :: zs) xs)) (++-:: x (z :: zs) (y :: xs)) (ap (z :: zs ++_) (swap x y xs))) ∙ sym (Square→compPath (E x y xs ys z zs p)))
                  ∙ sym (doubleCompPath≡compPath (swap x y (z :: zs ++ xs)) (ap (y ::_) (++-:: x (z :: zs) xs)) (++-:: y (z :: zs) (x :: xs))))
      (λ _ → is-groupoid)
      ys

    β-boundary :
      (ap (x ::_) (ap (y ::_) p ∙ ++-:: y ys xs) ∙ ++-:: x ys (y :: xs)) ∙ ap (ys ++_) (swap x y xs)
      ≡
      ap (_++ ys) (swap x y xs) ∙ (ap (y ::_) (ap (x ::_) p ∙ ++-:: x ys xs) ∙ ++-:: y ys (x :: xs))
    β-boundary = let
      A = ap (x ::_) (ap (y ::_) p)
      B = ap (x ::_) (++-:: y ys xs)
      C = ++-:: x ys (y :: xs)
      D = ap (ys ++_) (swap x y xs)

      E = swap x y (ys ++ xs)
      F = ap (y ::_) (++-:: x ys xs)
      G = ++-:: y ys (x :: xs)

      S = swap x y (xs ++ ys)
      T = ap (y ::_) (ap (x ::_) p)
      U = ap (_++ ys) (swap x y xs)
      R = ap (y ::_) (ap (x ::_) p ∙ ++-:: x ys xs)
      in

      (ap (x ::_) (ap (y ::_) p ∙ ++-:: y ys xs) ∙ ++-:: x ys (y :: xs)) ∙ ap (ys ++_) (swap x y xs)
        ≡⟨ ap (λ a → (a ∙ ++-:: x ys (y :: xs)) ∙ ap (ys ++_) (swap x y xs)) (ap-∙ (x ::_) (ap (y ::_ ) p) (++-:: y ys xs))  ⟩
      ((A ∙ B) ∙ C) ∙ D
        ≡⟨ sym (assoc (A ∙ B) C D) ⟩
      (A ∙ B) ∙ (C ∙ D)
        ≡⟨ sym (assoc A B (C ∙ D)) ⟩
      A ∙ (B ∙ (C ∙ D))
        ≡⟨ ap (A ∙_) (doubleCompPathEq→compPathEq ++-β-aux) ⟩
      A ∙ (E ∙ (F ∙ G))
        ≡⟨ assoc A E (F ∙ G) ⟩
      (A ∙ E) ∙ (F ∙ G)
        ≡⟨ ap (_∙ F ∙ G) (sym (homotopyNatural (swap x y) p)) ⟩
      (S ∙ T) ∙ (F ∙ G)
        ≡⟨ sym (assoc S T (F ∙ G)) ⟩
      S ∙ (T ∙ (F ∙ G))
        ≡⟨ ap (S ∙_) (assoc T F G) ⟩
      S ∙ ((T ∙ F) ∙ G)
        ≡⟨ ap (λ a → S ∙ (a ∙ G)) (sym (ap-∙ (y ::_) (ap (x ::_) p) (++-:: x ys xs))) ⟩
      S ∙ (R ∙ G)
        ≡⟨ refl ⟩
      U ∙ (R ∙ G) ∎

    β-swap :
      PathP (λ i → swap x y xs i ++ ys ≡ ys ++ swap x y xs i)
        (ap (x ::_) (ap (y ::_) p ∙ ++-:: y ys xs) ∙ ++-:: x ys (y :: xs))
        (ap (y ::_) (ap (x ::_) p ∙ ++-:: x ys xs) ∙ ++-:: y ys (x :: xs))
    β-swap = let
      A = ap (ys ++_) (swap x y xs)
      B = ap (_++ ys) (swap x y xs)
      P = ap (x ::_) (ap (y ::_) p ∙ ++-:: y ys xs) ∙ ++-:: x ys (y :: xs)
      Q = ap (y ::_) (ap (x ::_) p ∙ ++-:: x ys xs) ∙ ++-:: y ys (x :: xs)
      in
      compPathR→PathP (
        ap (x ::_) (ap (y ::_) p ∙ ++-:: y ys xs) ∙ ++-:: x ys (y :: xs)
          ≡⟨ refl ⟩
        P
          ≡⟨ rUnit _ ⟩
        P ∙ refl
          ≡⟨ ap (P ∙_) (sym (rCancel A)) ⟩
        P ∙ A ∙ sym A
          ≡⟨ assoc P A (sym A) ⟩
        (P ∙ A) ∙ sym A
          ≡⟨ ap (_∙ sym A) β-boundary ⟩
        (ap (_++ ys) (swap x y xs) ∙ ap (y ::_) (ap (x ::_) p ∙ ++-:: x ys xs) ∙ ++-:: y ys (x :: xs)) ∙ sym A
          ≡⟨ refl ⟩
        (B ∙ Q) ∙ sym A
          ≡⟨ sym (assoc B Q (sym A)) ⟩
        B ∙ Q ∙ (sym A)
          ≡⟨ refl ⟩
        ap (_++ ys) (swap x y xs) ∙ (ap (y ::_) (ap (x ::_) p ∙ ++-:: x ys xs) ∙ ++-:: y ys (x :: xs)) ∙ sym (ap (ys ++_) (swap x y xs)) ∎
      )

++-β : (xs ys : SList A) → xs ++ ys ≡ ys ++ xs
++-β xs ys =
  SListElimPaths.elim (λ _ → SList _) (_++ ys) (ys ++_)
    (sym (++-ρ ys))
    (λ x {xs} p → ap (x ::_) p ∙ ++-:: x ys xs)
    (λ x y {xs} p → β-swap x y xs ys x ys p)
    (λ _ → is-groupoid)
    xs
