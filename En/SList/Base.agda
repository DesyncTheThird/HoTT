module En.SList.Base where

open import En.Prelude

infixr 30 _::_

data SList {ℓ} (A : Type ℓ) : Type ℓ where
    nil : SList A
    _::_ : A → SList A → SList A

    swap : (x y : A) (xs : SList A) → x :: (y :: xs) ≡ y :: (x :: xs)
    swap² : (x y : A) (xs : SList A) → swap x y xs ≡ sym (swap y x xs)

    ⬡₌ : (x y z : A) (xs : SList A)
        → x :: (y :: (z :: xs)) ≡ z :: (y :: (x :: xs))
    ⬡₁ : (x y z : A) (xs : SList A)
        → Square (sym (swap x y (z :: xs))) (swap y z (x :: xs)) (ap (y ::_) (swap x z xs)) (⬡₌ x y z xs)
    ⬡₂ : (x y z : A) (xs : SList A)
        → Square (ap (x ::_) (swap y z xs)) (sym (ap (z ::_) (swap x y xs))) (⬡₌ x y z xs) (swap x z (y :: xs))

    is-groupoid : isGroupoid (SList A)

pattern [] = nil
pattern [_] x = x :: nil

module SListElim {ℓ ℓ'} {A : Type ℓ} (P : SList A → Type ℓ')
    (nil* : P nil)
    (_::*_ : (x : A) {xs : SList A} → (xs* : P xs) → P (x :: xs))

    (swap* : (x y : A) {xs : SList A} (xs* : P xs)
        → PathP (λ i → P (swap x y xs i)) (x ::* (y ::* xs*)) (y ::* (x ::* xs*)))

    (swap²* : (x y : A) {xs : SList A} (xs* : P xs)
        → SquareP (λ i j → P (swap² x y xs i j)) (swap* x y xs*) (symP (swap* y x xs*)) refl refl)

    (⬡₌* : (x y z : A) {xs : SList A} (xs* : P xs)
        → PathP (λ i → P (⬡₌ x y z xs i)) (x ::* (y ::* (z ::* xs*))) (z ::* (y ::* (x ::* xs*))))

    (⬡₁* : (x y z : A) {xs : SList A} (xs* : P xs)
        → SquareP (λ i j → P (⬡₁ x y z xs i j)) ((symP (swap* x y (z ::* xs*)))) (swap* y z (x ::* xs*)) (apP (λ i a → y ::* a) (swap* x z xs*)) (⬡₌* x y z xs*))

    (⬡₂* : (x y z : A) {xs : SList A} (xs* : P xs)
        → SquareP (λ i j → P (⬡₂ x y z xs i j)) (apP (λ i a → x ::* a) (swap* y z xs*)) (symP (apP (λ i a → z ::* a) (swap* x y xs*))) (⬡₌* x y z xs*) (swap* x z (y ::* xs*)))

    (is-groupoid* : (xs : SList A) → isGroupoid (P xs))
    where
    elim : (xs : SList A) → P xs
    elim nil = nil*
    elim (x :: xs) = x ::* elim xs
    elim (swap x y xs i) = swap* x y (elim xs) i
    elim (swap² x y xs i j) = swap²* x y (elim xs) i j
    elim (⬡₌ x y z xs i) = ⬡₌* x y z (elim xs) i
    elim (⬡₁ x y z xs i j) = ⬡₁* x y z (elim xs) i j
    elim (⬡₂ x y z xs i j) = ⬡₂* x y z (elim xs) i j
    elim (is-groupoid xs xs' p q r s i j k) = isGroupoid→CubeP (λ i j k → P (is-groupoid xs xs' p q r s i j k))
         (λ j k → elim (r j k)) (λ j k → elim (s j k)) (λ i k → elim (p k)) (λ i k → elim (q k)) (λ i j → elim xs) (λ i j → elim xs') (is-groupoid* xs') i j k


module SListElimSet {ℓ ℓ'} {A : Type ℓ} (P : SList A → Type ℓ')
    (nil* : P nil)
    (_::*_ : (x : A) {xs : SList A} → (xs* : P xs) → P (x :: xs))

    (swap* : (x y : A) {xs : SList A} (xs* : P xs)
        → PathP (λ i → P (swap x y xs i)) (x ::* (y ::* xs*)) (y ::* (x ::* xs*)))

    (is-set* : (xs : SList A) → isSet (P xs))
    where
    elim : (xs : SList A) → P xs
    elim =
      SListElim.elim P nil* _::*_ swap*
        (λ x y {xs} xs* → isSet→SquareP (λ i j → is-set* (swap² x y xs i j)) (swap* x y xs*) (symP (swap* y x xs*)) refl refl)
        (λ x y z {xs} xs* → sorry -- compPathP (swap* x y (z ::* xs*)) (compPathP (apP (λ _ → y ::*_) (swap* x z xs*)) (swap* y z (x ::* xs*))) {!!}
        )
        (λ x y z {xs} xs* → isSet→SquareP (λ i j → is-set* (⬡₁ x y z xs i j)) (symP (swap* x y (z ::* xs*))) (swap* y z (x ::* xs*)) (apP (λ i₁ → y ::*_) (swap* x z xs*)) sorry)
        (λ x y z {xs} xs* → isSet→SquareP (λ i j → is-set* (⬡₂ x y z xs i j)) (apP (λ i → _::*_ x) (swap* y z xs*)) (symP (apP (λ i → _::*_ z) (swap* x y xs*))) sorry λ i → swap* x z (y ::* xs*) i)
        (λ xs → isSet→isGroupoid (is-set* xs))

-- PathP (λ i → P (⬡₌ x y z xs i)) (x ::* (y ::* (z ::* xs*))) (z ::* (y ::* (x ::* xs*)))

module SListElimProp {ℓ ℓ'} {A : Type ℓ} (P : SList A → Type ℓ')
    (nil* : P nil)
    (_::*_ : (x : A) {xs : SList A} → (xs* : P xs) → P (x :: xs))
    (is-prop* : (xs : SList A) → isProp (P xs))
    where
    elim : (xs : SList A) → P xs
    elim =
      SListElimSet.elim P nil* _::*_
        (λ x y {xs} xs* → isProp→PathP (λ i → is-prop* (swap x y xs i)) (x ::* (y ::* xs*)) (y ::* (x ::* xs*)))
        (λ xs → isProp→isSet (is-prop* xs))

module SListElimPaths {ℓ ℓ'} {A : Type ℓ} (P : SList A → Type ℓ') (f g : (xs : SList A) → P xs)
    (nil* : f nil ≡ g nil)
    (_::*_ : (x : A) {xs : SList A} → (H : f xs ≡ g xs) → f (x :: xs) ≡ g (x :: xs))
    (swap* : (x y : A) {xs : SList A} (xs* : f xs ≡ g xs)
        → PathP (λ i → f (swap x y xs i) ≡ g (swap x y xs i)) (x ::* (y ::* xs*)) (y ::* (x ::* xs*)))
    (is-groupoid* : (xs : SList A) → isGroupoid (P xs))
    where

    elim : (xs : SList A) → f xs ≡ g xs
    elim =
      SListElimSet.elim (λ xs → f xs ≡ g xs) nil* _::*_ swap*
        (λ xs → is-groupoid* xs (f xs) (g xs))

module SListElimPathsSet {ℓ ℓ'} {A : Type ℓ} (P : SList A → Type ℓ') (f g : (xs : SList A) → P xs)
    (nil* : f nil ≡ g nil)
    (_::*_ : (x : A) {xs : SList A} → (H : f xs ≡ g xs) → f (x :: xs) ≡ g (x :: xs))
    (is-set* : (xs : SList A) → isSet (P xs))
    where

    elim : (xs : SList A) → f xs ≡ g xs
    elim =
      SListElimProp.elim (λ xs → f xs ≡ g xs) nil* _::*_ (λ xs → is-set* xs (f xs) (g xs))


module SListElim2Paths {ℓ ℓ'} {A : Type ℓ} (P : SList A → Type ℓ')
    (f g : (xs : SList A) → P xs)
    (p q : (xs : SList A) → f xs ≡ g xs)
    (nil* : p nil ≡ q nil)
    (_::*_ : (x : A) {xs : SList A} → (H : p xs ≡ q xs) → p (x :: xs) ≡ q (x :: xs))
    (is-groupoid* : (xs : SList A) → isGroupoid (P xs))
    where

    elim : (xs : SList A) → p xs ≡ q xs
    elim =
      SListElimProp.elim (λ xs → p xs ≡ q xs) nil* _::*_
        (λ xs → is-groupoid* xs (f xs) (g xs) (p xs) (q xs))
