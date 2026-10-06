module En.GroupoidQuotients.Properties where

open import En.Prelude
open import Cubical.Foundations.Equiv.Properties using ( compl≡Equiv )
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.GroupoidQuotients.Base
import Cubical.HITs.GroupoidQuotients as GQ

private
  variable
    ℓA ℓB ℓR : Level

  PathP→∙ : ∀ {ℓ} {X : Type ℓ} {x y z : X} {p : x ≡ y} {q : y ≡ z} {r : x ≡ z}
    → PathP (λ i → x ≡ q i) p r → p ∙ q ≡ r
  PathP→∙ {x = x} {p = p} {q} P j i =
    hcomp (λ k → λ { (i = i0) → x
                   ; (i = i1) → q k
                   ; (j = i1) → P k i
                   })
          (p i)

-- effectivity of groupoid quotients

module KernelPair {A : Type ℓA} {B : Type ℓB} {R : A → A → Type ℓR}
  (isTransR : BinaryRelation.isTrans R)
  (isGroupoidB : isGroupoid B)
  (f : A → B)
  (R≃ : {a b : A} → R a b ≃ (f a ≡ f b))
  (R≃-∙ : {a b c : A} (r : R a b) (s : R b c) → –> R≃ (isTransR a b c r s) ≡ –> R≃ r ∙ –> R≃ s)
  where

  private
    path : {a b : A} → R a b → f a ≡ f b
    path = –> R≃

    rel : {a b : A} → f a ≡ f b → R a b
    rel = <– R≃

    rel-∙ : {a b c : A} (q : f a ≡ f b) (s : R b c) → rel (q ∙ path s) ≡ isTransR a b c (rel q) s
    rel-∙ q s =
      rel (q ∙ path s)
        ≡⟨ ap (λ x → rel (x ∙ path s)) (sym (secEq R≃ q)) ⟩
      rel (path (rel q) ∙ path s)
        ≡⟨ ap rel (sym (R≃-∙ (rel q) s)) ⟩
      rel (path (isTransR _ _ _ (rel q) s))
        ≡⟨ retEq R≃ _ ⟩
      isTransR _ _ _ (rel q) s
        ∎

    eq//-∙ : {a b c : A} (q : f a ≡ f b) (s : R b c)
      → PathP (λ j → Path (A // isTransR) [ a ] (eq// s j)) (eq// (rel q)) (eq// (rel (q ∙ path s)))
    eq//-∙ q s = comp// (rel q) s ▷ ap eq// (sym (rel-∙ q s))

  rec// : A // isTransR → B
  rec// = GQ.rec isTransR isGroupoidB f path λ r s → compPath-filler _ _ ▷ sym (R≃-∙ r s)

  encode : (a : A) (y : A // isTransR) → [ a ] ≡ y → f a ≡ rec// y
  encode a y = ap rec//

  decode : (a : A) (y : A // isTransR) → f a ≡ rec// y → [ a ] ≡ y
  decode a =
    GQ.elimSet
      isTransR
      {B = λ y → f a ≡ rec// y → [ a ] ≡ y}
      (λ _ → isSetΠ λ _ → squash// _ _)
      (λ _ q → eq// (rel q))
      (λ s → funExtNonDep λ {q₀} p → eq//-∙ q₀ s ▷ ap (λ q → eq// (rel q)) (PathP→∙ p))

  decode-refl : (a : A) → decode a [ a ] refl ≡ refl
  decode-refl a = invEq (compl≡Equiv p p refl) (p∙p ∙ rUnit p)
    where
      p = eq// {Rt = isTransR} (rel refl)
      p∙p : p ∙ p ≡ p
      p∙p = PathP→∙ (eq//-∙ refl (rel refl) ▷ ap (λ q → eq// {Rt = isTransR} (rel q)) (sym (lUnit _) ∙ secEq R≃ refl))

  encodeDecode : (a : A) (y : A // isTransR) (q : f a ≡ rec// y) → encode a y (decode a y q) ≡ q
  encodeDecode a = GQ.elimProp isTransR (λ _ → isPropΠ λ _ → isGroupoidB _ _ _ _) λ _ → secEq R≃

  decodeEncode : (a : A) (y : A // isTransR) (p : [ a ] ≡ y) → decode a y (encode a y p) ≡ p
  decodeEncode a y p =
    decode a y (encode a y p)
      ≡⟨ sym (PathP→∙ λ i → decode a (p i) (λ j → rec// (p (i ∧ j)))) ⟩
    decode a [ a ] refl ∙ p
      ≡⟨ ap (_∙ p) (decode-refl a) ⟩
    refl ∙ p
      ≡⟨ sym (lUnit p) ⟩
    p
      ∎

  encode≃ : (a : A) (y : A // isTransR) → ([ a ] ≡ y) ≃ (f a ≡ rec// y)
  encode≃ a y = isoToEquiv (iso (encode a y) (decode a y) (encodeDecode a y) (decodeEncode a y))

  effective : (a b : A) → ([ a ] ≡ [ b ]) ≃ R a b
  effective a b = encode≃ a [ b ] ∙ₑ R≃ ⁻¹ₑ

  isEmbeddingRec// : isEmbedding rec//
  isEmbeddingRec// = GQ.elimProp isTransR (λ _ → isPropΠ λ _ → isPropIsEquiv _) λ a y → encode≃ a y .snd

  module _ (isSurjectionF : isSurjection f) where

    isSurjectionRec// : isSurjection rec//
    isSurjectionRec// b = PT.map (λ (a , q) → [ a ] , q) (isSurjectionF b)

    quotSurjectionEquiv : A // isTransR ≃ B
    quotSurjectionEquiv = rec// , isEmbedding×isSurjection→isEquiv (isEmbeddingRec// , isSurjectionRec//)
