module En.Prelude.Base where

open import Cubical.Foundations.Prelude
  renaming ( congS to ap
           ; cong to apd
           ; congP to apP
           ; subst to tpt
           ; _∙₂_ to _∙h_
           ) public
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Path public
open import Cubical.Foundations.GroupoidLaws
  renaming (cong-∙ to ap-∙) public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.Structure public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Function public
open import Cubical.Data.Sigma public
open import Cubical.Data.Nat hiding ( elim ) public
open import Cubical.Data.Nat.Properties public
import Cubical.Data.SumFin
import Cubical.Data.Fin
-- finite types as iterated sums
module SumFin = Cubical.Data.SumFin hiding ( elim ; ⊤ ; tt ; _⊎_ ; inl ; inr )
-- finite types as bounded naturals
module Finℕ = Cubical.Data.Fin hiding ( elim ; _/_ )
open import Cubical.Relation.Nullary.Base public
open import Cubical.Data.Nat.Order public
open import Cubical.Data.Empty hiding ( elim ; rec ) public
open import Cubical.Data.Nat.Order.Inductive public
open import Cubical.Data.Nat.Order public
open import Cubical.Relation.Binary public

infix 15 _≅_
_≅_ = Iso

-- forward and backward maps of an equivalence
–> : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → A → B
–> = equivFun

<– : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → B → A
<– = invEq

-- inverse of an equivalence
infix 40 _⁻¹ₑ
_⁻¹ₑ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → B ≃ A
_⁻¹ₑ = invEquiv

postulate
    sorry : ∀ {ℓ : Level} {A : Type ℓ} → A
