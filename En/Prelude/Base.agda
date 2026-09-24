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
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Function public
open import Cubical.Data.Sigma public
open import Cubical.Data.Nat hiding ( elim ) public
open import Cubical.Data.Nat.Properties public
open import Cubical.Data.Fin hiding ( elim ; _/_ ) public
open import Cubical.Relation.Nullary.Base public
open import Cubical.Data.Nat.Order public
open import Cubical.Data.Empty hiding ( elim ; rec ) public
open import Cubical.Data.Nat.Order.Inductive public
open import Cubical.Data.Nat.Order public
open import Cubical.Relation.Binary public
open import Cubical.Data.List hiding ( elim ; rec ) public



infix 15 _≅_
_≅_ = Iso
