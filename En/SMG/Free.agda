module En.SMG.Free where

open import En.Prelude
open import Cubical.Foundations.Equiv.Properties
import En.SMG as S hiding ( SMG* ; SMG*Fun )

-- free symmetric monoidal groupoids

module _ {A : Type ℓ} {F : Type ℓ'} (F* : S.SMG*Sq F) (η : A → F) where

  restrictSMG : {B : Type ℓ''} (B* : S.SMG*Sq B) → Σ (F → B) (S.SMG*Fun*Sq F* B*) → (A → B)
  restrictSMG B* g = g .fst ∘ η

  isFreeSMG : (ℓB : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓB))
  isFreeSMG ℓB = (B : Type ℓB) (B* : S.SMG*Sq B) → isEquiv (restrictSMG B*)

module _ {A : Type ℓ} {F : Type ℓ'} {F* : S.SMG*Sq F} {η : A → F} (isFreeF : isFreeSMG F* η ℓ') where

  freeEndo≡id : (g : Σ (F → F) (S.SMG*Fun*Sq F* F*)) → g .fst ∘ η ≡ η → g .fst ≡ idfun F
  freeEndo≡id g p = ap fst (<– (congEquiv {x = g} {y = idfun F , S.idSMG*Fun*Sq F*} (_ , isFreeF F F*)) p)

-- free symmetric monoidal groupoids are unique

module _ {A : Type ℓ} {F G : Type ℓ'}
  {F* : S.SMG*Sq F} {ηF : A → F} (isFreeF : isFreeSMG F* ηF ℓ')
  {G* : S.SMG*Sq G} {ηG : A → G} (isFreeG : isFreeSMG G* ηG ℓ')
  where

  freeSMG≃ : F ≃ G
  freeSMG≃ = isoToEquiv i
    where
      open Iso
      to : Σ (F → G) (S.SMG*Fun*Sq F* G*)
      to = invIsEq (isFreeF G G*) ηG
      from : Σ (G → F) (S.SMG*Fun*Sq G* F*)
      from = invIsEq (isFreeG F F*) ηF
      i : Iso F G
      i .fun = to .fst
      i .inv = from .fst
      i .sec = funExt⁻ (freeEndo≡id isFreeG
        (to .fst ∘ from .fst , S.compSMG*Fun*Sq (from .snd) (to .snd))
        (ap (to .fst ∘_) (secIsEq (isFreeG F F*) ηF) ∙ secIsEq (isFreeF G G*) ηG))
      i .ret = funExt⁻ (freeEndo≡id isFreeF
        (from .fst ∘ to .fst , S.compSMG*Fun*Sq (to .snd) (from .snd))
        (ap (from .fst ∘_) (secIsEq (isFreeF G G*) ηG) ∙ secIsEq (isFreeG F F*) ηF))
