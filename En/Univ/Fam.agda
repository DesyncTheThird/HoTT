module En.Univ.Fam where

open import En.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.SIP
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Implicit
open import Cubical.Reflection.RecordEquiv
open import Cubical.Structures.Axioms
open import Cubical.Structures.Constant
open import Cubical.Structures.Function
open import Cubical.Structures.Pointed
open import En.Univ.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

-- families over a subuniverse

LabelStructure : Type ℓ'' → Type ℓ → Type (ℓ-max ℓ ℓ'')
LabelStructure A X = X → A

FamStructure : SubUniv ℓ ℓ' → Type ℓ'' → Type ℓ → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
FamStructure 𝒮 A = AxiomsStructure (LabelStructure A) (λ X _ → 𝒮 .fst X)

Fam : SubUniv ℓ ℓ' → Type ℓ'' → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) ℓ') ℓ'')
Fam {ℓ} 𝒮 A = TypeWithStr ℓ (FamStructure 𝒮 A)

-- path spaces are relabellings

module FamPath (𝒮 : SubUniv ℓ ℓ') (A : Type ℓ'') where

  private
    P = 𝒮 .fst
    isPropP = 𝒮 .snd

  labels : (X : Fam 𝒮 A) → ⟨ X ⟩ → A
  labels X = X .snd .fst

  shape : Fam 𝒮 A → TypeWithStr ℓ P
  shape X = ⟨ X ⟩ , X .snd .snd

  Fam≃Σ : Fam 𝒮 A ≃ (Σ[ X ∈ TypeWithStr ℓ P ] (⟨ X ⟩ → A))
  Fam≃Σ = isoToEquiv i
    where
      open Iso
      i : Iso (Fam 𝒮 A) (Σ[ X ∈ TypeWithStr ℓ P ] (⟨ X ⟩ → A))
      i .fun (X , f , p) = (X , p) , f
      i .inv ((X , p) , f) = X , f , p
      i .sec _ = refl
      i .ret _ = refl

  isOfHLevelFam : (n : HLevel) → isOfHLevel n (TypeWithStr ℓ P) → isOfHLevel n A → isOfHLevel n (Fam 𝒮 A)
  isOfHLevelFam n hP hA = isOfHLevelRespectEquiv n (Fam≃Σ ⁻¹ₑ) (isOfHLevelΣ n hP λ _ → isOfHLevelΠ n λ _ → hA)

  record Cover (X Y : Fam 𝒮 A) : Type (ℓ-max ℓ ℓ'') where
    constructor cover
    field
      equiv : ⟨ X ⟩ ≃ ⟨ Y ⟩
      label : (x : ⟨ X ⟩) → labels X x ≡ labels Y (–> equiv x)

  open Cover public

  unquoteDecl CoverIsoΣ = declareRecordIsoΣ CoverIsoΣ (quote Cover)

  Cover≡ : {X Y : Fam 𝒮 A} {c c' : Cover X Y}
    → (p : –> (c .equiv) ≡ –> (c' .equiv))
    → PathP (λ i → (x : ⟨ X ⟩) → labels X x ≡ labels Y (p i x)) (c .label) (c' .label)
    → c ≡ c'
  Cover≡ p q = ap (CoverIsoΣ .Iso.inv) (ΣPathP (equivEq p , q))

  reflCode : (X : Fam 𝒮 A) → Cover X X
  reflCode X .equiv = idEquiv _
  reflCode X .label _ = refl

  infixr 30 _∙ᶜ_

  _∙ᶜ_ : {X Y Z : Fam 𝒮 A} → Cover X Y → Cover Y Z → Cover X Z
  (c ∙ᶜ d) .equiv = c .equiv ∙ₑ d .equiv
  (c ∙ᶜ d) .label x = c .label x ∙ d .label (–> (c .equiv) x)

  opaque
    Path≃Cover : (X Y : Fam 𝒮 A) → (X ≡ Y) ≃ Cover X Y
    Path≃Cover X Y =
      X ≡ Y
        ≃⟨ isoToEquiv (invIso ΣPathIsoPathΣ) ⟩
      Σ[ p ∈ ⟨ X ⟩ ≡ ⟨ Y ⟩ ] PathP (λ i → FamStructure 𝒮 A (p i)) (X .snd) (Y .snd)
        ≃⟨ Σ-cong-equiv-snd (λ _ → isoToEquiv (invIso ΣPathIsoPathΣ)) ⟩
      Σ[ p ∈ ⟨ X ⟩ ≡ ⟨ Y ⟩ ]
        Σ[ _ ∈ PathP (λ i → p i → A) (labels X) (labels Y) ] PathP (λ i → P (p i)) (X .snd .snd) (Y .snd .snd)
        ≃⟨ Σ-cong-equiv-snd (λ _ → Σ-contractSnd λ _ → isOfHLevelPathP' 0 (isPropP _) _ _) ⟩
      Σ[ p ∈ ⟨ X ⟩ ≡ ⟨ Y ⟩ ] PathP (λ i → p i → A) (labels X) (labels Y)
        ≃⟨ Σ-cong-equiv-snd (λ _ → funExtNonDepEquiv ⁻¹ₑ ∙ₑ heteroHomotopy≃Homotopy) ⟩
      Σ[ p ∈ ⟨ X ⟩ ≡ ⟨ Y ⟩ ] ((x : ⟨ X ⟩) → labels X x ≡ labels Y (transport p x))
        ≃⟨ Σ-cong-equiv univalence (λ _ → idEquiv _) ⟩
      Σ[ e ∈ ⟨ X ⟩ ≃ ⟨ Y ⟩ ] ((x : ⟨ X ⟩) → labels X x ≡ labels Y (–> e x))
        ≃⟨ isoToEquiv (invIso CoverIsoΣ) ⟩
      Cover X Y
        ■

  encode : (X Y : Fam 𝒮 A) → X ≡ Y → Cover X Y
  encode X Y = –> (Path≃Cover X Y)

  decode : (X Y : Fam 𝒮 A) → Cover X Y → X ≡ Y
  decode X Y = <– (Path≃Cover X Y)

  decodeEncode : (X Y : Fam 𝒮 A) (p : X ≡ Y) → decode X Y (encode X Y p) ≡ p
  decodeEncode X Y = retEq (Path≃Cover X Y)

  encodeDecode : (X Y : Fam 𝒮 A) (c : Cover X Y) → encode X Y (decode X Y c) ≡ c
  encodeDecode X Y = secEq (Path≃Cover X Y)

  encodeInj : (X Y : Fam 𝒮 A) {p q : X ≡ Y} → encode X Y p ≡ encode X Y q → p ≡ q
  encodeInj X Y = <– (congEquiv (Path≃Cover X Y))

  -- encode computes
  transportLabel : {X Y : Fam 𝒮 A} (p : X ≡ Y) (x : ⟨ X ⟩)
    → labels X x ≡ labels Y (transport (λ i → ⟨ p i ⟩) x)
  transportLabel p x i = labels (p i) (transport-filler (λ j → ⟨ p j ⟩) x i)

  transportLabel-∙ : {X Y Z : Fam 𝒮 A} (p : X ≡ Y) (q : Y ≡ Z)
    → PathP (λ i → (x : ⟨ X ⟩) → labels X x ≡ labels Z (substComposite ⟨_⟩ p q x i))
            (transportLabel (p ∙ q))
            (λ x → transportLabel p x ∙ transportLabel q (transport (λ i → ⟨ p i ⟩) x))
  transportLabel-∙ p q = funExt (λ _ → lUnit _) ◁ λ i x →
    (λ j → transportLabel p x (i ∧ j))
      ∙ transportLabel (compPath-filler' p q (~ i)) (transport-filler (λ j → ⟨ p j ⟩) x i)

  opaque
    unfolding Path≃Cover

    encodeTransport : (X Y : Fam 𝒮 A) (p : X ≡ Y)
      → encode X Y p ≡ cover (pathToEquiv (λ i → ⟨ p i ⟩)) (transportLabel p)
    encodeTransport X Y p = refl

  encode-fst : (X Y : Fam 𝒮 A) (p : X ≡ Y) → encode X Y p .equiv ≡ pathToEquiv (λ i → ⟨ p i ⟩)
  encode-fst X Y p = ap equiv (encodeTransport X Y p)

  encodeRefl : (X : Fam 𝒮 A) → encode X X refl ≡ reflCode X
  encodeRefl X =
    encode X X refl
      ≡⟨ encodeTransport X X refl ⟩
    cover (pathToEquiv refl) (transportLabel (refl {x = X}))
      ≡⟨ Cover≡ (funExt transportRefl) (λ i x j → labels X (transp (λ _ → ⟨ X ⟩) (~ j ∨ i) x)) ⟩
    reflCode X
      ∎

  encode-∙ : {X Y Z : Fam 𝒮 A} (p : X ≡ Y) (q : Y ≡ Z)
    → encode X Z (p ∙ q) ≡ encode X Y p ∙ᶜ encode Y Z q
  encode-∙ {X} {Y} {Z} p q =
    encode X Z (p ∙ q)
      ≡⟨ encodeTransport X Z (p ∙ q) ⟩
    cover (pathToEquiv (λ i → ⟨ (p ∙ q) i ⟩)) (transportLabel (p ∙ q))
      ≡⟨ Cover≡ (funExt (substComposite ⟨_⟩ p q)) (transportLabel-∙ p q) ⟩
    cover (pathToEquiv (λ i → ⟨ p i ⟩) ∙ₑ pathToEquiv (λ i → ⟨ q i ⟩))
          (λ x → transportLabel p x ∙ transportLabel q (transport (λ i → ⟨ p i ⟩) x))
      ≡⟨ sym (cong₂ _∙ᶜ_ (encodeTransport X Y p) (encodeTransport Y Z q)) ⟩
    encode X Y p ∙ᶜ encode Y Z q
      ∎

  -- path space via SIP

  LabelEquivStr : StrEquiv (LabelStructure {ℓ = ℓ} A) (ℓ-max ℓ ℓ'')
  LabelEquivStr = FunctionEquivStr PointedEquivStr (ConstantEquivStr A)

  labelUnivalentStr : UnivalentStr (LabelStructure {ℓ = ℓ} A) LabelEquivStr
  labelUnivalentStr =
    functionUnivalentStr PointedEquivStr pointedUnivalentStr (ConstantEquivStr A) (constantUnivalentStr A)

  FamEquivStr : StrEquiv (FamStructure 𝒮 A) (ℓ-max ℓ ℓ'')
  FamEquivStr = AxiomsEquivStr LabelEquivStr (λ X _ → P X)

  famUnivalentStr : UnivalentStr (FamStructure 𝒮 A) FamEquivStr
  famUnivalentStr = axiomsUnivalentStr LabelEquivStr (λ X _ → isPropP X) labelUnivalentStr

  FamSIP : (X Y : Fam 𝒮 A) → (X ≃[ FamEquivStr ] Y) ≃ (X ≡ Y)
  FamSIP = SIP famUnivalentStr

  Cover≃StrEquiv : (X Y : Fam 𝒮 A) → Cover X Y ≃ (X ≃[ FamEquivStr ] Y)
  Cover≃StrEquiv X Y =
    Cover X Y
      ≃⟨ isoToEquiv CoverIsoΣ ⟩
    Σ[ e ∈ ⟨ X ⟩ ≃ ⟨ Y ⟩ ] ((x : ⟨ X ⟩) → labels X x ≡ labels Y (–> e x))
      ≃⟨ Σ-cong-equiv-snd label≃ ⟩
    Σ[ e ∈ ⟨ X ⟩ ≃ ⟨ Y ⟩ ] ({x : ⟨ X ⟩} {y : ⟨ Y ⟩} → –> e x ≡ y → labels X x ≡ labels Y y)
      ■
    where
      label≃ : (e : ⟨ X ⟩ ≃ ⟨ Y ⟩)
        → ((x : ⟨ X ⟩) → labels X x ≡ labels Y (–> e x))
        ≃ ({x : ⟨ X ⟩} {y : ⟨ Y ⟩} → –> e x ≡ y → labels X x ≡ labels Y y)
      label≃ e =
        ((x : ⟨ X ⟩) → labels X x ≡ labels Y (–> e x))
          ≃⟨ equivΠCod (λ x → Π-contractDom (isContrSingl (–> e x)) ⁻¹ₑ ∙ₑ curryEquiv) ⟩
        ((x : ⟨ X ⟩) (y : ⟨ Y ⟩) → –> e x ≡ y → labels X x ≡ labels Y y)
          ≃⟨ equivΠCod (λ _ → implicit≃Explicit ⁻¹ₑ) ∙ₑ implicit≃Explicit ⁻¹ₑ ⟩
        ({x : ⟨ X ⟩} {y : ⟨ Y ⟩} → –> e x ≡ y → labels X x ≡ labels Y y)
          ■
