```
{-# OPTIONS --cubical --safe #-}

module Basis where

open import Function using (_∘_; id)
open import Level    public

import Cubical.Core.Everything                as CE
import Cubical.Data.Sigma                     as DS
import Cubical.Foundations.Prelude            as FP
import Cubical.Foundations.Equiv              as FE
import Cubical.Foundations.Logic              as FL
import Cubical.Foundations.HLevels            as FH
import Cubical.Foundations.Isomorphism        as FI
import Cubical.Foundations.Equiv.HalfAdjoint  as HAE
import Cubical.Functions.FunExtEquiv          as FEE

open import Cubical.Foundations.Univalence public using (ua)

open CE  public using     (_≡_; Type; Σ; Σ-syntax; _,_; _≃_; equivFun; isEquiv)
open DS  public using     (ΣProp≡; sigmaPath→pathSigma; pathSigma→sigmaPath; _×_; _,_)
                renaming  (fst to π₀; snd to π₁)
open FP  public using     (funExt; subst; isContr; isProp; isPropIsProp; isSet;
                           isProp→isSet; cong; refl; sym; _≡⟨_⟩_; _∎; transport;
                           transportRefl; J; JRefl)
open FE  public using     (idEquiv; invEquiv; secEq; retEq; fiber; equivToIso;
                           isPropIsEquiv)
open FL  public using     ( _⇔_ ; _⇒_ ; ⇔toPath ; _⊓_ ; [_] )
open FH  public using     (hProp; isSetHProp; isPropIsSet; isPropΣ; isOfHLevelSuc; isSetΣ;
                           isSetΠ; isPropΠ; isPropΠ2; isPropΠ3)
open FI  public using     (isoToPath; isoToEquiv; iso; section; retract; Iso)
open FEE public using     (funExtEquiv; funExt₂; funExt₂Equiv; funExt₂Path)
open HAE public using     (isHAEquiv; equiv→HAEquiv)
```

```
variable
  ℓ ℓ′ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₀′ ℓ₁′ ℓ₂′ ℓ₀′′ ℓ₁′′ ℓ₂′′ : Level

variable
  A    : Type ℓ₀
  B    : A → Type ℓ₀
  A₀   : Type ℓ₁
```

## The unit type

```
data Unit (ℓ : Level) : Type ℓ where
  tt : Unit ℓ

Unit-prop : {ℓ : Level} → isProp (Unit ℓ)
Unit-prop tt tt = refl
```

## Propositions

```
is-true-prop : (P : hProp ℓ) → isProp [ P ]
is-true-prop (P , P-prop) = P-prop
```

```
∃_ : {A : Type ℓ₀} → (A → hProp ℓ₁) → Type (ℓ₀ ⊔ ℓ₁)
∃_ {A = A} P = Σ[ x ∈ A ] [ P x ]
```

## Extensional equality

```
_~_ : (f g : (x : A) → B x) → Type _
_~_ {A = A} f g = (x : A) → f x ≡ g x
```

## Powerset

```
𝒫 : Type ℓ → Type (suc ℓ)
𝒫 {ℓ} A = A → hProp ℓ

_∈_ : A → 𝒫 A → hProp _
x ∈ U = U x

∈-prop : {A : Type ℓ} {x : A} → (U : 𝒫 A) → isProp [ x ∈ U ]
∈-prop {x = x} U = is-true-prop (x ∈ U)

𝒫-set : (A : Type ℓ) → isSet (𝒫 A)
𝒫-set A = isSetΠ λ _ → isSetHProp

variable
  U V : 𝒫 A

_⊆⊆_ : {A : Type ℓ} → (A → Type ℓ₀) → (A → Type ℓ₁) → Type (ℓ ⊔ ℓ₀ ⊔ ℓ₁)
_⊆⊆_ {A = A} U V =  (x : A) → U x → V x

_⊆_ : {A : Type ℓ} → 𝒫 A → 𝒫 A → hProp ℓ
_⊆_ {A = A} U V = ((λ - → [ U - ]) ⊆⊆ (λ - → [ V - ])) , prop
  where
    prop : isProp ((x : A) → [ U x ] → [ V x ])
    prop = isPropΠ λ x → isPropΠ λ _ → is-true-prop (V x)

⊆-antisym : [ U ⊆ V ] → [ V ⊆ U ] → U ≡ V
⊆-antisym {U = U} {V} U⊆V V⊆V = funExt (λ x → ⇔toPath (U⊆V x) (V⊆V x))

_∩_ : 𝒫 A → 𝒫 A → 𝒫 A
_∩_ {A = A} U V = λ x → ([ U x ] × [ V x ]) , prop x
  where
    prop : (x : A) → isProp ([ U x ] × [ V x ])
    prop x = isPropΣ (is-true-prop (x ∈ U)) λ _ → is-true-prop (V x)
```

## Family

```
Fam : (ℓ₀ : Level) → Type ℓ₁ → Type (suc ℓ₀ ⊔ ℓ₁)
Fam ℓ₀ A = Σ (Set ℓ₀) (λ I → I → A)

index : Fam ℓ₁ A → Type ℓ₁
index (I , _) = I

-- Application of a family over X to an index.
_$_ : (ℱ : Fam ℓ₀ A) → index ℱ → A
_$_ (_ , f) = f

infixr 7 _$_

-- Membership for families.
_ε_ : A → Fam ℓ₁ A → Type _
x ε (_ , f) = fiber f x

-- Composition of a family with a function.
_⟨$⟩_ : {X : Type ℓ₀} {Y : Type ℓ₁} → (g : X → Y) → (ℱ : Fam ℓ₂ X) → Fam ℓ₂ Y
g ⟨$⟩ ℱ = (index ℱ) , g ∘ (_$_ ℱ)

fmap : {X : Type ℓ₀} {Y : Type ℓ₁} → (g : X → Y) → (ℱ : Fam ℓ₂ X) → Fam ℓ₂ Y
fmap = _⟨$⟩_

syntax fmap (λ x → e) ℱ = ⁅ e ∣ x ε ℱ ⁆

fmap′ : {X : Type ℓ₀} → (I : Type ℓ₂) → (I → X) → Fam ℓ₂ X
fmap′ I f = (I , f)

syntax fmap′ I (λ i → e) = ⁅ e ∣ i ∶ I ⁆

-- Forall quantification for families.
fam-forall : {X : Type ℓ₀} (ℱ : Fam ℓ₂ X) → (X → hProp ℓ₁) → hProp (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
fam-forall {X = X} ℱ P = ((x : X) → x ε ℱ → [ P x ]) , prop
  where
    prop : isProp ((x : X) → x ε ℱ → [ P x ])
    prop = isPropΠ λ x → isPropΠ λ _ → is-true-prop (P x)

syntax fam-forall ℱ (λ x → P) = ∀[ x ε ℱ ] P

-- Familification of a given powerset.
⟪_⟫ : {A : Type ℓ₀} → (A → hProp ℓ₁) → Fam (ℓ₀ ⊔ ℓ₁) A
⟪_⟫ {A = A} U = (Σ[ x ∈ A ] [ U x ]) , π₀
```


## Truncation

```
data ∥_∥ (A : Type ℓ) : Type ℓ where
  ∣_∣    : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y

∥∥-prop : (A : Type ℓ) → isProp ∥ A ∥
∥∥-prop _ = squash

∥∥-rec : {X Y : Type ℓ} → isProp Y → (X → Y) → ∥ X ∥ → Y
∥∥-rec Y-prop f ∣ x ∣                = f x
∥∥-rec Y-prop f (squash ∣x∣₀ ∣x∣₁ i) =
  Y-prop (∥∥-rec Y-prop f ∣x∣₀) (∥∥-rec Y-prop f ∣x∣₁) i
```
