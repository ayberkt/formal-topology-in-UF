```
{-# OPTIONS --cubical --safe #-}

module Basis where

import Cubical.Core.Everything                as CE
import Cubical.Data.Sigma                     as DΣ
import Cubical.Data.Sum                       as DS
import Cubical.Foundations.Prelude            as FP
import Cubical.Foundations.Equiv              as FE
import Cubical.Functions.Logic                as FL
import Cubical.Foundations.Structure          as FS
import Cubical.Foundations.HLevels            as FH
import Cubical.Foundations.Isomorphism        as FI
import Cubical.Foundations.Equiv.HalfAdjoint  as HAE
import Cubical.Functions.FunExtEquiv          as FEE
import Cubical.Foundations.Function           as FF

open import Cubical.Foundations.Univalence public using (ua)

open CE  public using     (_≡_; Type; Σ; Σ-syntax; _,_; _≃_; equivFun; isEquiv; Level;
                           ℓ-max; ℓ-zero; ℓ-suc)
open DΣ  public using     (Σ≡Prop; ΣPathTransport→PathΣ; PathΣ→ΣPathTransport; _×_; _,_)
                renaming  (fst to π₀; snd to π₁)
open DS  public using     (inl; inr; _⊎_)
open FP  public using     (funExt; funExt⁻; subst; isContr; isProp; isPropIsProp; isSet;
                           isProp→isSet; cong; refl; sym; _≡⟨_⟩_; _∎; transport;
                           transportRefl; J; JRefl)
open FE  public using     (idEquiv; invEquiv; secEq; retEq; fiber; equivToIso;
                           isPropIsEquiv)
open FL  public using     ( _⇔_ ; _⇒_ ; ⇔toPath ; _⊓_ ; ∃[∶]-syntax; ∀[∶]-syntax; ∀[]-syntax; ¬_)
                renaming  (isProp⟨⟩ to isProp[])
open FS  public using     () renaming (⟨_⟩ to [_])
open FH public using      (hProp; isSetHProp; isPropIsSet; isPropΣ; isOfHLevel;
                           isOfHLevelΠ; isOfHLevelΣ; isOfHLevelSuc; isSetΣ;
                           isSetΠ; isSetΠ2; isPropΠ; isPropΠ2; isPropΠ3)
open FI  public using     (isoToPath; isoToEquiv; iso; section; retract; Iso)
open FF  public using     (_∘_) renaming (idfun to id)
open FEE public using     (funExtEquiv; funExt₂; funExt₂Equiv; funExt₂Path)
open HAE public using     (isHAEquiv; equiv→HAEquiv)

open import Cubical.Data.Nat  using (ℕ; _+_) renaming (suc to sucℕ; zero to zeroℕ)
open import Cubical.Data.Nat.Properties using (injSuc; snotz; +-comm)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty using (rec; ⊥)
open import Cubical.Data.List using (List; length; _∷_; [])
open import Cubical.Data.Fin  using (Fin)
open import Cubical.Relation.Nullary.DecidableEq using (Discrete→isSet)
open import Cubical.Relation.Nullary using (Discrete; yes; no; Dec)
```

```
variable
  ℓ ℓ′ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₀′ ℓ₁′ ℓ₂′ ℓ₀′′ ℓ₁′′ ℓ₂′′ : Level

variable
  A    : Type ℓ₀
  B    : A → Type ℓ₀
  A₀   : Type ℓ₁

_↔_ : (A : Type ℓ) (B : Type ℓ′) → Type _
A ↔ B = (A → B) × (B → A)

↔-to : {A : Type ℓ} {B : Type ℓ′} → A ↔ B → A → B
↔-to (to , _) = to

↔-from : {A : Type ℓ} {B : Type ℓ′} → A ↔ B → B → A
↔-from (_ , from) = from
```

## Levels

Escardó-style level notation.

```agda
infixr 5 _∨_

Universe : Type₀
Universe = Level

variable
  𝒰 𝒱 𝒲 𝓤 𝓥 𝓦 𝓤′ 𝓥′ 𝓦′ : Universe

_∨_ : Level → Level → Level
ℓ₀ ∨ ℓ₁ = ℓ-max ℓ₀ ℓ₁

infix 6 _⁺

_⁺ : Level → Level
ℓ ⁺ = ℓ-suc ℓ

infix 6 _̇

_̇ : (ℓ : Level) → Type (ℓ ⁺)
ℓ ̇ = Type ℓ

𝓤₀ : Level
𝓤₀ = ℓ-zero

𝓤₁ : Level
𝓤₁ = 𝓤₀ ⁺
```

## The unit type

```
data Unit (ℓ : Level) : Type ℓ where
  tt : Unit ℓ

Unit-prop : {ℓ : Level} → isProp (Unit ℓ)
Unit-prop tt tt = refl
```

## Bottom

```
data 𝟘 (ℓ : Level) : Type ℓ where

bot : (ℓ : Level) → hProp ℓ
bot ℓ = 𝟘 ℓ , λ ()
```

## Booleans

```agda
data Bool (ℓ : Level) : Type ℓ where
  true  : Bool ℓ
  false : Bool ℓ
```

```agda
true≠false : _≡_ {ℓ = 𝓤} true false → ⊥
true≠false p = subst (λ { true → Unit 𝓤₀ ; false → ⊥ }) p tt
```

```agda
_=b=_ : Discrete (Bool 𝓤)
true  =b= true  = yes refl
true  =b= false = no true≠false
false =b= true  = no (true≠false ∘ sym)
false =b= false = yes refl
```

```agda
Bool-set : isSet (Bool 𝓤)
Bool-set = Discrete→isSet _=b=_
```

```agda
if_then_else_ : {A : Type ℓ₀} → Bool ℓ₁ → A → A → A
if true  then x else y = x
if false then x else y = y
```

## Propositions

```
is-true-prop : (P : hProp ℓ) → isProp [ P ]
is-true-prop (P , P-prop) = P-prop
```

```
∃_ : {A : Type ℓ₀} → (A → hProp ℓ₁) → Type _
∃_ {A = A} P = Σ[ x ∈ A ] [ P x ]
```

## Extensional equality

```
_~_ : (f g : (x : A) → B x) → Type _
_~_ {A = A} f g = (x : A) → f x ≡ g x
```

## Powerset

```
𝒫 : Type ℓ → Type _
𝒫 {ℓ} A = A → hProp ℓ

_∈_ : A → 𝒫 A → hProp _
x ∈ U = U x

∈-prop : {A : Type ℓ} {x : A} → (U : 𝒫 A) → isProp [ x ∈ U ]
∈-prop {x = x} U = is-true-prop (x ∈ U)

𝒫-set : (A : Type ℓ) → isSet (𝒫 A)
𝒫-set A = isSetΠ λ _ → isSetHProp

_^c : {A : Type ℓ} → 𝒫 A → 𝒫 A
U ^c = λ x → ¬ (x ∈ U)

variable
  U V : 𝒫 A

_⊆⊆_ : {A : Type ℓ} → (A → Type ℓ₀) → (A → Type ℓ₁) → Type _
_⊆⊆_ {A = A} U V =  (x : A) → U x → V x

_⊆_ : {A : Type ℓ} → 𝒫 A → 𝒫 A → hProp ℓ
_⊆_ {A = A} U V = ((λ - → [ U - ]) ⊆⊆ (λ - → [ V - ])) , prop
  where
    prop : isProp ((x : A) → [ U x ] → [ V x ])
    prop = isPropΠ λ x → isPropΠ λ _ → is-true-prop (V x)

⊆-antisym : [ U ⊆ V ] → [ V ⊆ U ] → U ≡ V
⊆-antisym {U = U} {V} U⊆V V⊆V = funExt (λ x → ⇔toPath (U⊆V x) (V⊆V x))

∅ : 𝒫 A
∅  _ = bot _

entire : {A : Type ℓ} → 𝒫 A
entire {ℓ = ℓ} _ = Unit ℓ , Unit-prop

_∩_ : 𝒫 A → 𝒫 A → 𝒫 A
_∩_ {A = A} U V = λ x → ([ U x ] × [ V x ]) , prop x
  where
    prop : (x : A) → isProp ([ U x ] × [ V x ])
    prop x = isPropΣ (is-true-prop (x ∈ U)) λ _ → is-true-prop (V x)
```

```agda
U∩U^c=∅ : {A : Type ℓ} → (U : 𝒫 A) → Σ[ x ∈ A ] [ x ∈ (U ∩ (U ^c)) ] → Cubical.Data.Empty.⊥
U∩U^c=∅ U (x , (x∈U , x∈U^c)) = rec (x∈U^c x∈U)
```

## Family

```
Fam : (ℓ₀ : Level) → Type ℓ₁ → Type _
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

_⊆fam_ : {A : Type ℓ} → Fam ℓ₁ A → Fam ℓ₁ A → Type (ℓ-max ℓ ℓ₁)
_⊆fam_ {A = A} U V = (x : A) → x ε U → x ε V

-- Composition of a family with a function.
_⟨$⟩_ : {X : Type ℓ₀} {Y : Type ℓ₁} → (g : X → Y) → (ℱ : Fam ℓ₂ X) → Fam ℓ₂ Y
g ⟨$⟩ ℱ = (index ℱ) , g ∘ (_$_ ℱ)

fmap : {X : Type ℓ₀} {Y : Type ℓ₁} → (g : X → Y) → (ℱ : Fam ℓ₂ X) → Fam ℓ₂ Y
fmap = _⟨$⟩_

syntax fmap (λ x → e) ℱ = ⁅ e ∣ x ε ℱ ⁆

compr-∶-syntax : {X : Type ℓ₀} → (I : Type ℓ₂) → (I → X) → Fam ℓ₂ X
compr-∶-syntax I f = (I , f)

syntax compr-∶-syntax I (λ i → e) = ⁅ e ∣ i ∶ I ⁆

-- Forall quantification for families.
fam-forall : {X : Type ℓ₀} (ℱ : Fam ℓ₂ X) → (X → hProp ℓ₁) → hProp _
fam-forall {X = X} ℱ P = ((x : X) → x ε ℱ → [ P x ]) , prop
  where
    prop : isProp ((x : X) → x ε ℱ → [ P x ])
    prop = isPropΠ λ x → isPropΠ λ _ → is-true-prop (P x)

syntax fam-forall ℱ (λ x → P) = ∀[ x ε ℱ ] P

-- Familification of a given powerset.
⟪_⟫ : {A : Type ℓ₀} → (A → hProp ℓ₁) → Fam _ A
⟪_⟫ {A = A} U = (Σ[ x ∈ A ] [ U x ]) , π₀

lookup : {A : Type ℓ₀} → (xs : List A) → Fin (length xs) → A
lookup []       (_      , zeroℕ  , p) = rec (snotz p)
lookup []       (_      , sucℕ i , p) = rec (snotz p)
lookup (x ∷ xs) (zeroℕ  , _)          = x
lookup (x ∷ xs) (sucℕ i , p)          = lookup xs (i , pred-≤-pred p)

famFromList : {A : Type ℓ₀} → List A → Fam _ A
famFromList xs = Fin (length xs) , lookup xs

_×f_ : {A : Type ℓ₀} → Fam ℓ₂ A → Fam ℓ₂′ A → Fam (ℓ-max ℓ₂ ℓ₂′) (A × A)
_×f_ (I , f) (J , g) = I × J , (λ { (i , j) → f i , g j })

_∪f_ : {A : 𝓤 ̇} → Fam 𝓦 A → Fam 𝓦 A → Fam 𝓦 A
_∪f_ (I , f) (J , g) = I ⊎ J , λ { (inl i) → f i ; (inr j) → g j }

⁅_,_⁆ : {A : 𝓤 ̇} {𝓦 : Universe} → A → A → Fam 𝓦 A
⁅_,_⁆ {𝓦 = 𝓦} x y = Bool 𝓦 , λ b → if b then x else y
```

## Truncation

```
data ∥_∥ (A : Type ℓ) : Type ℓ where
  ∣_∣    : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y

∥∥-prop : (A : Type ℓ) → isProp ∥ A ∥
∥∥-prop _ = squash

∥_∥Ω : (A : 𝓤 ̇) → hProp 𝓤
∥ A ∥Ω = ∥ A ∥ , ∥∥-prop A

∥∥-rec : {X : Type ℓ} {Y : Type ℓ₀} → isProp Y → (X → Y) → ∥ X ∥ → Y
∥∥-rec Y-prop f ∣ x ∣                = f x
∥∥-rec Y-prop f (squash ∣x∣₀ ∣x∣₁ i) =
  Y-prop (∥∥-rec Y-prop f ∣x∣₀) (∥∥-rec Y-prop f ∣x∣₁) i

∥∥-× : {A : Type ℓ₀} {B : Type ℓ₁} → ∥ A ∥ → ∥ B ∥ → ∥ A × B ∥
∥∥-× {A = A} {B} p q = ∥∥-rec (∥∥-prop (A × B)) NTS p
  where
    NTS′ : B → A → ∥ A × B ∥
    NTS′ y x = ∣ x , y ∣

    NTS : A → ∥ A × B ∥
    NTS = ∥∥-rec (isPropΠ (λ _ → ∥∥-prop (A × B))) NTS′ q
```
