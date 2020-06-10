
## Preamble

```agda
{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

module Ring where

private
  variable
    ℓ : Level
```

## Definition of a ring

```agda
record RingStr (A : Type ℓ) : Type ℓ where

  field
    _+_ : A → A → A
    𝟎   : A
    -_  : A → A
    _*_ : A → A → A
    𝟏   : A

    -- (A, +, 𝟎) forms a commutative group.
    +-assoc  : (x y z : A) → (x + y) + z ≡ x + (y + z)
    𝟎-unit-l : (x     : A) → 𝟎 + x ≡ x
    +-inv    : (x     : A) → x + (- x) ≡ 𝟎
    +-comm   : (x y   : A) → x + y ≡ y + x

    -- (A , *, 𝟏) forms a monoid.
    *-assoc  : (x y z : A) → (x * y) * z ≡ x * (y * z)
    𝟏-unit-l : (x     : A) → 𝟏 * x ≡ x
    𝟏-unit-r : (x     : A) → x * 𝟏 ≡ x

    -- Distributivity.
    distr-left  : (x y z : A) → x * (y + z) ≡ (x * y) + (x * z)
    distr-right : (x y z : A) → (y + z) * x ≡ (y * x) + (z * x)

    A-set : isSet A
```

```agda
Ring : (ℓ : Level) → Type (ℓ-suc ℓ)
Ring ℓ = Σ[ A ∈ Type ℓ ] RingStr A
```

## Boolean rings

```agda
isBoolean : {A : Type ℓ} → RingStr A → Type ℓ
isBoolean {A = A} rs = (x y : A) → x * x ≡ x
  where
    open RingStr rs using (_*_)
```

```agda
BoolRing : (ℓ : Level) → Type (ℓ-suc ℓ)
BoolRing ℓ = Σ[ A ∈ Type ℓ ] Σ[ rs ∈ RingStr A ] isBoolean rs
```
