---
title: Boolean Algebra
---

## Preamble

```agda
{-# OPTIONS --cubical --safe #-}

module BooleanAlgebra where

open import Cubical.Core.Everything hiding (_∧_; _∨_)

private
  variable
    ℓ : Level
```

## Definition

```agda
record BooleanAlgebraStr (A : Type ℓ) : Type ℓ where
  field
    _∧_ : A → A → A
    _∨_ : A → A → A
    ⊤   : A
    ⊥   : A
    ¬_  : A → A

    ∧-assoc : (x y z : A) → x ∧ (y ∧ z) ≡ (x ∧ y) ∧ z
    ∨-assoc : (x y z : A) → x ∨ (y ∨ z) ≡ (x ∨ y) ∨ z

    ∧-comm  : (x y   : A) → x ∧ y ≡ y ∧ x
    ∨-comm  : (x y   : A) → x ∨ y ≡ y ∨ x

    ∧-absorb : (x y : A) → x ∧ (y ∨ x) ≡ x
    ∨-absorb : (x y : A) → x ∨ (y ∧ x) ≡ x

    ⊤-id : (x : A) → x ∧ ⊤ ≡ x
    ⊥-id : (x : A) → x ∨ ⊥ ≡ x

    ∧-dist : (x y z : A) → x ∧ (y ∨ z) ≡ (x ∧ y) ∨ (x ∧ z)
    ∨-dist : (x y z : A) → x ∨ (y ∧ z) ≡ (x ∨ y) ∧ (x ∨ z)

    ∧-inv : (x : A) → x ∧ (¬ x) ≡ ⊥
    ∨-inv : (x : A) → x ∨ (¬ x) ≡ ⊤
```

```agda
BooleanAlgebra : (ℓ : Level) → Type (ℓ-suc ℓ)
BooleanAlgebra ℓ = Σ[ A ∈ Type ℓ ] BooleanAlgebraStr A
```
