---
title: Boolean Algebra
---

## Preamble

```agda
{-# OPTIONS --cubical --safe #-}

module BooleanAlgebra where

open import Cubical.Core.Everything     hiding (_∧_; _∨_)
open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.Sigma

open import Poset
open import Lattice renaming (pos to pos-of-lattice)

private
  variable
    ℓ ℓ₀ ℓ₁ : Level
```

## Definition

```agda
hasComplements : (L : Lattice ℓ₀ ℓ₁) → Type ℓ₀
hasComplements L =
  (x : ∣ L ∣ₗ) → Σ[ ¬x ∈ ∣ L ∣ₗ ] (¬x ∧[ L ] x ≡ ⊥[ L ]) × (¬x ∨[ L ] x ≡ ⊤[ L ])

BooleanAlgebra : (ℓ₀ ℓ₁ : Level) → Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁))
BooleanAlgebra ℓ₀ ℓ₁ = Σ[ L ∈ Lattice ℓ₀ ℓ₁ ] isDistributive L × hasComplements L

∣_∣B : BooleanAlgebra ℓ₀ ℓ₁ → Type ℓ₀
∣ L , _ ∣B = ∣ L ∣ₗ

¬[_]_ : (B : BooleanAlgebra ℓ₀ ℓ₁) → ∣ B ∣B → ∣ B ∣B
¬[ _ , _ , ¬_ ] x = fst (¬ x)

pos : BooleanAlgebra ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁
pos (L , _ , _) = pos-of-lattice L

latt : BooleanAlgebra ℓ₀ ℓ₁ → Lattice ℓ₀ ℓ₁
latt (L , _) = L

¬-inv-∧ : (B : BooleanAlgebra ℓ₀ ℓ₁)
        → (x : ∣ B ∣B) → (¬[ B ] x) ∧[ latt B ] x ≡ ⊥[ latt B ]
¬-inv-∧ (_ , _ , comp) x = fst (snd (comp x))

¬-inv-∨ : (B : BooleanAlgebra ℓ₀ ℓ₁)
        → (x : ∣ B ∣B) → (¬[ B ] x) ∨[ latt B ] x ≡ ⊤[ latt B ]
¬-inv-∨ (_ , _ , comp) x = snd (snd (comp x))
```

# Symmetric difference

```agda
sym-diff : (B : BooleanAlgebra ℓ₀ ℓ₁) → ∣ B ∣B → ∣ B ∣B → ∣ B ∣B
sym-diff B@(L , _) x y = (x ∧[ L ] (¬[ B ] y)) ∨[ L ] (y ∧[ L ] (¬[ B ] x))

syntax sym-diff B x y = x ⊕[ B ] y

module SymmetricDifference (B : BooleanAlgebra ℓ₀ ℓ₁) where

  L = fst B

  _⊕_ : ∣ B ∣B → ∣ B ∣B → ∣ B ∣B
  x ⊕ y = x ⊕[ B ] y

  -- TODO: prove the following
  -- ⊕-dist : (x y z : ∣ B ∣B) → x ∧[ L ] (y ⊕ z) ≡ (x ∧[ L ] y) ⊕ (x ∧[ L ] z)
```

# Direct Definition of Boolean Algebras

```agda
record BooleanAlgebraStr (A : Type ℓ) : Type ℓ where
  field
    _⊓_ : A → A → A
    _⊔_ : A → A → A
    ⊤   : A
    ⊥   : A
    ¬_  : A → A

    ⊓-assoc : (x y z : A) → x ⊓ (y ⊓ z) ≡ (x ⊓ y) ⊓ z
    ⊔-assoc : (x y z : A) → x ⊔ (y ⊔ z) ≡ (x ⊔ y) ⊔ z

    ⊓-comm  : (x y   : A) → x ⊓ y ≡ y ⊓ x
    ⊔-comm  : (x y   : A) → x ⊔ y ≡ y ⊔ x

    ⊓-absorb : (x y : A) → x ⊓ (y ⊔ x) ≡ x
    ⊔-absorb : (x y : A) → x ⊔ (y ⊓ x) ≡ x

    ⊤-id : (x : A) → x ⊓ ⊤ ≡ x
    ⊥-id : (x : A) → x ⊔ ⊥ ≡ x

    ∧-dist : (x y z : A) → x ⊓ (y ⊔ z) ≡ (x ⊓ y) ⊔ (x ⊓ z)
    ∨-dist : (x y z : A) → x ⊔ (y ⊓ z) ≡ (x ⊔ y) ⊓ (x ⊔ z)

    ∧-inv : (x : A) → (¬ x) ⊓ x ≡ ⊥
    ∨-inv : (x : A) → (¬ x) ⊔ x ≡ ⊤

    A-set : isSet A
```

```agda
BooleanAlgebra′ : (ℓ : Level) → Type (ℓ-suc ℓ)
BooleanAlgebra′ ℓ = Σ[ A ∈ Type ℓ ] BooleanAlgebraStr A
```

## Equivalence of These Definitions

```agda
bool⇒bool′ : BooleanAlgebra ℓ₀ ℓ₁ → BooleanAlgebra′ ℓ₀
bool⇒bool′ B@(L , dist , complements) = ∣ L ∣ₗ , BA
  where
    open BooleanAlgebraStr

    BA : BooleanAlgebraStr ∣ L ∣ₗ
    _⊓_      BA  = λ x y → x ∧[ L ] y
    _⊔_      BA  = λ x y → x ∨[ L ] y
    ⊤        BA  = ⊤[ L ]
    ⊥        BA  = ⊥[ L ]
    ¬        BA  = λ x → ¬[ B ] x
    ⊓-assoc  BA  = ∧-assoc L
    ⊔-assoc  BA  = ∨-assoc L
    ⊓-comm   BA  = ∧-comm L
    ⊔-comm   BA  = ∨-comm L
    ⊓-absorb BA  = ∧-absorb L
    ⊔-absorb BA  = ∨-absorb L
    ⊤-id     BA  = ∧-id L
    ⊥-id     BA  = ∨-id L
    ∧-dist   BA  = dist
    ∨-dist   BA  = dist⇒distᵒᵖ L dist 
    ∧-inv    BA  = ¬-inv-∧ B
    ∨-inv    BA  = ¬-inv-∨ B
    A-set    BA  = carrier-is-set (pos-of-lattice L) 
```

## Some laws
