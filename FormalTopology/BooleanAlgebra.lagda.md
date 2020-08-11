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
  (x : ∣ L ∣ₗ) → Σ[ ¬x ∈ ∣ L ∣ₗ ] (¬x ∧[ L ] x ≡ ⊤[ L ]) × (¬x ∨[ L ] x ≡ ⊥[ L ])

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
        → (x : ∣ B ∣B) → (¬[ B ] x) ∧[ latt B ] x ≡ ⊤[ latt B ]
¬-inv-∧ (_ , _ , comp) x = fst (snd (comp x))

¬-inv-∨ : (B : BooleanAlgebra ℓ₀ ℓ₁)
        → (x : ∣ B ∣B) → (¬[ B ] x) ∨[ latt B ] x ≡ ⊥[ latt B ]
¬-inv-∨ (_ , _ , comp) x = snd (snd (comp x))
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

    ∧-inv : (x : A) → x ⊓ (¬ x) ≡ ⊥
    ∨-inv : (x : A) → x ⊓ (¬ x) ≡ ⊤

    A-set : isSet A
```

```agda
BooleanAlgebra′ : (ℓ : Level) → Type (ℓ-suc ℓ)
BooleanAlgebra′ ℓ = Σ[ A ∈ Type ℓ ] BooleanAlgebraStr A
```

## Some laws
