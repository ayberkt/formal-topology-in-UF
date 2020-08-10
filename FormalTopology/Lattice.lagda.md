---
title: Lattice
---

```agda
{-# OPTIONS --cubical --safe #-}

module Lattice where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Data.Sigma
open import Poset

private
  variable
    ℓ ℓ₀ ℓ₁ : Level
```

## Meet-semilattice

```agda
hasTop : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
hasTop P = Σ[ x ∈ ∣ P ∣ₚ ] ((y : ∣ P ∣ₚ) → [ x ⊒[ P ] y ])

isAMeetOf : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ × ∣ P ∣ₚ → Type (ℓ-max ℓ₀ ℓ₁)
isAMeetOf P x (y , z) =
    [ x ⊑[ P ]⟨ y , z ⟩ ]
  × ((x′ : ∣ P ∣ₚ) → [ x′ ⊑[ P ]⟨ y , z ⟩ ] → [ x′ ⊑[ P ] x ] )

hasBinaryMeets : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
hasBinaryMeets P = (x y : ∣ P ∣ₚ) → Σ[ z ∈ ∣ P ∣ₚ ] isAMeetOf P z (x , y)

hasAllFinMeets : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
hasAllFinMeets P = hasTop P × hasBinaryMeets P

MeetSemilattice : (ℓ₀ ℓ₁ : Level) → Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁))
MeetSemilattice ℓ₀ ℓ₁ = Σ[ P ∈ Poset ℓ₀ ℓ₁ ] hasAllFinMeets P
```

## Join-semilattice

```agda
hasBottom : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
hasBottom P = Σ[ x ∈ ∣ P ∣ₚ ] ((y : ∣ P ∣ₚ) → [ y ⊑[ P ] x ])

isAJoinOf : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ × ∣ P ∣ₚ → Type (ℓ-max ℓ₀ ℓ₁)
isAJoinOf P x (y , z) = [ ⟨ y , z ⟩⊑[ P ] x ]
                      × ((x′ : ∣ P ∣ₚ) → [ ⟨ y , z ⟩⊑[ P ] x′ ] → [ x ⊑[ P ] x′ ])

hasBinaryJoins : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
hasBinaryJoins P = (y z : ∣ P ∣ₚ) → Σ[ x ∈ ∣ P ∣ₚ ] isAJoinOf P x (y , z)

hasAllFinJoins : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
hasAllFinJoins P = hasBottom P × hasBinaryJoins P
```

## Lattice

A lattice is a poset that has all finite *meets* and *joins*, i.e. a meet and join
semilattice.

```agda
isALattice : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
isALattice P = hasAllFinMeets P × hasAllFinJoins P

Lattice : (ℓ₀ ℓ₁ : Level) → Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁))
Lattice ℓ₀ ℓ₁ = Σ[ P ∈ Poset ℓ₀ ℓ₁ ] isALattice P
```

## Pretty syntax for lattices

The carrier set of a lattice.

```agda
∣_∣ₗ : Lattice ℓ₀ ℓ₁ → Type ℓ₀
∣ P , _ ∣ₗ = ∣ P ∣ₚ

pos : Lattice ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁
pos (P , _) = P
```

```agda
meet-of : (L : Lattice ℓ₀ ℓ₁) → ∣ L ∣ₗ → ∣ L ∣ₗ → ∣ L ∣ₗ
meet-of (_ , (⊤ , _∧_) , _) x y = fst (x ∧ y)

syntax meet-of L x y = x ∧[ L ] y

∧-lower₀ : (L : Lattice ℓ₀ ℓ₁) → (x y : ∣ L ∣ₗ) → [ (x ∧[ L ] y) ⊑[ pos L ] x ]
∧-lower₀ (_ , (_ , meet) , _) x y = fst (fst (snd (meet x y)))

∧-lower₁ : (L : Lattice ℓ₀ ℓ₁) → (x y : ∣ L ∣ₗ) → [ (x ∧[ L ] y) ⊑[ pos L ] y ]
∧-lower₁ (_ , (_ , meet) , _) x y = snd (fst (snd (meet x y)))

∧-greatest : (L : Lattice ℓ₀ ℓ₁) {x y z : ∣ L ∣ₗ}
           → [ z ⊑[ pos L ]⟨ x , y ⟩ ] → [ z ⊑[ pos L ] (x ∧[ L ] y) ]
∧-greatest (_ , (_ , meet) , _) {x} {y} (z⊑x , z⊑y) =
  snd (snd (meet x y)) _ (z⊑x , z⊑y)
```

```agda
join-of : (L : Lattice ℓ₀ ℓ₁) → ∣ L ∣ₗ → ∣ L ∣ₗ → ∣ L ∣ₗ
join-of (_ , _ , (⊥ , _∨_)) x y = fst (x ∨ y)

syntax join-of L x y = x ∨[ L ] y

∨-upper₀ : (L : Lattice ℓ₀ ℓ₁) → (x y : ∣ L ∣ₗ) → [ x ⊑[ pos L ] (x ∨[ L ] y) ]
∨-upper₀ (_ , _ , (_ , join)) x y = fst (fst (snd (join x y)))

∨-upper₁ : (L : Lattice ℓ₀ ℓ₁) → (x y : ∣ L ∣ₗ) → [ y ⊑[ pos L ] (x ∨[ L ] y) ]
∨-upper₁ (_ , _ , (_ , join)) x y = snd (fst (snd (join x y)))

∨-least : (L : Lattice ℓ₀ ℓ₁) {x y z : ∣ L ∣ₗ}
        → [ ⟨ x , y ⟩⊑[ pos L ] z ] → [ (x ∨[ L ] y) ⊑[ pos L ] z ]
∨-least (_ , _ , (_ , join)) {x} {y} (x⊑z , y⊑z) =
  snd (snd (join x y)) _ (x⊑z , y⊑z)
```

## Some properties of lattices

Both the meet and join operations are idempotent in a lattice.

```agda
module Idempotent (L : Lattice ℓ₀ ℓ₁) where

  P = fst L

  ∧-idem : (x : ∣ L ∣ₗ) → x ∧[ L ] x ≡ x
  ∧-idem x = ⊑[ P ]-antisym (x ∧[ L ] x) x down up
    where
      down : [ x ∧[ L ] x ⊑[ P ] x ]
      down = ∧-lower₀ L x x

      up : [ x ⊑[ P ] (x ∧[ L ] x) ]
      up = ∧-greatest L (⊑[ P ]-refl x , ⊑[ P ]-refl x)

  ∨-idem : (x : ∣ L ∣ₗ) → x ∨[ L ] x ≡ x
  ∨-idem x = ⊑[ P ]-antisym (x ∨[ L ] x) x down up
    where
      down : [ (x ∨[ L ] x) ⊑[ P ] x ]
      down = ∨-least L (⊑[ pos L ]-refl x , ⊑[ pos L ]-refl x)

      up : [ x ⊑[ P ] (x ∨[ L ] x) ]
      up = ∨-upper₀ L x x
```

Both operations are commutative.

```agda
∧-comm : (L : Lattice ℓ₀ ℓ₁) → (x y : ∣ L ∣ₗ) → x ∧[ L ] y ≡ y ∧[ L ] x
∧-comm L x y = ⊑[ pos L ]-antisym _ _ down up
  where
    down : [ (x ∧[ L ] y) ⊑[ pos L ] (y ∧[ L ] x) ]
    down = ∧-greatest L (∧-lower₁ L x y , ∧-lower₀ L x y)

    up : [ (y ∧[ L ] x) ⊑[ pos L ] (x ∧[ L ] y) ]
    up = ∧-greatest L (∧-lower₁ L y x , ∧-lower₀ L y x)
```
