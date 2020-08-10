---
title: Lattice
---

```agda
{-# OPTIONS --cubical --safe #-}

module Lattice where

open import Cubical.Core.Everything
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
