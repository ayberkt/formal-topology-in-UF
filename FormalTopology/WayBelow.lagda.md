---
title: The Way Below Relation
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Cubical.Functions.Logic
open import Frame

module WayBelow (F : Frame 𝓤 𝓥 𝓦) where

open import Poset
open import Nucleus
```
-->

## Notation

```agda
infix 7 _≤_

_≤_ : ∣ F ∣F → ∣ F ∣F → hProp 𝓥
x ≤ y = x ⊑[ pos F ] y
```

```agda
infix 8 ⋁_

⋁_ : Fam 𝓦 ∣ F ∣F → ∣ F ∣F
⋁ U = ⋁[ F ] U
```

## Definition of way below

```agda
_≪_ : ∣ F ∣F → ∣ F ∣F → hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺)
x ≪ y =
  ∀[ S ∶ Fam 𝓦 ∣ F ∣F ]
    isDirected (pos F) S ⇒ y ≤ ⋁ S ⇒ ∥ Σ[ s ∈ ∣ F ∣F ] s ε S × [ x ≤ s ] ∥Ω
```

## Definition of a compact element

```agda
isCompactOpen : ∣ F ∣F → hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺)
isCompactOpen x = x ≪ x
```

## Definition of a compact frame

```agda
isCompact : hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺)
isCompact = isCompactOpen ⊤[ F ]
```
