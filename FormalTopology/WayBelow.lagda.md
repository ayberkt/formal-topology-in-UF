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
open import Cubical.Data.Sigma hiding (_∨_)
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

Definition copied from Escardó and de Jong.

```agda
_≪_ : ∣ F ∣F → ∣ F ∣F → hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺)
x ≪ y =
  ∀[ S ∶ Fam 𝓦 ∣ F ∣F ]
    isDirected (pos F) S ⇒ y ≤ ⋁ S ⇒ ∥ Σ[ i ∈ index S  ] [ x ≤ (S $ i) ] ∥Ω
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

## Continuity

```agda
isContinuous : hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺)
isContinuous =
  ∀[ x ∶ ∣ F ∣F ] isSup (pos F) ((Σ[ y ∈ ∣ F ∣F ] [ y ≪ x ]) , fst) x
```
