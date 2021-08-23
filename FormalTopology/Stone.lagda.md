---
title: Stone Locales
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Cubical.Functions.Logic
open import Frame

module Stone (F : Frame 𝓤 𝓥 𝓦) where

open import Poset
open import WayBelow
open import Regular
```
-->

## Definition of Stone

```agda
isStone : hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺)
isStone = isCompact F ⊓ ∥ hasClopenBasis F ∥Ω
```

```agda
isComplemented : Fam 𝓦 ∣ F ∣F → (𝓤 ∨ 𝓦) ̇
isComplemented S = (x : ∣ F ∣F) → x ε S → hasComplement F x
```

```agda
isStone′ : (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
isStone′ =
  ∥ Σ[ ℬ ∈ Fam 𝓦 ∣ F ∣F ] isBasisFor F ℬ × isComplemented ℬ ∥
```
