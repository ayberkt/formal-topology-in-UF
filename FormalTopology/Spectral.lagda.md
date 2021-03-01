---
title: Spectral Locales
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Cubical.Functions.Logic
open import Frame

module Spectral (F : Frame 𝓤 𝓥 𝓦) where

open import Poset
open import WayBelow
open import Regular
```
-->

## Definition of spectrality

```agda
isSpectral : hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺)
isSpectral =
  ∀[ x ∶ ∣ F ∣F ]
    ∥ Σ[ U ∈ Fam 𝓦 ∣ F ∣F ] [ isDirected (pos F) U ] × [ isSup (pos F) U x ] ∥Ω
```
