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

**Definition.** A spectral locale is a locale for which the compact opens form
a base closed under finite meets.

```agda
isSpectral : hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺)
isSpectral =
  ∀[ x ∶ ∣ F ∣F ]
    ∥ Σ[ U ∈ Fam 𝓦 ∣ F ∣F ]
        [ isDirectedᵒᵖ (pos F) U ]
      × [ isSup (pos F) U x ]
      × [ ∀[ y ε U ] isCompactOpen F y ] ∥Ω
```
