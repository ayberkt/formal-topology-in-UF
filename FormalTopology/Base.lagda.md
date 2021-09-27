---
title: Base for a Frame
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

module Base where

open import Basis
open import Frame
open import Poset
```
-->

```agda
isBasisFor : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ∣ F ∣F → (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇ 
isBasisFor {𝓦 = 𝓦} F ℬ =
  (x : ∣ F ∣F) →
    Σ[ J ∈ Fam 𝓦 (index ℬ) ] [ isSup (pos F) ⁅ ℬ $ j ∣ j ε  J ⁆ x ]

isDirBasisFor : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ∣ F ∣F → (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
isDirBasisFor {𝓥 = 𝓥} {𝓦} F B =
  (x : ∣ F ∣F) →
    Σ[ U ∈ Fam 𝓦 (index B) ]
      [ isDirected (pos F) ⁅ B $ u ∣ u ε U ⁆ ⊓ isSup (pos F) ⁅ B $ u ∣ u ε U ⁆ x ]
```
