---
title: Heyting Implication in a Frame
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

module NegriFormalTopology where

open import Basis
open import Poset
```
-->

## Definition

```agda
record FormalTopologyStr₀ (P : Poset 𝓤 𝓥) : (𝓤 ⁺ ∨ 𝓥) ̇ where
  field
    _◁_ : ∣ P ∣ₚ → (∣ P ∣ₚ → hProp 𝓤) → hProp 𝓤

  _◁◁_ : 𝒫 ∣ P ∣ₚ → 𝒫 ∣ P ∣ₚ → hProp 𝓤
  U ◁◁ V = ∀[ u ∶ ∣ P ∣ₚ ] u ∈ U ⇒ u ◁ V

  _∧_ : (∣ P ∣ₚ → hProp 𝓥) → (∣ P ∣ₚ → hProp 𝓥) → ∣ P ∣ₚ → hProp (𝓤 ∨ 𝓥)
  (U ∧ V) x =
    ∥ Σ[ (u , v) ∈ ∣ P ∣ₚ × ∣ P ∣ₚ ]
        [ U u ] × [ V v ] × [ x ⊑[ P ] u ] × [ x ⊑[ P ] v ] ∥Ω

  field
    ◁-refl  : (U : 𝒫 ∣ P ∣ₚ) → [ U ⊆ (λ - → - ◁ U) ]
    ◁-trans : (a : ∣ P ∣ₚ) (U V : 𝒫 ∣ P ∣ₚ)
            → [ a ◁ U ] → [ U ◁◁ V ] → [ a ◁ V ]
    ◁-left  : (a b : ∣ P ∣ₚ)
            → [ b ⊑[ P ] a ] → [ a ◁ U ] → [ b ◁ U ]
    -- ◁-right : (U : 𝒫 ∣ P ∣ₚ) (a : ∣ P ∣ₚ)
            -- → [ a ◁ U ] → [ a ◁ V ] → [ a ◁ (U ∧ V) ]
```
