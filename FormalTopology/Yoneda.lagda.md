---
title: Yoneda Lemma for Posets
---


```agda
{-# OPTIONS --cubical --safe #-}

module Yoneda where

open import Cubical.Core.Everything
open import Cubical.Foundations.Logic
open import Poset

private
  variable
    ℓ₀ ℓ₁ : Level
```

```agda
yoneda : (P : Poset ℓ₀ ℓ₁)
       → (x y : ∣ P ∣ₚ)
       → [ (x ⊑[ P ] y) ⇔ (∀[ z ∶ ∣ P ∣ₚ ] z ⊑[ P ] x ⇒ z ⊑[ P ] y) ]
yoneda P x y = forwards , backwards
  where
    open PosetReasoning P

    forwards : [ x ⊑[ P ] y ⇒ (∀[ z ∶ ∣ P ∣ₚ ] z ⊑[ P ] x ⇒ z ⊑[ P ] y) ]
    forwards x⊑y z z⊑x = z ⊑⟨ z⊑x ⟩ x ⊑⟨ x⊑y ⟩ y ■

    backwards : [ (∀[ z ∶ ∣ P ∣ₚ ] z ⊑[ P ] x ⇒ z ⊑[ P ] y) ⇒ x ⊑[ P ] y ]
    backwards p = p x (⊑[ P ]-refl x)
```
