---
title: Regular Locales
---

```agda
{-# OPTIONS --cubical --safe #-}

module Regular where

open import Cubical.Core.Everything
open import Basis
open import Poset
open import Frame

```

```agda
well-inside : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → ∣ F ∣F → Type ℓ₀
well-inside F x y =
  Σ[ z ∈ ∣ F ∣F ] (x ⊓[ F ] z ≡ ⊥[ F ]) × (y ∨[ F ] z ≡ ⊤[ F ])

syntax well-inside F x y = x ≪[ F ] y
```

```agda
module SomePropertiesOf≪ (F : Frame ℓ₀ ℓ₁ ℓ₂) where

  hasComplement : ∣ F ∣F → Type ℓ₀
  hasComplement x =
    Σ[ y ∈ ∣ F ∣F ] (x ⊓[ F ] y ≡ ⊥[ F ]) × (x ∨[ F ] y ≡ ⊤[ F ])

  ≪-comp : (x : ∣ F ∣F) → (x ≪[ F ] x) ↔ hasComplement x
  ≪-comp x = (λ x → x) , (λ x → x)

  a≪b→a⊑b : (x y : ∣ F ∣F) → x ≪[ F ] y → [ x ⊑[ pos F ] y ]
  a≪b→a⊑b x y (z , p , q) = x=x∧y⇒x⊑y F NTS
    where
      open PosetReasoning (pos F)

      NTS : x ≡ x ⊓[ F ] y
      NTS = x                                ≡⟨ sym (x∧⊤=x F x)                 ⟩
            x ⊓[ F ] ⊤[ F ]                  ≡⟨ cong (λ - → x ⊓[ F ] -) (sym q) ⟩
            x ⊓[ F ] (y ∨[ F ] z)            ≡⟨ bin-dist F x y z                ⟩
            (x ⊓[ F ] y) ∨[ F ] (x ⊓[ F ] z) ≡⟨ cong (λ - → _ ∨[ F ] -) p       ⟩
            (x ⊓[ F ] y) ∨[ F ] ⊥[ F ]       ≡⟨ ∨-comm F (x ⊓[ F ] y) ⊥[ F ]    ⟩
            ⊥[ F ] ∨[ F ] (x ⊓[ F ] y)       ≡⟨ x∨⊥=x F (x ⊓[ F ] y)            ⟩
            x ⊓[ F ] y                       ∎
```
