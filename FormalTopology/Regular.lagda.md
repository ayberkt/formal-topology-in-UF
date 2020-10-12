---
title: Regular Locales
---

```agda
{-# OPTIONS --cubical --safe #-}

module Regular where

open import Cubical.Core.Everything
open import Basis
open import Poset
open import Nucleus
open import Frame
open import CoverFormsNucleus

```

```agda
well-inside : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → ∣ F ∣F → Type ℓ₀
well-inside F x y =
  Σ[ z ∈ ∣ F ∣F ] (x ⊓[ F ] z ≡ ⊥[ F ]) × (y ∨[ F ] z ≡ ⊤[ F ])

syntax well-inside F x y = x ⋜[ F ] y
```

```agda
-- In other words, x is clopen.
hasComplement : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → Type ℓ₀
hasComplement F x =
  Σ[ y ∈ ∣ F ∣F ] (x ⊓[ F ] y ≡ ⊥[ F ]) × (x ∨[ F ] y ≡ ⊤[ F ])
```

```agda
module SomePropertiesOf⋜ (F : Frame ℓ₀ ℓ₁ ℓ₂) where

  private
    _⊑_ = λ (x y : ∣ F ∣F) → x ⊑[ pos F ] y

  ⋜-comp : (x : ∣ F ∣F) → (x ⋜[ F ] x) ↔ hasComplement F x
  ⋜-comp x = (λ x → x) , (λ x → x)

  a⋜b→a⊑b : (x y : ∣ F ∣F) → x ⋜[ F ] y → [ x ⊑[ pos F ] y ]
  a⋜b→a⊑b x y (z , p , q) = x=x∧y⇒x⊑y F NTS
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

  a⋜c≤d : {x y z : ∣ F ∣F} → x ⋜[ F ] y → [ y ⊑[ pos F ] z ] → x ⋜[ F ] z
  a⋜c≤d {x} {y} {z} (c , p , q) y⊑z =
    c , (p , ⊑[ pos F ]-antisym _ _ (⊤[ F ]-top _)
             (subst (λ - → [ - ⊑[ pos F ] (z ∨[ F ] c) ]) q (⊔[ F ]-least y c (z ∨[ F ] c) (⊑[ pos F ]-trans y z _ y⊑z (⊔[ F ]-upper₀ z c)) (⊔[ F ]-upper₁ z c))))
    where
      open PosetReasoning (pos F)
```

# Regular formal topologies

```agda
```

# Regular locales

A locale A is said to be *regular* if it satisfies

  a = ⋁ { b ∈ A | b ⋜ a }

for every a ∈ A.

```agda
⇊ : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → Fam ℓ₀ ∣ F ∣F
⇊ F x = (Σ[ y ∈ ∣ F ∣F ] y ⋜[ F ] x) , π₀
```

```agda
isRegular : (F : Frame ℓ₀ ℓ₁ ℓ₂) → hProp (ℓ-max ℓ₀ ℓ₁)
isRegular F = ∀[ x ∶ ∣ F ∣F ] isSup (pos F) (⇊ F x) x
```

Prove lemma stating that if any element
```agda
regularity-lemma : (F : Frame ℓ₀ ℓ₁ ℓ₂)
                 → ((x : ∣ F ∣F) →
                      Σ[ U ∈ Fam ℓ₂ ∣ F ∣F ]
                       (((y : ∣ F ∣F) → y ε U → hasComplement F y)
                        × (x ≡ ⋁[ F ] U)))
                 → [ isRegular F ]
regularity-lemma F p x =
  upper , subst (λ - → (y : ∣ F ∣F) → [ fam-forall (⇊ F x) (λ k → rel (pos F) k y) ] → [ rel (pos F) - y ]) (sym x=⋁𝔘) ψ
  where
    open PosetReasoning (pos F)
    open SomePropertiesOf⋜ F

    𝔘 = π₀ (p x)

    x=⋁𝔘 : x ≡ ⋁[ F ] 𝔘
    x=⋁𝔘 = π₁ (π₁ (p x))

    upper : [ ∀[ y ε (⇊ F x) ] (y ⊑[ pos F ] x) ]
    upper y (i , eq) = subst (λ - → [ - ⊑[ pos F ] x ]) eq (a⋜b→a⊑b (π₁ (⇊ F x) i) x (π₁ i))

    ψ : (y : ∣ pos F ∣ₚ) → [ ∀[ x₁ ε (⇊ F x) ] (x₁ ⊑[ pos F ] y) ] → [ (⋁[ F ] 𝔘) ⊑[ pos F ] y ]
    ψ y q = ⋁[ F ]-least 𝔘 y NTS
      where
        NTS : [ ∀[ k ε 𝔘 ] (k ⊑[ pos F ] y) ]
        NTS k (i , eq) = q k ((𝔘 $ i , subst (λ - → (𝔘 $ i) ⋜[ F ] -) (sym x=⋁𝔘) (a⋜c≤d {y = 𝔘 $ i} (π₀ (π₁ (p x)) (𝔘 $ i) (i , refl)) (⋁[ F ]-upper 𝔘 (𝔘 $ i) (i , refl)))) , eq)
```

```agda
-- sublocale-regular : (F : Frame ℓ₀ ℓ₁ ℓ₂)
--                   → (j : Nucleus F)
--                   → [ isRegular F ]
--                   → [ isRegular (𝔣𝔦𝔵 F j) ]
-- sublocale-regular F j F-reg (x , jx=x) = {!!} , {!!}
```
