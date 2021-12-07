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
open import Cubical.Foundations.Function using (uncurry)
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

```agda
compacts-of : (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
compacts-of = Σ[ x ∈ ∣ F ∣F ] [ isCompactOpen x ]
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

## Properties of the way below relation

```agda
compactness-closed-under-joins : (x y : ∣ F ∣F)
                               → [ x ≪ x ] → [ y ≪ y ] → [ (x ∨[ F ] y) ≪ (x ∨[ F ] y) ]
compactness-closed-under-joins x y x≪x y≪y S S-dir p =
  ∥∥-rec (∥∥-prop _) (uncurry nts) (∥∥-× s-x s-y)
  where
  open PosetReasoning (pos F)

  x≤⋁S : [ x ⊑[ pos F ] ⋁[ F ] S ]
  x≤⋁S = x          ⊑⟨ ⊔[ F ]-upper₀ x y ⟩
         x ∨[ F ] y ⊑⟨ p                 ⟩
         ⋁[ F ] S   ■

  y≤⋁S : [ y ⊑[ pos F ] ⋁[ F ] S ]
  y≤⋁S = y          ⊑⟨ ⊔[ F ]-upper₁ x y ⟩
         x ∨[ F ] y ⊑⟨ p                 ⟩
         ⋁[ F ] S   ■

  s-x : ∥ Σ[ i₀ ∈ index S ] [ x ⊑[ pos F ] (S $ i₀) ] ∥
  s-x = x≪x S S-dir x≤⋁S

  s-y : ∥ Σ[ i₁ ∈ index S ] [ y ⊑[ pos F ] (S $ i₁) ] ∥
  s-y = y≪y S S-dir y≤⋁S

  nts : Σ[ i₀ ∈ index S ] [ x ⊑[ pos F ] (S $ i₀) ]
      → Σ[ i₁ ∈ index S ] [ y ⊑[ pos F ] (S $ i₁) ]
      → ∥ Σ[ i ∈ index S ] [ (x ∨[ F ] y) ⊑[ pos F ] (S $ i)  ] ∥
  nts (i₀ , x≤s₀) (i₁ , y≤s₁) =
    ∥∥-rec
      (∥∥-prop (Σ[ i ∈ index S ] [ (x ∨[ F ] y) ⊑[ pos F ] (S $ i) ]))
      rem
      (π₁ S-dir i₀ i₁)
    where
    rem : Σ[ k ∈ index S ] [ (S $ i₀) ⊑[ pos F ] (S $ k) ] × [ (S $ i₁) ⊑[ pos F ] (S $ k) ]
        → ∥ Σ[ i ∈ index S ] [ (x ∨[ F ] y) ⊑[ pos F ] (S $ i) ] ∥
    rem (i , Si₀≤Sk , Si₁≤Sk) = ∣ i , (⋁[ F ]-least _ _ goal) ∣
      where
      goal : [ ∀[ z ε ⁅ x , y ⁆ ] (z ⊑[ pos F ] (S $ i)) ]
      goal z (true  , eq) = subst (λ - → [ - ⊑[ pos F ] (S $ i) ]) eq
                              (x ⊑⟨ x≤s₀ ⟩ S $ i₀ ⊑⟨ Si₀≤Sk ⟩ S $ i ■)
      goal z (false , eq) = subst (λ - → [ - ⊑[ pos F ] (S $ i) ]) eq
                              (y ⊑⟨ y≤s₁ ⟩ S $ i₁ ⊑⟨ Si₁≤Sk ⟩ S $ i ■)
```
