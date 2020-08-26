---
title: Galois Connection
---

```agda
{-# OPTIONS --cubical --safe #-}

module GaloisConnection where

open import Cubical.Core.Everything
open import Basis
open import Poset
open import Frame
```

The monotonic map that is right adjoint to the diagonal monotonic map.

```agda
hasBinMeets : (P : Poset ℓ₀ ℓ₁) → Type (ℓ-max ℓ₀ ℓ₁)
hasBinMeets P = Σ[ _⊓_ ∈ (∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ) ] [ isGLB P _⊓_ ]

hasBinMeets′ : (P : Poset ℓ₀ ℓ₁) → Type (ℓ-max ℓ₀ ℓ₁)
hasBinMeets′ P = Σ[ g ∈ (P ×ₚ P) ─m→ P ] [ (Δ P) ⊣ g ]
  where
    open GaloisConnection P (P ×ₚ P)
```

```agda
bin-meets→bin-meets′ : (P : Poset ℓ₀ ℓ₁) → hasBinMeets P → hasBinMeets′ P
bin-meets→bin-meets′ P meet = (f , f-mono) , f⊣Δ
  where
    open GaloisConnection P (P ×ₚ P)
    open PosetReasoning P

    f : ∣ P ×ₚ P ∣ₚ → ∣  P ∣ₚ
    f (x , y) = fst meet x y

    f-mono : isMonotonic (P ×ₚ P) P f
    f-mono (x₀ , x₁) (y₀ , y₁) (x₀⊑y₀ , x₁⊑y₁) =
      π₁ (π₁ meet) y₀ y₁ (f (x₀ , x₁)) (φ , ψ)
      where
        φ : [ f (x₀ , x₁) ⊑[ P ] y₀ ]
        φ = f (x₀ , x₁) ⊑⟨ fst (fst (snd meet) x₀ x₁)  ⟩ x₀ ⊑⟨ x₀⊑y₀ ⟩ y₀ ■

        ψ : [ f (x₀ , x₁) ⊑[ P ] y₁ ]
        ψ = f (x₀ , x₁) ⊑⟨ snd (fst (snd meet) x₀ x₁)  ⟩ x₁ ⊑⟨ x₁⊑y₁ ⟩ y₁ ■

    f⊣Δ : [ (Δ P) ⊣ (f , f-mono) ]
    f⊣Δ x (y₀ , y₁) = NTS₀ , NTS₁
      where
        NTS₀ : [ (x , x) ⊑[ P ×ₚ P ] (y₀ , y₁) ⇒ x ⊑[ P ] f (y₀ , y₁) ]
        NTS₀ (x⊑y₀ , x⊑y₁) = π₁ (π₁ meet) y₀ y₁ x (x⊑y₀ , x⊑y₁)

        NTS₁ : [ x ⊑[ P ] f (y₀ , y₁) ] → [ (x , x) ⊑[ P ×ₚ P ] (y₀ , y₁) ]
        NTS₁ x⊑fy₀y₁ = x⊑y₀ , x⊑y₁
          where
            x⊑y₀ : [ x ⊑[ P ] y₀ ]
            x⊑y₀ = x ⊑⟨ x⊑fy₀y₁ ⟩ f (y₀ , y₁) ⊑⟨ fst (fst (snd meet) y₀ y₁) ⟩ y₀ ■

            x⊑y₁ : [ x ⊑[ P ] y₁ ]
            x⊑y₁ = x ⊑⟨ x⊑fy₀y₁ ⟩ f (y₀ , y₁) ⊑⟨ snd (fst (snd meet) y₀ y₁) ⟩ y₁ ■
```

```agda
bin-meets′→bin-meets : (P : Poset ℓ₀ ℓ₁)
                     → hasBinMeets′ P
                     → hasBinMeets  P
bin-meets′→bin-meets P (g , Δ⊣g) = inf , inf-is-glb
  where
    inf : ∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ
    inf x y = g $ₘ (x , y)

    inf-is-glb : [ isGLB P inf ]
    inf-is-glb = NTS₀ , NTS₁
      where
        NTS₀ : (x y : ∣ P ∣ₚ) → [ (inf x y) ⊑[ P ] x ⊓ (inf x y) ⊑[ P ] y ]
        NTS₀ x y = snd (Δ⊣g (inf x y) (x , y)) (⊑[ P ]-refl _)

        NTS₁ : (x y z : ∣ P ∣ₚ) → [ z ⊑[ P ] x ⊓ z ⊑[ P ] y ⇒ z ⊑[ P ] inf x y ]
        NTS₁ x y z (z⊑x , z⊑y) = π₀ (Δ⊣g z (x , y)) (z⊑x , z⊑y)
```
