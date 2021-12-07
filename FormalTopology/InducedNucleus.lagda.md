---
title: Induced Nucleus
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

module InducedNucleus where

open import Frame
open import Poset
open import Base
open import Nucleus
open import Basis
open import RightAdjoint
open import Basis using ([_])
```
-->

```agda
induced₀ : (A : Frame 𝓤 𝓥 𝓥) (B : Frame 𝓤′ 𝓥 𝓥)
         → (ℬ : Fam 𝓥 ∣ A ∣F)
         → isDirBasisFor A ℬ
         → (f : A ─f→ B) → ∣ A ∣F → ∣ A ∣F
induced₀ A B ℬ dir 𝒻@((f , _) , _) = 𝒻 ⋆ ∘ f
  where
  open AdjointFunctorTheorem A B (ℬ , dir) renaming (RA-of-homo to _⋆)
```

```agda
induced₀-is-nuclear : (A : Frame 𝓤 𝓥 𝓥) (B : Frame 𝓤′ 𝓥 𝓥)
                    → (ℬ : Fam 𝓥 ∣ A ∣F)
                    → (b : isDirBasisFor A ℬ)
                    → (h : A ─f→ B)
                    → isNuclear A (induced₀ A B ℬ b h)
induced₀-is-nuclear A B ℬ b 𝒻@((f , _) , _ , f∧ , f⋁) =
  ind-𝓃₀ , ind-𝓃₁ , ind-𝓃₂
  where
  open AdjointFunctorTheorem A B (ℬ , b) renaming (RA-of-homo to _⋆)
  open PosetReasoning (pos A)

  f⋆ : ∣ B ∣F → ∣ A ∣F
  f⋆ = _⋆ 𝒻

  f⋆∘f : ∣ A ∣F → ∣ A ∣F
  f⋆∘f = induced₀ A B ℬ b 𝒻

  open GaloisConnection (pos A) (pos B)

  ind-𝓃₀ : (x y : ∣ A ∣F) → f⋆∘f (x ⊓[ A ] y) ≡ (f⋆∘f x) ⊓[ A ] (f⋆∘f y)
  ind-𝓃₀ x y = f⋆ (f (x ⊓[ A ] y))      ≡⟨ cong f⋆ (f∧ x y)                   ⟩
               f⋆ (f x ⊓[ B ] f y)      ≡⟨ RAPL (π₀ 𝒻) (sym ∘ f⋁) (f x) (f y) ⟩
               f⋆ (f x) ⊓[ A ] f⋆ (f y) ∎

  ind-𝓃₁ : (x : ∣ A ∣F) → [ x ⊑[ pos A ] f⋆∘f x ]
  ind-𝓃₁ x = π₀ (^*-RA (π₀ 𝒻) (sym ∘ f⋁) x (f x)) (⊑[ pos B ]-refl (f x))

  ind-𝓃₂ : (x : ∣ A ∣F) → [ f⋆∘f (f⋆∘f x) ⊑[ pos A ] f⋆∘f x ]
  ind-𝓃₂ x = f⋆∘f (f⋆∘f x)     ⊑⟨ ⊑[ pos A ]-refl _ ⟩
             f⋆ (f (f⋆ (f x))) ⊑⟨ †                 ⟩
             f⋆∘f x            ■
               where
               † = f⋆∘f-idempotent (π₀ 𝒻) (_^*ᴹ (π₀ 𝒻) (sym ∘ f⋁)) (^*-RA (π₀ 𝒻) (sym ∘ f⋁)) x
```
