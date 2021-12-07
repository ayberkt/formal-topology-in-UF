---
title: Right Adjoints for Frame Homomorphisms
author: Ayberk Tosun (j.w.w. Martín Escardó)
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Poset
open import Frame
open import Base hiding (hasBasis)

module RightAdjoint where
```
-->

```agda
hasBasis : (F : Frame 𝓤 𝓥 𝓦) → (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
hasBasis {𝓦 = 𝓦} F = Σ[ B ∈ Fam 𝓦 ∣ F ∣F ] isDirBasisFor F B
```

```agda
module AdjointFunctorTheorem (F : Frame 𝓤 𝓥 𝓥) (G : Frame 𝓤′ 𝓥 𝓥) (basis : hasBasis F) where

  open GaloisConnection (pos F) (pos G)

  open PosetReasoning (pos G)
  open PosetReasoning (pos F) using () renaming (_⊑⟨_⟩_ to _⊑F⟨_⟩_; _■ to _■F)

  aft-1 : (f : pos F ─m→ pos G)
        → [ f hasRightAdjoint ]
        → ((S : Fam 𝓥 ∣ F ∣F) → (⋁[ G ] ⁅ π₀ f s ∣ s ε S ⁆) ≡ (π₀ f (⋁[ F ] S)))
  aft-1 (f , f-mono) ((g , g-mono) , f⊣g) S = sym (⋁-unique G _ _ G𝟏 G𝟐)
    where
    G𝟏 : (x : ∣ G ∣F) → x ε (f ⟨$⟩ S) → [ x ⊑[ pos G ] (f (⋁[ F ] S)) ]
    G𝟏 x (i , eq) = subst (λ - → [ - ⊑[ pos G ] f (⋁[ F ] S) ]) eq G𝟏a
      where
      G𝟏a : [ f (S $ i) ⊑[ pos G ] f (⋁[ F ] S) ]
      G𝟏a = f-mono _ _ (⋁[ F ]-upper _ _ (i , refl))

    G𝟐 : (z : ∣ G ∣F)
       → ((x : ∣ G ∣F) → x ε (f ⟨$⟩ S) → [ x ⊑[ pos G ] z ])
       → [ f (⋁[ F ] S) ⊑[ pos G ] z ]
    G𝟐 z ϕ = π₁ (f⊣g (⋁[ F ] S) z) (⋁[ F ]-least _ _ G𝟐a)
      where
      G𝟐a : [ ∀[ s ε S ] (s ⊑[ pos F ] g z) ]
      G𝟐a s (i , eq) =
        subst (λ - → [ - ⊑[ pos F ] g z ]) eq (π₀ (f⊣g (π₁ S i) z) (ϕ (f (S $ i)) (i , refl)))

  aft-2 : (f : pos F ─m→ pos G)
        → ((S : Fam 𝓥 ∣ F ∣F) → (⋁[ G ] ⁅ π₀ f s ∣ s ε S ⁆) ≡ (π₀ f (⋁[ F ] S)))
        → [ f hasRightAdjoint ]
  aft-2 f eq = (g , g-mono) , f⊣g
    where
    ℬ-F = π₀ basis

    g : ∣ G ∣F → ∣ F ∣F
    g y =
      ⋁[ F ] ⁅ π₁ ℬ-F i ∣ (i , _) ∶ Σ[ i ∈ π₀ ℬ-F ] [ f $ₘ (π₁ ℬ-F i) ⊑[ pos G ] y ] ⁆

    g-mono : isMonotonic (pos G) (pos F) g
    g-mono x y x⊑y  = ⋁[ F ]-least _ _ γ
      where
      γ : _
      γ z ((i , p) , eq) = subst (λ - → [ - ⊑[ pos F ] (g y) ]) eq δ
        where
        nts : [ f $ₘ (π₁ ℬ-F i) ⊑[ pos G ] y ]
        nts = f $ₘ (π₁ ℬ-F i) ⊑⟨ p ⟩ x ⊑⟨ x⊑y ⟩ y ■

        δ : [ _ ⊑[ pos F ] g y ]
        δ = ⋁[ F ]-upper _ _ ((i , nts) , refl)

    gm : pos G ─m→ pos F
    gm = g , g-mono

    f⊣g : [ f ⊣ gm ]
    f⊣g x y = nts₀ , nts₁
      where
      nts₀ : [ f $ₘ x ⊑[ pos G ] y ⇒ x ⊑[ pos F ] g y ]
      nts₀ fx≤y =
        x                           ⊑F⟨ ≡⇒⊑ (pos F) (sym x-eq) ⟩
        ⋁[ F ] ⁅ π₁ ℬ-F j ∣ j ε 𝒥 ⁆ ⊑F⟨ ⋁[ F ]-least _ _ rem ⟩
        g y                         ■F
        where
        𝒥 = π₀ (π₁ basis x)

        ϕ : _
        ϕ = π₀ (π₁ (π₁ (π₁ basis x)))

        ψ : _
        ψ = π₁ (π₁ (π₁ (π₁ basis x)))

        x-eq : (⋁[ F ] fmap (λ j → π₁ ℬ-F j) 𝒥) ≡ x
        x-eq = sym (⋁-unique F _ _ ϕ ψ)

        rem : [ ∀[ z ε ⁅ π₁ ℬ-F j ∣ j ε 𝒥 ⁆ ] (z ⊑[ pos F ] g y) ]
        rem z (j , eq) = subst (λ - → [ - ⊑[ pos F ] g y ]) eq rem′
          where
          goal : [ f $ₘ π₁ ℬ-F (𝒥 $ j) ⊑[ pos G ] y ]
          goal = f $ₘ π₁ ℬ-F (𝒥 $ j)                ⊑⟨ π₁ f _ _ (⋁[ F ]-upper _ _ (j , refl))  ⟩
                 f $ₘ (⋁[ F ] ⁅ π₁ ℬ-F j ∣ j ε 𝒥 ⁆) ⊑⟨ ≡⇒⊑ (pos G) (cong (f $ₘ_) x-eq) ⟩
                 f $ₘ x                             ⊑⟨ fx≤y ⟩
                 y                                  ■

          rem′ : [ (π₁ ((π₁ ℬ-F) ⟨$⟩ 𝒥) j) ⊑[ pos F ] (g y) ]
          rem′ = ⋁[ F ]-upper _ _ ((𝒥 $ j , goal) , refl)

      nts₁ : [ x ⊑[ pos F ] g y ⇒ f $ₘ x ⊑[ pos G ] y ]
      nts₁ x≤gy =
        f $ₘ x ⊑⟨ π₁ f _ _ x≤gy ⟩
        f $ₘ (⋁[ F ] ⁅ π₁ ℬ-F i ∣ (i , _) ∶ Σ[ i ∈ π₀ ℬ-F ] [ f $ₘ (π₁ ℬ-F i) ⊑[ pos G ] y ] ⁆)     ⊑⟨ ≡⇒⊑ (pos G) (sym (eq _)) ⟩
        (⋁[ G ] ⁅ f $ₘ (π₁ ℬ-F i) ∣ (i , _) ∶ Σ[ i ∈ π₀ ℬ-F ] [ f $ₘ (π₁ ℬ-F i) ⊑[ pos G ] y ] ⁆  ) ⊑⟨ rem ⟩
        y         ■
        where
        𝒥 = π₀ (π₁ basis x)

        rem : [ ⋁[ G ] (⁅ f $ₘ (π₁ ℬ-F i) ∣ (i , _) ∶ Σ[ i ∈ π₀ ℬ-F ] [ f $ₘ (π₁ ℬ-F i) ⊑[ pos G ] y ] ⁆) ⊑[ pos G ] y ]
        rem = ⋁[ G ]-least _ _ goal
          where
          goal : [ ∀[ z ε ⁅ f $ₘ (π₁ ℬ-F i) ∣ (i , _) ∶ Σ[ i ∈ π₀ ℬ-F ] [ f $ₘ (π₁ ℬ-F i) ⊑[ pos G ] y ] ⁆ ] (z ⊑[ pos G ] y) ]
          goal z ((i , p) , eq) = subst (λ - → [ - ⊑[ pos G ] y ]) eq p

  _^*ᴹ : (f : pos F ─m→ pos G) → ((S : Fam 𝓥 ∣ F ∣F) → (⋁[ G ] ⁅ π₀ f s ∣ s ε S ⁆) ≡ f $ₘ (⋁[ F ] S)) → pos G ─m→ pos F
  _^*ᴹ f rem = (π₀ (aft-2 f rem))

  _^* : (f : pos F ─m→ pos G) → ((S : Fam 𝓥 ∣ F ∣F) → (⋁[ G ] ⁅ π₀ f s ∣ s ε S ⁆) ≡ f $ₘ (⋁[ F ] S)) → ∣ G ∣F → ∣ F ∣F
  _^* f rem = π₀ (π₀ (aft-2 f rem))

  ^*-RA : (f : pos F ─m→ pos G) → (rem : (S : Fam 𝓥 ∣ F ∣F) → (⋁[ G ] ⁅ π₀ f s ∣ s ε S ⁆) ≡ f $ₘ (⋁[ F ] S)) → [ f ⊣ (_^*ᴹ f rem) ]
  ^*-RA f = π₁ ∘ aft-2 f

  RA-of-homo : (F ─f→ G) → ∣ G ∣F → ∣ F ∣F
  RA-of-homo (f , _ , _ , p) = π₀ (_^*ᴹ f λ S → sym (p S))

  closure : (f : pos F ─m→ pos G)
          → (f⋆ : pos G ─m→ pos F)
          → [ f ⊣ f⋆ ]
          → (x : ∣ G ∣F) → [ f $ₘ (f⋆ $ₘ x) ⊑[ pos G ] x ]
  closure f f⋆ f⊣f⋆ x = π₁ (f⊣f⋆ (f⋆ $ₘ x) x) (⊑[ pos F ]-refl (f⋆ $ₘ x))

  RAPL : (f : pos F ─m→ pos G)
       → (f⋁ : ((S : Fam 𝓥 ∣ F ∣F) → (⋁[ G ] ⁅ f $ₘ  s ∣ s ε S ⁆) ≡ f $ₘ (⋁[ F ] S)))
       → (x y : ∣ G ∣F) → _^* f f⋁ (x ⊓[ G ] y) ≡ (_^* f f⋁ x) ⊓[ F ] (_^* f f⋁ y)
  RAPL 𝒻@(f , _) f⋁ x y = ⊑[ pos F ]-antisym _ _ G𝟏 G𝟐
    where
    f⊣f⋆ : [ 𝒻 ⊣ _^*ᴹ 𝒻 f⋁ ]
    f⊣f⋆ = ^*-RA 𝒻 f⋁

    𝒻⋆ : pos G ─m→ pos F
    𝒻⋆ = _^*ᴹ 𝒻 f⋁

    f⋆ : ∣ G ∣F → ∣ F ∣F
    f⋆ = _^* 𝒻 f⋁

    G𝟏 : [ (𝒻 ^*) f⋁ (x ⊓[ G ] y) ⊑[ pos F ] (𝒻 ^*) f⋁ x ⊓[ F ] (𝒻 ^*) f⋁ y ]
    G𝟏 = ⊓[ F ]-greatest _ _ _ G𝟏a G𝟏b
      where
      G𝟏a : [ (𝒻 ^*) f⋁ (x ⊓[ G ] y) ⊑[ pos F ] (𝒻 ^*) f⋁ x ]
      G𝟏a = π₁ ((𝒻 ^*ᴹ) f⋁) _ _ (⊓[ G ]-lower₀ x y)

      G𝟏b : [ (𝒻 ^*) f⋁ (x ⊓[ G ] y) ⊑[ pos F ] (𝒻 ^*) f⋁ y ]
      G𝟏b = (π₁ ((𝒻 ^*ᴹ) f⋁) _ _ (⊓[ G ]-lower₁ x y))

    G𝟐 : [ (𝒻 ^*) f⋁ x ⊓[ F ] (𝒻 ^*) f⋁ y ⊑[ pos F ] (𝒻 ^*) f⋁ (x ⊓[ G ] y) ]
    G𝟐 = π₀ (f⊣f⋆ (glb-of F ((𝒻 ^*) f⋁ x) ((𝒻 ^*) f⋁ y)) (x ⊓[ G ] y)) G𝟐a
      where
      G𝟐a : [ f (f⋆ x ⊓[ F ] f⋆ y) ⊑[ pos G ] x ⊓[ G ] y ]
      G𝟐a = ⊓[ G ]-greatest x y (f (f⋆ x ⊓[ F ] f⋆ y)) G𝟐b G𝟐c
        where
        G𝟐b : [ f (f⋆ x ⊓[ F ] f⋆ y) ⊑[ pos G ] x ]
        G𝟐b = f (f⋆ x ⊓[ F ] f⋆ y) ⊑⟨ ⦅𝟏⦆ ⟩ f (f⋆ x) ⊑⟨ ⦅𝟐⦆ ⟩ x ■
          where
          ⦅𝟏⦆ = π₁ 𝒻 _ _ (⊓[ F ]-lower₀ _ _)
          ⦅𝟐⦆ = closure 𝒻 𝒻⋆ (^*-RA 𝒻 f⋁) x

        G𝟐c : [ f (f⋆ x ⊓[ F ] f⋆ y) ⊑[ pos G ] y ]
        G𝟐c = f (f⋆ x ⊓[ F ] f⋆ y) ⊑⟨ ⦅𝟏⦆ ⟩ f (f⋆ y) ⊑⟨ ⦅𝟐⦆ ⟩ y ■
          where
          ⦅𝟏⦆ = π₁ 𝒻 _ _ (⊓[ F ]-lower₁ _ _)
          ⦅𝟐⦆ = closure 𝒻 𝒻⋆ (^*-RA 𝒻 f⋁) y
```
