---
title: Spectral Locales
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Cubical.Functions.Logic
open import Cubical.Foundations.Function
open import Frame

module Spectral (F : Frame 𝓤 𝓥 𝓦) where

open import Poset
open import WayBelow
open import Regular
open import PatchFrame
```
-->

## Definition of spectrality

**Definition.** A spectral locale is a locale for which the compact opens form
a base closed under finite meets.

**Definition (better).** Every open is the join of the set of compact opens
below it and the meet of two compacts opens is compact. Also, the top element is
compact.

```agda
isSpectral : (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
isSpectral =
    ((x : ∣ F ∣F) → Σ[ U ∈ Fam 𝓦 ∣ F ∣F ] [ isSup (pos F) U x ] × [ ∀[ y ε U ] isCompactOpen F y ])
  × [ isCompactOpen F ⊤[ F ] ]
  × ((x y : ∣ F ∣F) →
       [ isCompactOpen F x ] → [ isCompactOpen F y ] → [ isCompactOpen F (x ⊓[ F ] y) ])

-- TODO.
-- The definition of spectral should be the same as Stone but the requirement of clopen
-- basis replaced with the requirement of a compact basis.
```

```agda
compact-yoneda : isSpectral
               → (x y : ∣ F ∣F)
               → ((b : ∣ F ∣F) → [ isCompactOpen F b ] →
                    [ b ⊑[ pos F ] x ] → [ b ⊑[ pos F ] y ])
               → [ x ⊑[ pos F ] y ]
compact-yoneda spec x y ϕ =
  x        ⊑⟨ ≡⇒⊑ (pos F) β ⟩
  ⋁[ F ] W ⊑⟨ γ          ⟩
  y        ■
  where
  open PosetReasoning (pos F)

  W : Fam 𝓦 ∣ F ∣F
  W = π₀ (π₀ spec x)

  β : x ≡ ⋁[ F ] W
  β = uncurry (⋁-unique F W x) (π₀ (π₁ (π₀ spec x)))

  γ : [ ⋁[ F ] W ⊑[ pos F ] y ]
  γ = ⋁[ F ]-least W y nts
    where
    nts : (z : ∣ F ∣F) → z ε W → [ z ⊑[ pos F ] y ]
    nts z (i , eq) = subst (λ - → [ - ⊑[ pos F ] y ]) eq rem
      where
      δ : [ (W $ i) ⊑[ pos F ] x ]
      δ = W $ i    ⊑⟨ ⋁[ F ]-upper W (W $ i) (i , refl) ⟩
          ⋁[ F ] W ⊑⟨ ≡⇒⊑ (pos F) (sym β)               ⟩
          x        ■

      rem : [ (W $ i) ⊑[ pos F ] y ]
      rem = ϕ (W $ i) (π₁ (π₁ (π₀ spec x)) (W $ i) (i , refl)) δ

compact-yoneda₁ : isSpectral
                → (x y : ∣ F ∣F)
                → [ x ⊑[ pos F ] y ]
                → ((b : ∣ F ∣F) → [ isCompactOpen F b ] →
                     [ b ⊑[ pos F ] x ] → [ b ⊑[ pos F ] y ])
compact-yoneda₁ spec x y p b b-comp q =
  b ⊑⟨ q ⟩ x ⊑⟨ p ⟩ y ■
  where
  open PosetReasoning (pos F)
```

```agda
-- spectral→stone : (F : Frame 𝓤 𝓥 𝓦) → isSpectral F → [ isStone F ]
-- spectral→stone F F-spec = ?
```

```agda
resp-compactness : (f : ∣ F ∣F → ∣ F ∣F) → (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
resp-compactness f =
  (b x : ∣ F ∣F) →
    [ isCompactOpen F b ] →
      [ b ⊑[ pos F ] f x ] →
        Σ[ a ∈ ∣ F ∣F ]
          [ isCompactOpen F a ] × [ a ⊑[ pos F ] x ]  × [ b ⊑[ pos F ] f a ]

continuity-lemma : isSpectral
                 → (f : ∣ F ∣F → ∣ F ∣F)
                 → isMonotonic (pos F) (pos F) f
                 → resp-compactness f
                 → isScottCont′ F f
continuity-lemma spec f mono comp U U-dir =
  ⊑[ pos F ]-antisym _ _ β γ
  where
  η : (b : ∣ F ∣F)
    → [ isCompactOpen F b ]
    → [ b ⊑[ pos F ] f (⋁[ F ] U) ]
    → [ b ⊑[ pos F ] ⋁[ F ] ⁅ f x ∣ x ε U ⁆ ]
  η b b-compact α =
    b                      ⊑⟨ π₁ (π₁ (π₁ (comp b _ b-compact α))) ⟩
    f a                    ⊑⟨ nts ⟩
    ⋁[ F ] ⁅ f x ∣ x ε U ⁆ ■
    where
    open PosetReasoning (pos F)

    a = π₀ (comp b _ b-compact α)

    a-comp : [ isCompactOpen F a ]
    a-comp = π₀ (π₁ (comp b _ b-compact α))

    q : [ a ⊑[ pos F ] ⋁[ F ] U ]
    q = π₀ (π₁ (π₁ (comp b _ b-compact α)))

    rem : Σ[ i ∈ index U ] [ a ⊑[ pos F ] (U $ i) ]
        → [ f a ⊑[ pos F ] ⋁[ F ] ⁅ f x ∣ x ε U ⁆ ]
    rem (i , p) =
      f a                    ⊑⟨ mono a (U $ i) p            ⟩
      f (U $ i)              ⊑⟨ ⋁[ F ]-upper _ _ (i , refl) ⟩
      ⋁[ F ] ⁅ f x ∣ x ε U ⁆ ■

    nts : [ f a ⊑[ pos F ] ⋁[ F ] ⁅ f x ∣ x ε U ⁆ ]
    nts = ∥∥-rec (isProp[] (_ ⊑[ pos F ] _)) rem (a-comp U U-dir q)

  β : [ f (⋁[ F ] U) ⊑[ pos F ] (⋁[ F ] ⁅ f x ∣ x ε U ⁆) ]
  β = compact-yoneda spec (f (⋁[ F ] U)) (⋁[ F ] ⁅ f x ∣ x ε U ⁆) η

  δ : (z : ∣ F ∣F) → z ε ⁅ f x ∣ x ε U ⁆ → [ z ⊑[ pos F ] f (⋁[ F ] U) ]
  δ z (i , eq) = subst (λ - → [ - ⊑[ pos F ] f (⋁[ F ] U) ]) eq nts
    where
    nts : [ f (U $ i) ⊑[ pos F ] (f (⋁[ F ] U)) ]
    nts = mono (U $ i) (⋁[ F ] U) (⋁[ F ]-upper _ _ (i , refl))

  γ : [ (⋁[ F ] ⁅ f x ∣ x ε U ⁆) ⊑[ pos F ] f (⋁[ F ] U) ]
  γ = ⋁[ F ]-least ⁅ f x ∣ x ε U ⁆ (f (⋁[ F ] U)) δ

  -- function-lemma : (f g : ∣ F ∣F → ∣ F ∣F)
  --                → isMonotonic (pos F) (pos F) f
  --                → isMonotonic (pos F) (pos F) g
  --                → ((b : ∣ F ∣F) → [ isCompactOpen F b ] → f b ≡ g b)
  --                → (x : ∣ F ∣F)
  --                → f x ≡ g x
  -- function-lemma f g f-sc g-sc ϕ x =
  --   f x ≡⟨ {!!} ⟩ f (⋁⟨ i ⟩ (b $ i)) ≡⟨ {!!} ⟩ {!f (⋁⟨ i ⟩ (b $ i))!} ≡⟨ {!!} ⟩ g x ∎
  --   where
  --   open JoinSyntax ∣ F ∣F (λ - → ⋁[ F ] -)

  --   b = π₀ (π₀ spec x)
```

```agda
-- patch-is-stone : [ isStone Patch ]
-- patch-is-stone = patch-is-compact , ∣ {!!} ∣
```

TODO:

1. Prove 3.3.(i)
2. Patch(A) is a Stone locale for every spectral A.
n
