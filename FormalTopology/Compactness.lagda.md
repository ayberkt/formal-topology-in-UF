```agda
{-# OPTIONS --cubical --safe #-}

module Compactness where

open import Basis             hiding (A; B)
open import Cubical.Data.List hiding ([_])
open import Poset
open import FormalTopology
open import Cover
open import Frame             hiding (pos)
```

# Compactness for formal topologies

```agda
module _ (F : FormalTopology ℓ₀ ℓ₀) where

  open CoverFromFormalTopology F using (_◁_)

  private
    A = stage   F
    B = exp     F
    C = outcome F
    d = next    F

  down : List A → 𝒫 A
  down []       = λ _ → bot ℓ₀
  down (x ∷ xs) = λ y → ∥ [ y ⊑[ pos F ] x ] ⊎ [ y ∈ down xs ] ∥ , ∥∥-prop _

  isCompact : Type (suc ℓ₀)
  isCompact = (a : A) (U : 𝒫 A) (U-dc : [ isDownwardsClosed (pos F) U ]) →
                a ◁ U → ∥ Σ[ as ∈ List A ] (a ◁ down as) × [ down as ⊆ U ] ∥
```

# Compactness for frames

We start by stating the notion of a *cover* for a frame.

```agda
cover-syntax : (F : Frame ℓ₀ ℓ₁ ℓ₂) → Fam ℓ₂ ∣ F ∣F → Type ℓ₀
cover-syntax F U = ⋁[ F ] U ≡ ⊤[ F ]

syntax cover-syntax F U = U covers F

Cover : (F : Frame ℓ₀ ℓ₁ ℓ₂) → Type (ℓ₀ ⊔ suc ℓ₂)
Cover {ℓ₂ = ℓ₂} F = Σ[ U ∈ Fam ℓ₂ ∣ F ∣F ] U covers F
```

The type of *subcovers* of a given cover.

```agda
Subcover : (F : Frame ℓ₀ ℓ₁ ℓ₂) → (C : Cover F) → Type (ℓ₀ ⊔ suc ℓ₂)
Subcover F (U , _) = Σ[ (V , _) ∈ Cover F ] V ⊆fam U
```

Statement of compactness.

```agda
isACompactFrame : (F : Frame ℓ₀ ℓ₁ ℓ₂) → Type (ℓ₀ ⊔ suc ℓ₂)
isACompactFrame F = (C : Cover F) → Subcover F C
```
