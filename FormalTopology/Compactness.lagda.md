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
Cover : (F : Frame ℓ₀ ℓ₁ ℓ₂) → Type (ℓ₀ ⊔ suc ℓ₂)
Cover {ℓ₂ = ℓ₂} F = Σ[ U ∈ Fam ℓ₂ ∣ F ∣F ] ⋁[ F ] U ≡ ⊤[ F ]
```
