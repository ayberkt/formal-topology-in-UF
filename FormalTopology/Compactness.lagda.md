```agda
{-# OPTIONS --cubical --safe #-}

module Compactness where

open import Basis             hiding (A; B)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Nat  using  (ℕ)
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

Next, we define what it means for a cover to be finite.

```agda
FinCover : (F : Frame ℓ₀ ℓ₁ zero) → Type ℓ₀
FinCover F = Σ[ xs ∈ List ∣ F ∣F ] (famFromList xs) covers F 
```

The type of *subcovers* of a given cover.

```agda
isASubcover : (F : Frame ℓ₀ ℓ₁ zero) → FinCover F → Cover F → Type ℓ₀
isASubcover F (xs , _) (U , _) = famFromList xs ⊆fam U

hasFinSubcover : (F : Frame ℓ₀ ℓ₁ zero) → Cover F → Type ℓ₀
hasFinSubcover F C₀ = Σ[ C₁ ∈ FinCover F ] isASubcover F C₁ C₀
```

Statement of compactness.

```agda
isACompactFrame : (F : Frame ℓ₀ ℓ₁ zero) → Type (suc zero ⊔ ℓ₀)
isACompactFrame F = (C : Cover F) → hasFinSubcover F C
```
