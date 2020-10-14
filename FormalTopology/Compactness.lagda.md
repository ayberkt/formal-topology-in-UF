```agda
{-# OPTIONS --cubical --safe #-}

module Compactness where

open import Basis             hiding (A; B)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Nat  using  (ℕ)
open import Poset
open import FormalTopology
open import Cover
open import Frame             renaming (pos to posf)
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

  isCompact : Type (ℓ-suc ℓ₀)
  isCompact = (a : A) (U : 𝒫 A) (U-dc : [ isDownwardsClosed (pos F) U ]) →
                a ◁ U → ∥ Σ[ as ∈ List A ] (a ◁ down as) × [ down as ⊆ U ] ∥
```

## Compactness for frames

Johnstone's definition of a compact frame is simply a frame whose top element is
finite. Therefore, let us start by writing down Johnstone's notion of
finiteness (Lemma 3.1.ii, pg. 63).

```agda
isFinite₂ : (F : Frame ℓ₀ ℓ₁ ℓ₂)
          → ∣ F ∣F → Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-suc ℓ₂))
isFinite₂ {ℓ₂ = ℓ₂} F x =
  (U : Fam ℓ₂ ∣ F ∣F) →
    [ isDirected (Frame.pos F) U ] →
      x ≡ ⋁[ F ] U → ∥ Σ[ i ∈ index U ] [ x ⊑[ Frame.pos F ] (U $ i) ] ∥
```

A frame is compact iff its top element is finite.

```agda
isCompactFrame : (F : Frame ℓ₀ ℓ₁ ℓ₂) → hProp (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-suc ℓ₂))
isCompactFrame F = isFinite₂ F ⊤[ F ] , isPropΠ3 (λ x y z → ∥∥-prop _)
```
