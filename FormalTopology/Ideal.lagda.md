```agda
{-# OPTIONS --cubical --safe #-}

module Ideal where

open import Basis
open import Poset hiding (isDownwardsClosed)
open import Frame
```

```agda
↓ : (L : Frame 𝓤 𝓥 𝓦) → ∣ L ∣F → ∣ L ∣F → hProp 𝓥
↓ L x y = y ⊑[ pos L ] x

isDownwardsClosed : (L : Frame 𝓤 𝓥 𝓦) → (∣ L ∣F → hProp 𝓥) → hProp (𝓤 ∨ 𝓥)
isDownwardsClosed L U =
  ∀[ x ∶ ∣ L ∣F ] U x ⇒ (∀[ y ∶ ∣ L ∣F ] y ⊑[ pos L ] x ⇒ U y)

isUpwardsDirected : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (∣ L ∣F → hProp ℓ₁) → hProp _
isUpwardsDirected L U =
  U ⊥[ L ] ⊓ (∀[ x ∶ ∣ L ∣F ] ∀[ y ∶ ∣ L ∣F ] U x ⇒ U y ⇒ U (x ∨[ L ] y))

isIdeal : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (∣ L ∣F → hProp ℓ₁) → hProp _
isIdeal L U = isDownwardsClosed L U ⊓ isUpwardsDirected L U

isIdeal′ : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (∣ L ∣F → hProp ℓ₁) → hProp _
isIdeal′ L U = isDownwardsClosed L U ⊓ ϕ
  where
  ϕ : hProp _
  ϕ = ∀[ x ∶ ∣ L ∣F ] ∀[ y ∶ ∣ L ∣F ] U x ⇒ U y ⇒ U (x ∨[ L ] y)

ideal→ideal′ : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (U : ∣ L ∣F → hProp ℓ₁)
             → [ isIdeal L U ] → [ isIdeal′ L U ]
ideal→ideal′ L U (dc , ud) = dc , †
  where
  † : [ ∀[ x ∶ ∣ L ∣F ] ∀[ y ∶ ∣ L ∣F ] U x ⇒ U y ⇒ U (x ∨[ L ] y) ]
  † x y x∈U y∈U = ?
```

```agda
↓-ideal : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (x : ∣ L ∣F) → [ isIdeal L (↓ L x) ]
↓-ideal L x = dc , ud
  where
    open PosetReasoning (pos L)

    dc : [ isDownwardsClosed L (↓ L x) ]
    dc y y⊑x z z⊑y = z ⊑⟨ z⊑y ⟩ y ⊑⟨ y⊑x ⟩ x ■

    ud : [ isUpwardsDirected L (↓ L x) ]
    ud = ⊥[ L ]-bottom x , λ y z y∈U z∈U → ⊔[ L ]-least y z x y∈U z∈U
```

```agda
isAPrincipalIdeal : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (∣ L ∣F → hProp ℓ₁) → Type _
isAPrincipalIdeal L U = Σ[ x ∈ ∣ L ∣F ] U ≡ ↓ L x
```
