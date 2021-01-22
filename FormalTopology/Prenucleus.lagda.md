```agda
{-# OPTIONS --cubical --safe #-}

module Prenucleus where

open import Cubical.Core.Everything hiding (_∧_)

open import Poset
open import Frame
open import Cubical.Functions.Logic      hiding   (_⊓_)
open import Cubical.Foundations.Prelude  using    (refl; sym; cong; _≡⟨_⟩_; _∎)
open import Cubical.Data.Sigma           using    (Σ≡Prop; _×_)
open import Cubical.Foundations.Function using    (const; _∘_)
open import Basis                        renaming (_⊓_ to _∧_)
```

```agda
isPrenuclear : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (∣ L ∣F → ∣ L ∣F) → Type (ℓ-max ℓ₀ ℓ₁)
isPrenuclear L j = N₀ × N₁
  where
    N₀ = (x y : ∣ L ∣F) → j (x ⊓[ L ] y) ≡ (j x) ⊓[ L ] (j y)
    N₁ = (x   : ∣ L ∣F) → [ x ⊑[ pos L ] (j x) ]
```

```agda
Prenucleus : Frame ℓ₀ ℓ₁ ℓ₂ → Type (ℓ-max ℓ₀ ℓ₁)
Prenucleus L = Σ (∣ L ∣F → ∣ L ∣F) (isPrenuclear L)
```

Every prenucleus is monotonic.

```agda
monop : (L : Frame ℓ₀ ℓ₁ ℓ₂) ((j , _) : Prenucleus L)
      → (x y : ∣ L ∣F) → [ x ⊑[ pos L ] y ] → [ (j x) ⊑[ pos L ] (j y) ]
monop L (j , N₀ , _) x y x⊑y =
  j x             ⊑⟨ ≡⇒⊑ (pos L) (cong j (x⊑y⇒x=x∧y L x⊑y)) ⟩
  j (x ⊓[ L ] y)  ⊑⟨ ≡⇒⊑ (pos L) (N₀ x y)                   ⟩
  j x ⊓[ L ] j y  ⊑⟨ ⊓[ L ]-lower₁ (j x) (j y)              ⟩
  j y             ■
  where
    open PosetReasoning (pos L)
```
