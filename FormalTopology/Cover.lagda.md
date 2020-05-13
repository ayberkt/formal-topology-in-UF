```
{-# OPTIONS --cubical --safe #-}

module Cover where

open import Level
open import FormalTopology
open import Poset
open import Basis
```

## Some lemmas about the cover relation

```
module CoverFromFormalTopology (ℱ : FormalTopology ℓ ℓ′) where
  private
    P    = pos ℱ
    D    = π₀ ℱ
    out  = outcome

  data _◀_ (a : ∣ P ∣ₚ) (U : ∣ P ∣ₚ → hProp ℓ) : Type ℓ where
    dir    : [ U a ] → a ◀ U
    branch : (b : exp ℱ a) → (f : (c : out ℱ b) → next ℱ c ◀ U) → a ◀ U
    squash : (p₀ p₁ : a ◀ U) → p₀ ≡ p₁

  ◀-prop : (a : ∣ P ∣ₚ) (U : 𝒫 ∣ P ∣ₚ) → isProp (a ◀ U)
  ◀-prop a U = squash
```

```
  module _ {U : ∣ P ∣ₚ → hProp ℓ} (U-down : [ isDownwardsClosed P U ]) where

    ◀-lem₁ : {a a′ : ∣ P ∣ₚ} → [ a′ ⊑[ P ] a ] →  a ◀ U → a′ ◀ U
    ◀-lem₁ {_}     {_}  h (squash p₀ p₁ i) = squash (◀-lem₁ h p₀) (◀-lem₁ h p₁) i
    ◀-lem₁ {_}     {_}  h (dir q)          = dir (U-down _ _ q h)
    ◀-lem₁ {a = a} {a′} h (branch b f)     = branch b′ g
      where
        b′ : exp ℱ a′
        b′ = π₀ (sim ℱ a′ a h b)

        g : (c′ : out ℱ b′) → next ℱ c′ ◀ U
        g c′ = ◀-lem₁ δc′⊑δc (f c)
          where
            c : out ℱ b
            c = π₀ (π₁ (sim ℱ a′ a h b) c′)

            δc′⊑δc : [ next ℱ c′ ⊑[ P ] next ℱ c ]
            δc′⊑δc = π₁ (π₁ (sim ℱ a′ a h b) c′)

  lem₄ : (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ)
       → ((u : ∣ P ∣ₚ) → [ u ∈ U ] → u ◀ V) → (a : ∣ P ∣ₚ) → a ◀ U → a ◀ V
  lem₄ U V h a (squash p₀ p₁ i) = squash (lem₄ U V h a p₀) (lem₄ U V h a p₁) i
  lem₄ U V h a (dir p)          = h a p
  lem₄ U V h a (branch b f)     = branch b (λ c → lem₄  U V h (next ℱ c) (f c))

  module _ (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ) (V-dc : [ isDownwardsClosed P V ]) where
```

```
    lem₂ : {a : ∣ P ∣ₚ} → a ◀ U → [ a ∈ V ] → a ◀ (U ∩ V)
    lem₂ (squash p₀ p₁ i) h = squash (lem₂ p₀ h) (lem₂ p₁ h) i
    lem₂ (dir q)          h = dir (q , h)
    lem₂ (branch b f)     h = branch b (λ c → lem₂ (f c) (V-dc _ _ h (mono ℱ _ b c)))

  module _ (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ)
           (U-dc : [ isDownwardsClosed P U ])
           (V-dc : [ isDownwardsClosed P V ]) where

    lem₃ : {a a′ : ∣ P ∣ₚ} → [ a′ ⊑[ P ] a ] → a ◀ U → a′ ◀ V → a′ ◀ (V ∩ U)
    lem₃ {a} {a′} a′⊑a (squash p₀ p₁ i) q = squash (lem₃ a′⊑a p₀ q) (lem₃ a′⊑a p₁ q) i
    lem₃ {a} {a′} a′⊑a (dir a∈U)        q = lem₂ V U U-dc q (U-dc a a′ a∈U a′⊑a)
    lem₃ {a} {a′} a′⊑a (branch b f)     q = branch b′ g
      where
        b′ : exp ℱ a′
        b′ = π₀ (sim ℱ a′ a a′⊑a b)

        g : (c′ : out ℱ b′) → next ℱ c′ ◀ (V ∩ U)
        g c′ = lem₃ NTS (f c) (◀-lem₁ V-dc (mono ℱ a′ b′ c′) q)
          where
            c : out ℱ b
            c = π₀ (π₁ (sim ℱ a′ a a′⊑a b) c′)

            NTS : [ next ℱ c′ ⊑[ P ] next ℱ c ]
            NTS = π₁ (π₁ (sim ℱ a′ a a′⊑a b) c′)
```
