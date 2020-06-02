# Some lemmas about the cover relation

```agda
{-# OPTIONS --cubical --safe #-}

module Cover where

open import Level
open import FormalTopology
open import Poset
open import Basis
```

We define a submodule `CoverFromFormalTopology` parameterised by a formal topology `ℱ`
since all of the functions in this module take as argument a certain formal topology.

```agda
module CoverFromFormalTopology (ℱ : FormalTopology ℓ ℓ′) where
```

We refer to the underlying poset of the formal topology `ℱ` as `P`, and its outcome
function as `out`.

```agda
  private
    P    = pos ℱ
    out  = outcome
```

## Definition of the covering relation

The covering relation is defined as follows:

```agda
  data _◁_ (a : ∣ P ∣ₚ) (U : ∣ P ∣ₚ → hProp ℓ) : Type ℓ where
    dir    : [ U a ] → a ◁ U
    branch : (b : exp ℱ a) → (f : (c : out ℱ b) → next ℱ c ◁ U) → a ◁ U
    squash : (p q : a ◁ U) → p ≡ q

  ◁-prop : (a : ∣ P ∣ₚ) (U : 𝒫 ∣ P ∣ₚ) → isProp (a ◁ U)
  ◁-prop a U = squash
```

## Lemmas about the covering relation

We now prove four crucial lemmas about the cover.

### Lemma 1

```agda
  module _ {U : ∣ P ∣ₚ → hProp ℓ} (U-down : [ isDownwardsClosed P U ]) where

    ◁-lem₁ : {a a′ : ∣ P ∣ₚ} → [ a′ ⊑[ P ] a ] →  a ◁ U → a′ ◁ U
    ◁-lem₁ {_}     {_}  h (squash p₀ p₁ i) = squash (◁-lem₁ h p₀) (◁-lem₁ h p₁) i
    ◁-lem₁ {_}     {_}  h (dir q)          = dir (U-down _ _ q h)
    ◁-lem₁ {a = a} {a′} h (branch b f)     = branch b′ g
      where
        b′ : exp ℱ a′
        b′ = π₀ (sim ℱ a′ a h b)

        g : (c′ : out ℱ b′) → next ℱ c′ ◁ U
        g c′ = ◁-lem₁ δc′⊑δc (f c)
          where
            c : out ℱ b
            c = π₀ (π₁ (sim ℱ a′ a h b) c′)

            δc′⊑δc : [ next ℱ c′ ⊑[ P ] next ℱ c ]
            δc′⊑δc = π₁ (π₁ (sim ℱ a′ a h b) c′)
```

### Lemma 2

```agda
  module _ (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ) (V-dc : [ isDownwardsClosed P V ]) where

    ◁-lem₂ : {a : ∣ P ∣ₚ} → a ◁ U → [ a ∈ V ] → a ◁ (U ∩ V)
    ◁-lem₂ (squash p₀ p₁ i) h = squash (◁-lem₂ p₀ h) (◁-lem₂ p₁ h) i
    ◁-lem₂ (dir q)          h = dir (q , h)
    ◁-lem₂ (branch b f)     h = branch b λ c → ◁-lem₂ (f c) (V-dc _ _ h (mono ℱ _ b c))
```

### Lemma 3

```agda
  lem₄ : (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ)
       → ((u : ∣ P ∣ₚ) → [ u ∈ U ] → u ◁ V) → (a : ∣ P ∣ₚ) → a ◁ U → a ◁ V
  lem₄ U V h a (squash p₀ p₁ i) = squash (lem₄ U V h a p₀) (lem₄ U V h a p₁) i
  lem₄ U V h a (dir p)          = h a p
  lem₄ U V h a (branch b f)     = branch b λ c → lem₄  U V h (next ℱ c) (f c)
```

### Lemma 4

```
  module _ (U : 𝒫 ∣ P ∣ₚ) (V : 𝒫 ∣ P ∣ₚ)
           (U-dc : [ isDownwardsClosed P U ])
           (V-dc : [ isDownwardsClosed P V ]) where

    ◁-lem₃ : {a a′ : ∣ P ∣ₚ} → [ a′ ⊑[ P ] a ] → a ◁ U → a′ ◁ V → a′ ◁ (V ∩ U)
    ◁-lem₃ {a} {a′} a′⊑a (squash p q i) r = squash (◁-lem₃ a′⊑a p r) (◁-lem₃ a′⊑a q r) i
    ◁-lem₃ {a} {a′} a′⊑a (dir a∈U)      r = ◁-lem₂ V U U-dc r (U-dc a a′ a∈U a′⊑a)
    ◁-lem₃ {a} {a′} a′⊑a (branch b f)   r = branch b′ g
      where
        b′ : exp ℱ a′
        b′ = π₀ (sim ℱ a′ a a′⊑a b)

        g : (c′ : out ℱ b′) → next ℱ c′ ◁ (V ∩ U)
        g c′ = ◁-lem₃ NTS (f c) (◁-lem₁ V-dc (mono ℱ a′ b′ c′) r)
          where
            c : out ℱ b
            c = π₀ (π₁ (sim ℱ a′ a a′⊑a b) c′)

            NTS : [ next ℱ c′ ⊑[ P ] next ℱ c ]
            NTS = π₁ (π₁ (sim ℱ a′ a a′⊑a b) c′)
```
