```agda
{-# OPTIONS --cubical --safe #-}

module HeytingAlgebra where

open import Cubical.Core.Everything
open import Cubical.Foundations.Logic
open import Cubical.Data.Sigma
open import Poset
open import Lattice

private
  variable
    ℓ₀ ℓ₁ : Level
```

```agda
isHeyting : (L : Lattice ℓ₀ ℓ₁) → Type (ℓ-max ℓ₀ ℓ₁)
isHeyting L =
  (x y : ∣ L ∣ₗ) →
    Σ[ x⇒y ∈ ∣ L ∣ₗ ]
      ((z : ∣ L ∣ₗ) → [ z ⊑[ pos L ] x⇒y ⇔ (z ∧[ L ] x) ⊑[ pos L ] y ])
```

```agda
HeytingAlgebra : (ℓ₀ ℓ₁ : Level) → Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁))
HeytingAlgebra ℓ₀ ℓ₁ = Σ[ L ∈ Lattice ℓ₀ ℓ₁ ] isHeyting L
```

```
implies : (H : HeytingAlgebra ℓ₀ ℓ₁) → ∣ fst H ∣ₗ → ∣ fst H ∣ₗ → ∣ fst H ∣ₗ
implies (_ , heyting) x y = fst (heyting x y)

syntax implies H x y = x ⇒[ H ] y

pseudocomplement : (H : HeytingAlgebra ℓ₀ ℓ₁) → ∣ fst H ∣ₗ → ∣ fst H ∣ₗ
pseudocomplement H x = x ⇒[ H ] ⊥[ fst H ]

syntax pseudocomplement H x = ¬[ H ] x
```

```agda
module HeytingAlgebraLaws (H : HeytingAlgebra ℓ₀ ℓ₁) where

  L = fst H
  open PosetReasoning (pos L)

  x⇒x=⊤ : (x : ∣ L ∣ₗ) → x ⇒[ H ] x ≡ ⊤[ L ]
  x⇒x=⊤ x = ⊑[ pos L ]-antisym _ _ (⊤-top L (x ⇒[ H ] x)) NTS
    where
      NTS : [ ⊤[ L ] ⊑[ pos L ] (x ⇒[ H ] x) ]
      NTS = snd (snd (snd H x x) ⊤[ L ]) (∧-lower₁ L ⊤[ L ] x)

  mp : (x y : ∣ L ∣ₗ) → x ∧[ L ] (x ⇒[ H ] y) ≡ x ∧[ L ] y
  mp x y = ⊑[ pos L ]-antisym _ _ down {!!}
    where
      down : _
      down = {!!}
        where
          NTS : _
          NTS = snd (yoneda (pos L) (x ∧[ L ] (x ⇒[ H ] y)) y) λ z → {!!}
```

```agda
isHeyting′ : (L : Lattice ℓ₀ ℓ₁) → Type ℓ₀
isHeyting′ L =
  Σ[ _⇒_ ∈ (∣ L ∣ₗ → ∣ L ∣ₗ → ∣ L ∣ₗ) ]
    [ sat-i _⇒_ ⊓ sat-ii _⇒_ ⊓ sat-iii _⇒_ ⊓ sat-iv _⇒_ ]
  where
    sat-i : (∣ L ∣ₗ → ∣ L ∣ₗ → ∣ L ∣ₗ) → hProp _
    sat-i _⇒_ = ∀[ x ∶ ∣ L ∣ₗ ] ((x ⇒ x) ≡ ⊤[ L ])
              , carrier-is-set (pos L) _ _

    sat-ii : (∣ L ∣ₗ → ∣ L ∣ₗ → ∣ L ∣ₗ) → hProp _
    sat-ii _⇒_ =
      ∀[ x ∶ ∣ L ∣ₗ ] ∀[ y ∶ ∣ L ∣ₗ ] (x ∧[ L ] (x ⇒ y) ≡ x ∧[ L ] y)
      , carrier-is-set (pos L) _ _

    sat-iii : (∣ L ∣ₗ → ∣ L ∣ₗ → ∣ L ∣ₗ) → hProp _
    sat-iii _⇒_ = ∀[ x ∶ ∣ L ∣ₗ ] ∀[ y ∶ ∣ L ∣ₗ ] (y ∧[ L ] (x ⇒ y) ≡ y)
                , carrier-is-set (pos L) _ _

    sat-iv : (∣ L ∣ₗ → ∣ L ∣ₗ → ∣ L ∣ₗ) → hProp _
    sat-iv _⇒_ =
      ∀[ x ∶ ∣ L ∣ₗ ] ∀[ y ∶ ∣ L ∣ₗ ] ∀[ z ∶ ∣ L ∣ₗ ]
        (x ⇒ (y ∧[ L ] z) ≡ (x ⇒ y) ∧[ L ] (x ⇒ z))
      , carrier-is-set (pos L) _ _
```

```agda
HeytingAlgebra′ : (ℓ₀ ℓ₁ : Level) → Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁))
HeytingAlgebra′ ℓ₀ ℓ₁ = Σ[ L ∈ Lattice ℓ₀ ℓ₁ ] isHeyting′ L
```
