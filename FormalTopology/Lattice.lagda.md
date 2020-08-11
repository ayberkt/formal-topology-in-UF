---
title: Lattice
---

```agda
{-# OPTIONS --cubical --safe #-}

module Lattice where

open import Cubical.Core.Everything hiding (_∨_; _∧_)
open import Cubical.Foundations.Prelude hiding (_∨_; _∧_)
open import Cubical.Foundations.Logic
open import Cubical.Data.Sigma hiding (_∨_; _∧_)
open import Poset

private
  variable
    ℓ ℓ₀ ℓ₁ : Level
```

## Meet-semilattice

```agda
hasTop : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
hasTop P = Σ[ x ∈ ∣ P ∣ₚ ] ((y : ∣ P ∣ₚ) → [ x ⊒[ P ] y ])

isAMeetOf : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ × ∣ P ∣ₚ → Type (ℓ-max ℓ₀ ℓ₁)
isAMeetOf P x (y , z) =
    [ x ⊑[ P ]⟨ y , z ⟩ ]
  × ((x′ : ∣ P ∣ₚ) → [ x′ ⊑[ P ]⟨ y , z ⟩ ] → [ x′ ⊑[ P ] x ] )

hasBinaryMeets : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
hasBinaryMeets P = (x y : ∣ P ∣ₚ) → Σ[ z ∈ ∣ P ∣ₚ ] isAMeetOf P z (x , y)

hasAllFinMeets : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
hasAllFinMeets P = hasTop P × hasBinaryMeets P

MeetSemilattice : (ℓ₀ ℓ₁ : Level) → Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁))
MeetSemilattice ℓ₀ ℓ₁ = Σ[ P ∈ Poset ℓ₀ ℓ₁ ] hasAllFinMeets P
```

## Join-semilattice

```agda
hasBottom : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
hasBottom P = Σ[ x ∈ ∣ P ∣ₚ ] ((y : ∣ P ∣ₚ) → [ y ⊑[ P ] x ])

isAJoinOf : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ × ∣ P ∣ₚ → Type (ℓ-max ℓ₀ ℓ₁)
isAJoinOf P x (y , z) = [ ⟨ y , z ⟩⊑[ P ] x ]
                      × ((x′ : ∣ P ∣ₚ) → [ ⟨ y , z ⟩⊑[ P ] x′ ] → [ x ⊑[ P ] x′ ])

hasBinaryJoins : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
hasBinaryJoins P = (y z : ∣ P ∣ₚ) → Σ[ x ∈ ∣ P ∣ₚ ] isAJoinOf P x (y , z)

hasAllFinJoins : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
hasAllFinJoins P = hasBottom P × hasBinaryJoins P
```

## Lattice

A lattice is a poset that has all finite *meets* and *joins*, i.e. a meet and join
semilattice.

```agda
isALattice : Poset ℓ₀ ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
isALattice P = hasAllFinMeets P × hasAllFinJoins P

Lattice : (ℓ₀ ℓ₁ : Level) → Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁))
Lattice ℓ₀ ℓ₁ = Σ[ P ∈ Poset ℓ₀ ℓ₁ ] isALattice P
```

## Pretty syntax for lattices

The carrier set of a lattice.

```agda
∣_∣ₗ : Lattice ℓ₀ ℓ₁ → Type ℓ₀
∣ P , _ ∣ₗ = ∣ P ∣ₚ

pos : Lattice ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁
pos (P , _) = P
```

```agda
⊤[_] : (L : Lattice ℓ₀ ℓ₁) → ∣ L ∣ₗ
⊤[ (_ , (⊤ , _) , _) ] = fst ⊤

meet-of : (L : Lattice ℓ₀ ℓ₁) → ∣ L ∣ₗ → ∣ L ∣ₗ → ∣ L ∣ₗ
meet-of (_ , (⊤ , _∧_) , _) x y = fst (x ∧ y)

syntax meet-of L x y = x ∧[ L ] y

∧-lower₀ : (L : Lattice ℓ₀ ℓ₁) → (x y : ∣ L ∣ₗ) → [ (x ∧[ L ] y) ⊑[ pos L ] x ]
∧-lower₀ (_ , (_ , meet) , _) x y = fst (fst (snd (meet x y)))

∧-lower₁ : (L : Lattice ℓ₀ ℓ₁) → (x y : ∣ L ∣ₗ) → [ (x ∧[ L ] y) ⊑[ pos L ] y ]
∧-lower₁ (_ , (_ , meet) , _) x y = snd (fst (snd (meet x y)))

∧-greatest : (L : Lattice ℓ₀ ℓ₁) {x y z : ∣ L ∣ₗ}
           → [ z ⊑[ pos L ]⟨ x , y ⟩ ] → [ z ⊑[ pos L ] (x ∧[ L ] y) ]
∧-greatest (_ , (_ , meet) , _) {x} {y} (z⊑x , z⊑y) =
  snd (snd (meet x y)) _ (z⊑x , z⊑y)
```

```agda
⊥[_] : (L : Lattice ℓ₀ ℓ₁) → ∣ L ∣ₗ
⊥[ (_ , _  , (⊥ , _)) ] = fst ⊥

join-of : (L : Lattice ℓ₀ ℓ₁) → ∣ L ∣ₗ → ∣ L ∣ₗ → ∣ L ∣ₗ
join-of (_ , _ , (⊥ , _∨_)) x y = fst (x ∨ y)

syntax join-of L x y = x ∨[ L ] y

∨-upper₀ : (L : Lattice ℓ₀ ℓ₁) → (x y : ∣ L ∣ₗ) → [ x ⊑[ pos L ] (x ∨[ L ] y) ]
∨-upper₀ (_ , _ , (_ , join)) x y = fst (fst (snd (join x y)))

∨-upper₁ : (L : Lattice ℓ₀ ℓ₁) → (x y : ∣ L ∣ₗ) → [ y ⊑[ pos L ] (x ∨[ L ] y) ]
∨-upper₁ (_ , _ , (_ , join)) x y = snd (fst (snd (join x y)))

∨-least : (L : Lattice ℓ₀ ℓ₁) {x y z : ∣ L ∣ₗ}
        → [ ⟨ x , y ⟩⊑[ pos L ] z ] → [ (x ∨[ L ] y) ⊑[ pos L ] z ]
∨-least (_ , _ , (_ , join)) {x} {y} (x⊑z , y⊑z) =
  snd (snd (join x y)) _ (x⊑z , y⊑z)
```

## Some properties of lattices

Both the meet and join operations are idempotent in a lattice.

```agda
module Idempotent (L : Lattice ℓ₀ ℓ₁) where

  P = fst L

  ∧-idem : (x : ∣ L ∣ₗ) → x ∧[ L ] x ≡ x
  ∧-idem x = ⊑[ P ]-antisym (x ∧[ L ] x) x down up
    where
      down : [ x ∧[ L ] x ⊑[ P ] x ]
      down = ∧-lower₀ L x x

      up : [ x ⊑[ P ] (x ∧[ L ] x) ]
      up = ∧-greatest L (⊑[ P ]-refl x , ⊑[ P ]-refl x)

  ∨-idem : (x : ∣ L ∣ₗ) → x ∨[ L ] x ≡ x
  ∨-idem x = ⊑[ P ]-antisym (x ∨[ L ] x) x down up
    where
      down : [ (x ∨[ L ] x) ⊑[ P ] x ]
      down = ∨-least L (⊑[ pos L ]-refl x , ⊑[ pos L ]-refl x)

      up : [ x ⊑[ P ] (x ∨[ L ] x) ]
      up = ∨-upper₀ L x x
```

Both operations are commutative.

```agda
∧-comm : (L : Lattice ℓ₀ ℓ₁) → (x y : ∣ L ∣ₗ) → x ∧[ L ] y ≡ y ∧[ L ] x
∧-comm L x y = ⊑[ pos L ]-antisym _ _ down up
  where
    down : [ (x ∧[ L ] y) ⊑[ pos L ] (y ∧[ L ] x) ]
    down = ∧-greatest L (∧-lower₁ L x y , ∧-lower₀ L x y)

    up : [ (y ∧[ L ] x) ⊑[ pos L ] (x ∧[ L ] y) ]
    up = ∧-greatest L (∧-lower₁ L y x , ∧-lower₀ L y x)

∨-comm : (L : Lattice ℓ₀ ℓ₁) → (x y : ∣ L ∣ₗ) → x ∨[ L ] y ≡ y ∨[ L ] x
∨-comm L x y = ⊑[ pos L ]-antisym _ _ (φ x y) (φ y x)
  where
    φ : (z w : ∣ L ∣ₗ) → [ z ∨[ L ] w ⊑[ pos L ] w ∨[ L ] z ]
    φ z w = ∨-least L (∨-upper₁ L w z , ∨-upper₀ L w z)
```

Both operations are associative.

```agda
∧-assoc : (L : Lattice ℓ₀ ℓ₁)
        → (x y z : ∣ L ∣ₗ) → x ∧[ L ] (y ∧[ L ] z) ≡ (x ∧[ L ] y) ∧[ L ] z
∧-assoc L x y z = ⊑[ pos L ]-antisym _ _ down up
  where
    open PosetReasoning (pos L)

    p : [ x ∧[ L ] (y ∧[ L ] z) ⊑[ pos L ] y ]
    p = x ∧[ L ] (y ∧[ L ] z) ⊑⟨ ∧-lower₁ L _ _ ⟩
        y ∧[ L ] z            ⊑⟨ ∧-lower₀ L y z ⟩
        y                     ■

    q : [ x ∧[ L ] (y ∧[ L ] z) ⊑[ pos L ] z ]
    q = x ∧[ L ] (y ∧[ L ] z) ⊑⟨ ∧-lower₁ L _ _ ⟩
        y ∧[ L ] z            ⊑⟨ ∧-lower₁ L y z ⟩
        z                     ■

    r : [ (x ∧[ L ] y) ∧[ L ] z ⊑[ pos L ] x ]
    r = (x ∧[ L ] y) ∧[ L ] z ⊑⟨ ∧-lower₀ L _ _ ⟩ x ∧[ L ] y ⊑⟨ ∧-lower₀ L x y ⟩ x ■

    r′ : [ (x ∧[ L ] y) ∧[ L ] z ⊑[ pos L ] y ]
    r′ = (x ∧[ L ] y) ∧[ L ] z ⊑⟨ ∧-lower₀ L _ _ ⟩ x ∧[ L ] y ⊑⟨ ∧-lower₁ L x y ⟩ y ■

    s : [ (x ∧[ L ] y) ∧[ L ] z ⊑[ pos L ] (y ∧[ L ] z) ]
    s = ∧-greatest L (r′ , ∧-lower₁ L _ _)

    down : _
    down = ∧-greatest L ((∧-greatest L (∧-lower₀ L _ _ , p)) , q)

    up : _
    up = ∧-greatest L (r , s)

∨-assoc : (L : Lattice ℓ₀ ℓ₁)
        → (x y z : ∣ L ∣ₗ) → x ∨[ L ] (y ∨[ L ] z) ≡ (x ∨[ L ] y) ∨[ L ] z
∨-assoc L x y z = ⊑[ pos L ]-antisym _ _ down up
  where
    open PosetReasoning (pos L)

    r : [ y ⊑[ pos L ] ((x ∨[ L ] y) ∨[ L ] z) ]
    r = y ⊑⟨ ∨-upper₁ L x y ⟩ x ∨[ L ] y ⊑⟨ ∨-upper₀ L _ _ ⟩ (x ∨[ L ] y) ∨[ L ] z ■

    r′ : [ x ⊑[ pos L ] ((x ∨[ L ] y) ∨[ L ] z) ]
    r′ = x ⊑⟨ ∨-upper₀ L x y ⟩ x ∨[ L ] y ⊑⟨ ∨-upper₀ L _ _ ⟩ (x ∨[ L ] y) ∨[ L ] z ■

    p : [ (y ∨[ L ] z) ⊑[ pos L ] (x ∨[ L ] y) ∨[ L ] z ]
    p = ∨-least L (r , ∨-upper₁ L (x ∨[ L ] y) z)

    q′ : [ y ⊑[ pos L ] ((x ∨[ L ] y) ∨[ L ] z) ]
    q′ = y ⊑⟨ ∨-upper₁ L x y ⟩ x ∨[ L ] y ⊑⟨ ∨-upper₀ L _ _ ⟩ (x ∨[ L ] y) ∨[ L ] z ■

    q : [ (y ∨[ L ] z ) ⊑[ pos L ] ((x ∨[ L ] y) ∨[ L ] z) ]
    q = ∨-least L (q′ , ∨-upper₁ L _ _)

    down : [ x ∨[ L ] (y ∨[ L ] z) ⊑[ pos L ] (x ∨[ L ] y) ∨[ L ] z ]
    down = ∨-least L (r′ , q)

    s′ : [ y ⊑[ pos L ] x ∨[ L ] (y ∨[ L ] z) ]
    s′ = y ⊑⟨ ∨-upper₀ L y z ⟩ y ∨[ L ] z ⊑⟨ ∨-upper₁ L _ _ ⟩ x ∨[ L ] (y ∨[ L ] z) ■

    s : [ (x ∨[ L ] y) ⊑[ pos L ] x ∨[ L ] (y ∨[ L ] z) ]
    s = ∨-least L (∨-upper₀ L _ _ , s′)

    t : [ z ⊑[ pos L ] x ∨[ L ] (y ∨[ L ] z) ]
    t = z ⊑⟨ ∨-upper₁ L y z ⟩ y ∨[ L ] z ⊑⟨ ∨-upper₁ L _ _ ⟩ x ∨[ L ] (y ∨[ L ] z) ■

    up : [ (x ∨[ L ] y) ∨[ L ] z ⊑[ pos L ] x ∨[ L ] (y ∨[ L ] z) ]
    up = ∨-least L (s , t)
```

```agda
∧-absorb : (L : Lattice ℓ₀ ℓ₁)
         → (x y : ∣ L ∣ₗ)
         → x ∧[ L ] (y ∨[ L ] x) ≡ x
∧-absorb L x y = ⊑[ pos L ]-antisym _ _ down up
  where
    down : [ x ∧[ L ] (y ∨[ L ] x) ⊑[ pos L ] x ]
    down = ∧-lower₀ L x _

    up : [ x ⊑[ pos L ] (x ∧[ L ] (y ∨[ L ] x)) ]
    up = ∧-greatest L (⊑[ pos L ]-refl x , ∨-upper₁ L y x)

∨-absorb : (L : Lattice ℓ₀ ℓ₁)
         → (x y : ∣ L ∣ₗ)
         → x ∨[ L ] (y ∧[ L ] x) ≡ x
∨-absorb L x y = ⊑[ pos L ]-antisym _ _ down up
  where
    down : [ x ∨[ L ] (y ∧[ L ] x) ⊑[ pos L ] x ]
    down = ∨-least L (⊑[ pos L ]-refl x , ∧-lower₁ L y x)

    up : [ x ⊑[ pos L ] (x ∨[ L ] (y ∧[ L ] x)) ]
    up = ∨-upper₀ L x _
```

## Distributive

```agda
isDistributive : Lattice ℓ₀ ℓ₁ → Type ℓ₀
isDistributive L =
  (x y z : ∣ L ∣ₗ) → x ∧[ L ] (y ∨[ L ] z) ≡ (x ∧[ L ] y) ∨[ L ] (x ∧[ L ] z)

isDistributiveᵒᵖ : Lattice ℓ₀ ℓ₁ → Type ℓ₀
isDistributiveᵒᵖ L =
  (x y z : ∣ L ∣ₗ) → x ∨[ L ] (y ∧[ L ] z) ≡ (x ∨[ L ] y) ∧[ L ] (x ∨[ L ] z)

-- TODO: prove the following.
dist⇒distᵒᵖ : (L : Lattice ℓ₀ ℓ₁) → isDistributive L → isDistributiveᵒᵖ L
dist⇒distᵒᵖ L L-dist x y z =
  x ∨ (y ∧ z)                   ≡⟨ cong (λ - → x ∨ -) (∧-comm L y z)             ⟩
  x ∨ (z ∧ y)                   ≡⟨ cong (λ - → - ∨ _) (sym (∨-absorb L x z))     ⟩
  (x ∨ (z ∧ x)) ∨ (z ∧ y)       ≡⟨ sym (∨-assoc L x _ _)                         ⟩
  x ∨ ((z ∧ x) ∨ (z ∧ y))       ≡⟨ cong (λ - → x ∨ -) (sym (L-dist z x y))       ⟩
  x ∨ (z ∧ (x ∨ y))             ≡⟨ cong (λ - → x ∨ -) (∧-comm L z (x ∨ y))       ⟩
  x ∨ ((x ∨ y) ∧ z)             ≡⟨ cong (λ - → - ∨ (_ ∧ _)) (sym (∧-abs _ _))    ⟩
  (x ∧ (y ∨ x)) ∨ ((x ∨ y) ∧ z) ≡⟨ cong (λ - → (x ∧ -) ∨ ((_ ∨ _) ∧ z)) y∨x=x∨y  ⟩
  (x ∧ (x ∨ y)) ∨ ((x ∨ y) ∧ z) ≡⟨ cong (λ - → - ∨ ((x ∨ y) ∧ z)) (∧-comm L _ _) ⟩
  ((x ∨ y) ∧ x) ∨ ((x ∨ y) ∧ z) ≡⟨ sym (L-dist (x ∨ y) x z)                      ⟩
  (x ∨ y) ∧ (x ∨ z)             ∎
  where
    ∧-abs = ∧-absorb L

    _∨_ : ∣ L ∣ₗ → ∣ L ∣ₗ → ∣ L ∣ₗ
    _∨_ = λ x y → x ∨[ L ] y

    _∧_ : ∣ L ∣ₗ → ∣ L ∣ₗ → ∣ L ∣ₗ
    _∧_ = λ x y → x ∧[ L ] y

    y∨x=x∨y : y ∨ x ≡ x ∨ y
    y∨x=x∨y = ∨-comm L y x

```
