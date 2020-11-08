---
title: Semilattice
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

module Semilattice where

open import Basis hiding (A; A₀)
open import Poset
```
-->

Definition
==========

```agda
RawJoinSemilatticeStr : (ℓ₁ : Level) → Type ℓ₀ → Type (ℓ-max ℓ₀ (ℓ-suc ℓ₁))
RawJoinSemilatticeStr ℓ₁ A = PosetStr ℓ₁ A × A × (A → A → A)
```

```
satJoinSemilatticeAxioms : (A : Type ℓ₀)
                         → RawJoinSemilatticeStr ℓ₁ A
                         → hProp (ℓ-max ℓ₀ ℓ₁)
satJoinSemilatticeAxioms A (P , ⊥ , _∨_) =
  isBottom (A , P) ⊥ ⊓ (∀[ x ∶ A ] ∀[ y ∶ A ] isJoinOf (A , P) (x ∨ y) x y)
```

```agda
JoinSemilatticeStr : (ℓ₁ : Level) → Type ℓ₀ → Type (ℓ-max ℓ₀ (ℓ-suc ℓ₁))
JoinSemilatticeStr ℓ₁ A =
  Σ[ s ∈ RawJoinSemilatticeStr ℓ₁ A ] [ satJoinSemilatticeAxioms A s ]
```

```agda
JoinSemilattice : (ℓ₀ ℓ₁ : Level) → Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁))
JoinSemilattice ℓ₀ ℓ₁ = Σ[ A ∈ Type ℓ₀ ] JoinSemilatticeStr ℓ₁ A
```

Projections
-----------

```agda
module JoinSemilatticeNotation (S : JoinSemilattice ℓ₀ ℓ₁) where

  carrier = π₀ S

  pos : Poset ℓ₀ ℓ₁
  pos = carrier , (π₀ (π₀ (π₁ S)))

  𝟎 : carrier
  𝟎 = π₀ (π₁ (π₀ (π₁ S)))

  𝟎-bottom : [ isBottom pos 𝟎 ]
  𝟎-bottom = π₀ (π₁ (π₁ S))

  _∨_ : carrier → carrier → carrier
  _∨_ = π₁ (π₁ (π₀ (π₁ S)))

  ∨-upper : [ ∀[ x ] ∀[ y ] ⟨ x , y ⟩⊑[ pos ] (x ∨ y) ]
  ∨-upper x y = π₀ (π₁ (π₁ (π₁ S)) x y)

  ∨-least : [ ∀[ x ] ∀[ y ] ∀[ z ] ⟨ x , y ⟩⊑[ pos ] z ⇒ (x ∨ y) ⊑[ pos ] z ]
  ∨-least x y = π₁ (π₁ (π₁ (π₁ S)) x y)
```

Join-semilattice homomorphism
-----------------------------

```agda
open JoinSemilatticeNotation

module JSMap (L₀ : JoinSemilattice ℓ₀ ℓ₁) (L₁ : JoinSemilattice ℓ₀′ ℓ₁′) (f : carrier L₀ → carrier L₁) where

  open JoinSemilatticeNotation L₀ using    ()
                                  renaming (_∨_ to _∨₀_; carrier to A₀; 𝟎 to 𝟎₀)
  open JoinSemilatticeNotation L₁ using    ()
                                  renaming (_∨_ to _∨₁_; 𝟎 to 𝟎₁)

  respects-⊥ : hProp ℓ₀′
  respects-⊥ = (f 𝟎₀ ≡ 𝟎₁) , carrier-is-set (pos L₁) _ _

  respects-∨ : hProp (ℓ-max ℓ₀ ℓ₀′)
  respects-∨ =
    ∀[ x ] ∀[ y ] (f (x ∨₀ y) ≡ f x ∨₁ f y) ,  carrier-is-set (pos L₁) _ _

  isJoinSemilatticeHomomorphism : hProp (ℓ-max ℓ₀ ℓ₀′)
  isJoinSemilatticeHomomorphism = respects-⊥ ⊓ respects-∨
```
