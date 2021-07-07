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
RawJoinSemilatticeStr : Type ℓ₀ → Type ℓ₀
RawJoinSemilatticeStr A = A × (A → A → A)
```

```agda
isCommutative : (A : Type ℓ₀) → isSet A → (A → A → A) → hProp ℓ₀
isCommutative A A-set _⊕_ = ∀[ x ] ∀[ y ] (x ⊕ y ≡ y ⊕ x) , A-set _ _
```

```agda
isAssoc : (A : Type ℓ₀) → isSet A → (A → A → A) → hProp ℓ₀
isAssoc A A-set _⊕_ =
  ∀[ x ] ∀[ y ] ∀[ z ] ((x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)) , (A-set _ _)
```

```agda
isUnit : {A : Type ℓ₀} → isSet A → A → (A → A → A) → hProp ℓ₀
isUnit A-set ε _⊕_ = ∀[ x ] (ε ⊕ x ≡ x) , A-set _ _
```

```agda
isIdempotent : {A : Type ℓ₀} → isSet A → (A → A → A) → hProp ℓ₀
isIdempotent {A = A} A-set _⊕_ = ∀[ x ] (x ⊕ x ≡ x) , A-set (x ⊕ x) x
```

```
satJoinSemilatticeAxioms : (A : Type ℓ₀) → RawJoinSemilatticeStr A → hProp ℓ₀
satJoinSemilatticeAxioms {ℓ₀ = ℓ₀} A (⊥ , _∨_) =
  (Σ[ A-set ∈ isSet A ] [ satAxioms A-set ]) , is-prop where
    satAxioms : isSet A → hProp ℓ₀
    satAxioms A-set = isCommutative A A-set _∨_
                    ⊓ isAssoc A A-set _∨_
                    ⊓ isUnit A-set ⊥ _∨_
                    ⊓ isIdempotent A-set _∨_

    is-prop : isProp (Σ[ A-set ∈ isSet A ] [ satAxioms A-set ])
    is-prop = isPropΣ isPropIsSet (isProp[] ∘ satAxioms)
```

```agda
JoinSemilatticeStr : Type ℓ₀ → Type ℓ₀
JoinSemilatticeStr A =
  Σ[ s ∈ RawJoinSemilatticeStr A ] [ satJoinSemilatticeAxioms A s ]
```

```agda
JoinSemilattice : (ℓ₀ : Level) → Type (ℓ-suc ℓ₀)
JoinSemilattice ℓ₀ = Σ[ A ∈ Type ℓ₀ ] JoinSemilatticeStr A
```

Projections
-----------

```agda
module JoinSemilatticeNotation (S : JoinSemilattice ℓ₀) where

  carrier = π₀ S

  _∨_ : carrier → carrier → carrier
  _∨_ = π₁ (π₀ (π₁ S))

  carrier-set : isSet carrier
  carrier-set = π₀ (π₁ (π₁ S))

  ∨-idem : [ isIdempotent carrier-set _∨_ ]
  ∨-idem = π₁ (π₁ (π₁ (π₁ (π₁ (π₁ S))))) 

  ∨-assoc : [ isAssoc carrier carrier-set _∨_ ]
  ∨-assoc = π₀ (π₁ (π₁ (π₁ (π₁ S)))) 

  ∨-comm : [ isCommutative carrier carrier-set _∨_ ]
  ∨-comm = π₀ (π₁ (π₁ (π₁ S)))

  pos : Poset ℓ₀ ℓ₀
  pos = carrier , pstr where

    _⊑_ : carrier → carrier → hProp ℓ₀
    x ⊑ y = (π₁ (π₀ (π₁ S)) x y ≡ y) , π₀ (π₁ (π₁ S)) _ _

    ⊑-refl : [ isReflexive _⊑_ ]
    ⊑-refl x = ∨-idem x

    ⊑-trans : [ isTransitive _⊑_ ]
    ⊑-trans x y z x⊑y y⊑z =
      x ∨ z               ≡⟨ cong (x ∨_) (sym y⊑z)               ⟩
      x ∨ (y ∨ z)         ≡⟨ cong (λ - → x ∨ (- ∨ z)) (sym x⊑y)  ⟩
      (x ∨ ((x ∨ y) ∨ z)) ≡⟨ sym (∨-assoc x (x ∨ y) z)           ⟩
      ((x ∨ (x ∨ y)) ∨ z) ≡⟨ sym (cong (_∨ z) (∨-assoc x x y))   ⟩
      (((x ∨ x) ∨ y) ∨ z) ≡⟨ cong (λ - → (- ∨ y) ∨ z) (∨-idem x) ⟩
      ((x ∨ y) ∨ z)       ≡⟨ cong (_∨ z) x⊑y                     ⟩
      (y ∨ z)             ≡⟨ y⊑z                                 ⟩
      z                   ∎

    ⊑-antisym : [ isAntisym carrier-set _⊑_ ]
    ⊑-antisym x y x⊑y y⊑x =
      x ≡⟨ sym y⊑x ⟩ y ∨ x ≡⟨ ∨-comm y x ⟩ x ∨ y ≡⟨ x⊑y ⟩ y ∎

    pstr : PosetStr ℓ₀ carrier
    pstr = _⊑_ , (π₀ (π₁ (π₁ S))) , ⊑-refl , ⊑-trans , ⊑-antisym

  𝟎 : carrier
  𝟎 = π₀ (π₀ (π₁ S))

  𝟎-bottom : [ isBottom pos 𝟎 ]
  𝟎-bottom = π₀ (π₁ (π₁ (π₁ (π₁ (π₁ S)))))

  ∨-upper : [ ∀[ x ] ∀[ y ] ⟨ x , y ⟩⊑[ pos ] (x ∨ y) ]
  ∨-upper x y = x⊑x∨y , y⊑x∨y where

    x⊑x∨y : [ x ⊑[ pos ] (x ∨ y) ]
    x⊑x∨y = x ∨ (x ∨ y)   ≡⟨ sym (∨-assoc x x y)    ⟩
            (x ∨ x) ∨ y   ≡⟨ cong (_∨ y) (∨-idem x) ⟩
            (x ∨ y)       ∎

    y⊑x∨y : [ y ⊑[ pos ] (x ∨ y) ]
    y⊑x∨y = y ∨ (x ∨ y)   ≡⟨ cong (y ∨_) (∨-comm x y)      ⟩
            y ∨ (y ∨ x)   ≡⟨ sym (∨-assoc y y x)           ⟩
            (y ∨ y) ∨ x   ≡⟨ cong (λ - → - ∨ x) (∨-idem y) ⟩
            y ∨ x         ≡⟨ ∨-comm y x                    ⟩
            x ∨ y         ∎

  ∨-least : [ ∀[ x ] ∀[ y ] ∀[ z ] ⟨ x , y ⟩⊑[ pos ] z ⇒ (x ∨ y) ⊑[ pos ] z ]
  ∨-least x y z (x⊑z , y⊑z) = (x ∨ y) ∨ z          ≡⟨ ∨-assoc x y z   ⟩
                              x ∨ (y ∨ z)          ≡⟨ cong (x ∨_) y⊑z ⟩
                              x ∨ z                ≡⟨ x⊑z             ⟩
                              z                    ∎
```

Join-semilattice homomorphism
-----------------------------

```agda
open JoinSemilatticeNotation

module JSMap (L₀ : JoinSemilattice ℓ₀)
             (L₁ : JoinSemilattice ℓ₀′)
             (f : carrier L₀ → carrier L₁) where

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
