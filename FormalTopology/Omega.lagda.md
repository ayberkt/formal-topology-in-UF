---
title: The Initial Frame
author: Ayberk Tosun
---

```agda
{-# OPTIONS --cubical --safe #-}

module Omega where

open import Basis
open import Cubical.Data.Sigma hiding (_∨_)
open import Cubical.Functions.Logic
open import Cubical.Foundations.Function
open import Poset
open import Frame

```

## Definition

```agda
_≤_ : hProp 𝓤 → hProp 𝓤 → hProp 𝓤
A ≤ B = A ⇒ B

ΩP-str : (𝓤 : Universe) → PosetStr 𝓤 (hProp 𝓤)
ΩP-str 𝓤 = _≤_ , isSetHProp , ≤-reflexive , ≤-trans , ≤-antisym
  where
  ≤-reflexive : [ isReflexive _≤_ ]
  ≤-reflexive x = idfun _

  ≤-trans : [ isTransitive _≤_ ]
  ≤-trans _ _ _ p q = q ∘ p

  ≤-antisym : [ isAntisym isSetHProp _≤_ ]
  ≤-antisym _ _ = ⇔toPath
```

```agda
ΩP : (𝓤 : Universe) → Poset (𝓤 ⁺) 𝓤
ΩP 𝓤 = hProp 𝓤 , ΩP-str 𝓤
```

```agda
ΩF : (𝓤 : Universe) → Frame (𝓤 ⁺) 𝓤 𝓤
ΩF 𝓤 =
  (hProp 𝓤) , (ΩP-str 𝓤 , top 𝓤 , _⊓_ , ⋁_) , is-top , is-glb , is-lub , distr
  where
  ⋁_ : Fam 𝓤 (hProp 𝓤) → hProp 𝓤
  ⋁ (I , f) = ∥ (Σ[ i ∈ I ] [ f i ]) ∥Ω

  is-top : [ isTop (ΩP 𝓤) (top 𝓤) ]
  is-top _ _ = tt

  is-glb : [ isGLB (ΩP 𝓤) _⊓_ ]
  is-glb = (λ _ _ → fst , snd) , λ x y z p q → fst p q , snd p q

  is-lub : [ isLUB (ΩP 𝓤) ⋁_ ]
  is-lub = (λ { U _ (i , eq) q → ∣ i , subst [_] (sym eq) q ∣ }) , nts
    where
    nts : (U : Fam 𝓤 (hProp 𝓤)) (A : hProp 𝓤)
        → [ ∀[ B ε U ] (B ≤ A) ⇒ (⋁ U) ≤ A ]
    nts U x p q = ∥∥-rec (isProp[] x) rem q
      where
      rem : Σ[ i ∈ index U ] [ U $ i ] → [ x ]
      rem (i , eq) = p (U $ i) (i , refl) eq

  distr : [ isDist (ΩP 𝓤)  _⊓_ ⋁_ ]
  distr A U = ⇔toPath nts₀ nts₁
    where
    open JoinSyntax (hProp 𝓤) ⋁_

    nts₀ : _
    nts₀ (x , y) = ∥∥-rec (∥∥-prop _) (λ { (i , Uᵢ) → ∣ i , x , Uᵢ ∣ }) y

    nts₁ : [ ⋁⟨ i ⟩ (A ⊓ (U $ i)) ⇒ A ⊓ (⋁ U) ]
    nts₁ y = ∥∥-rec (isProp[] (A ⊓ (⋁ U))) (λ { (i , x , y) → x , ∣ i , y ∣ }) y
```
