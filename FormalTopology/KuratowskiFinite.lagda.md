---
title: Kuratowski Finiteness
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

module KuratowskiFinite where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Empty using (rec)
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Foundations.Logic
open import Cubical.Data.Unit

private
  variable
    ℓ ℓ₀ ℓ₁ : Level
```
-->

## Definition ##

```agda
isSurjective : {A : Type ℓ₀} {B : Type ℓ₁} → (A → B) → Type (ℓ-max ℓ₀ ℓ₁)
isSurjective {A = A} {B} f = (y : B) → Σ[ x ∈ A ] f x ≡ y
```

```agda
Ψ : (ℓ : Level) → Type (ℓ-suc ℓ)
Ψ ℓ = Σ[ A ∈ Type ℓ ] isSet A
```

```agda
_↠_ : Type ℓ₀ → Type ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
A ↠ B = Σ[ f ∈ (A → B) ] isSurjective f
```

```agda
isKFin : (A : Ψ ℓ) → ℙ (fst A) → Type ℓ
isKFin A U = Σ[ n ∈ ℕ ] Fin n ↠ (Σ[ x ∈ fst A ] [ U x ])
```

```agda
KFin : Ψ ℓ → Type (ℓ-suc ℓ)
KFin A = Σ[ U ∈ ℙ (fst A) ] isKFin A U

+-lemma : {m n : ℕ} → m + suc (suc n) ≡ 1 → [ ⊥ ]
+-lemma {m} {n} p = snotz (injSuc q)
  where
    q : suc (suc n) + m ≡ 1
    q = subst (λ - → - ≡ 1) (+-comm m (suc (suc n))) p

η : {A : Ψ ℓ} → fst A → KFin A
η {A = (A , A-set)} x = (λ y → (x ≡ y) , A-set x y) , singleton-kfin
  where
    singleton-kfin : isKFin (A , A-set) (λ y → (x ≡ y) , A-set x y)
    singleton-kfin = 1 , (f , f-surj)
      where
        f : Fin 1 → Σ[ y ∈ A ] [ (x ≡ y) , A-set x y ]
        f (zero  , _)     = x , refl
        f (suc n , _ , p) = rec (+-lemma p)

        0<1 : 0 < 1
        0<1 = 0 , refl

        f-surj : isSurjective f
        f-surj (y , x=y) =
          (0 , 0<1) , Σ≡Prop (λ _ → isProp[] ((x ≡ _) , A-set x _)) x=y
```
