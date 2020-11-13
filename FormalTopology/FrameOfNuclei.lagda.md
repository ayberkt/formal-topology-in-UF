```agda
{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything hiding (_∧_)

open import Poset
open import Frame
open import Nucleus
open import Cubical.Functions.Logic      hiding   (_⊓_)
open import Cubical.Foundations.Prelude  using    (refl; sym; cong; _≡⟨_⟩_; _∎)
open import Cubical.Data.Sigma           using    (Σ≡Prop; _×_)
open import Cubical.Foundations.Function using    (const; _∘_)
open import Basis                        renaming (_⊓_ to _∧_)

module FrameOfNuclei (F : Frame ℓ₀ ℓ₁ ℓ₂) where
```

Preliminaries
=============

We assume a fixed frame `F` on which to define the frame of nuclei.

```agda
open PosetReasoning (pos F) using (_⊑⟨_⟩_; _■)
```

For simplicity, we will refer to the meet of `F` simply as `_⊓_`.

```agda
_⊓_ : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
x ⊓ y = x ⊓[ F ] y
```

Poset of nuclei on `F`
======================

```agda
_⊑N_ : Order (ℓ-max ℓ₀ ℓ₁) (Nucleus F)
(j , _) ⊑N (k , _) = ∀[ x ∶ ∣ F ∣F ] j x ⊑[ pos F ] k x

poset-of-nuclei-str : PosetStr (ℓ-max ℓ₀ ℓ₁) (Nucleus F)
poset-of-nuclei-str = _⊑N_ , Nucleus-set F , ⊑-refl , ⊑-trans , ⊑-antisym
  where
    ⊑-refl : [ isReflexive _⊑N_ ]
    ⊑-refl (j , _) x = ⊑[ pos F ]-refl (j x)

    ⊑-trans : [ isTransitive _⊑N_ ]
    ⊑-trans (j , _) (k , _) (l , _) j⊑k k⊑l x =
      j x ⊑⟨ j⊑k x ⟩ k x ⊑⟨ k⊑l x ⟩ l x ■

    ⊑-antisym : [ isAntisym (Nucleus-set F)  _⊑N_ ]
    ⊑-antisym (j , _) (k , _) j⊑k k⊑j =
      Σ≡Prop
        (isNuclear-prop F)
        (funExt λ x → ⊑[ pos F ]-antisym (j x) (k x) (j⊑k x) (k⊑j x))

poset-of-nuclei : Poset (ℓ-max ℓ₀ ℓ₁) (ℓ-max ℓ₀ ℓ₁)
poset-of-nuclei = (Nucleus F) , poset-of-nuclei-str
```

Frame of nuclei on `F`
======================

The top nucleus
---------------

```agda
𝟏 : Nucleus F
𝟏 = const ⊤[ F ] , 𝟎-N₀ , 𝟎-N₁ , 𝟎-N₂
  where
    𝟎-N₀ : _
    𝟎-N₀ _ _ = sym (x∧⊤=x F ⊤[ F ])

    𝟎-N₁ : _
    𝟎-N₁ = ⊤[ F ]-top

    𝟎-N₂ : _
    𝟎-N₂ _ = ⊑[ pos F ]-refl ⊤[ F ]
```

```agda
𝟏-top : (j : Nucleus F) → [ j ⊑[ poset-of-nuclei ] 𝟏 ]
𝟏-top (j , _) = ⊤[ F ]-top ∘ j
```

The meet of two nuclei
----------------------

```agda
_⊓N_ : Nucleus F → Nucleus F → Nucleus F
𝒿@(j , j-n₀ , j-n₁ , j-n₂) ⊓N 𝓀@(k , k-n₀ , k-n₁ , k-n₂) =
  (λ x → j x ⊓[ F ] k x) , ⊓-N₀ , ⊓-N₁ , ⊓-N₂
  where
    ⊓-N₀ : _
    ⊓-N₀ x y =
      j (x ⊓ y) ⊓ k (x ⊓ y)        ≡⟨ ⦅𝟏⦆ ⟩
      j (x ⊓ y) ⊓ (k x ⊓ k y)      ≡⟨ ⦅𝟐⦆ ⟩
      (j (x ⊓ y) ⊓ k x) ⊓ k y      ≡⟨ ⦅𝟑⦆ ⟩
      (k x ⊓ j (x ⊓ y)) ⊓ k y      ≡⟨ ⦅𝟒⦆ ⟩
      (k x ⊓ (j x ⊓ j y)) ⊓ k y    ≡⟨ ⦅𝟓⦆ ⟩
      ((k x ⊓ j x) ⊓ j y) ⊓ k y    ≡⟨ ⦅𝟔⦆ ⟩
      ((j x ⊓ k x) ⊓ j y) ⊓ k y    ≡⟨ ⦅𝟕⦆ ⟩
      (j x ⊓ k x) ⊓ (j y ⊓ k y)    ∎
      where
        ⦅𝟏⦆ = cong (λ - → j (x ⊓ y) ⊓ -) (k-n₀ x y)
        ⦅𝟐⦆ = sym (⊓[ F ]-assoc (j (x ⊓ y)) (k x) (k y)) 
        ⦅𝟑⦆ = cong (λ - → - ⊓ k y) (comm F (j (x ⊓ y)) (k x))
        ⦅𝟒⦆ = cong (λ - → (k x ⊓ -) ⊓ k y) (j-n₀ x y)
        ⦅𝟓⦆ = cong (λ - → - ⊓ k y) (sym (⊓[ F ]-assoc _ _ _))
        ⦅𝟔⦆ = cong (λ - → (- ⊓ j y) ⊓ k y) (comm F _ _)
        ⦅𝟕⦆ = ⊓[ F ]-assoc _ _ _


    ⊓-N₁ : _
    ⊓-N₁ x = ⊓[ F ]-greatest (j x) (k x) x (j-n₁ x) (k-n₁ x)

    ⊓-N₂ : _
    ⊓-N₂ x =
      j (j x ⊓ k x) ⊓ k (j x ⊓ k x)             ⊑⟨ ⦅𝟏⦆ ⟩
      (j (j x) ⊓ j (k x)) ⊓ k (j x ⊓ k x)       ⊑⟨ ⦅𝟐⦆ ⟩
      (j (j x) ⊓ j (k x)) ⊓ (k (j x) ⊓ k (k x)) ⊑⟨ ⦅𝟑⦆ ⟩
      (j (j x) ⊓ j (k x)) ⊓ k (k x)             ⊑⟨ ⦅𝟒⦆ ⟩
      (j (j x)) ⊓ (k (k x))                     ⊑⟨ ⦅𝟓⦆ ⟩
      (j x) ⊓ (k (k x))                         ⊑⟨ ⦅𝟔⦆ ⟩
      (j x) ⊓ (k x) ■
      where
        ⦅𝟏⦆ = cleft  F _ (≡⇒⊑ (pos F) (j-n₀ _ _))
        ⦅𝟐⦆ = cright F _ (≡⇒⊑ (pos F) (k-n₀ _ _))
        ⦅𝟑⦆ = cright F _ (⊓[ F ]-lower₁ _ _)
        ⦅𝟒⦆ = cleft  F _ (⊓[ F ]-lower₀ (j (j x)) (j (k x)))
        ⦅𝟓⦆ = cleft  F _ (j-n₂ x)
        ⦅𝟔⦆ = cright F _ (k-n₂ x)
```

```agda
⊓N-meet : [ isGLB poset-of-nuclei _⊓N_ ]
⊓N-meet = lb , greatest where

  lb : (j k : Nucleus F) → [ (j ⊓N k) ⊑N j ∧ (j ⊓N k) ⊑N k ]
  lb (j , _) (k , _) = (λ x → ⊓[ F ]-lower₀ (j x) (k x))
                      , (λ x → ⊓[ F ]-lower₁ (j x) (k x))

  greatest : (j k l : Nucleus F) → [ l ⊑N j ∧ l ⊑N k ⇒ l ⊑N (j ⊓N k) ]
  greatest (j , _) (k , _) (l , _) (l⊑j , l⊑k) x =
    ⊓[ F ]-greatest (j x) (k x) (l x) (l⊑j x) (l⊑k x)
```

Arbitrary join of nuclei
------------------------

```agda
⋁N_ : Fam ℓ₂ (Nucleus F) → Nucleus F
⋁N J = {!!}
```

```agda
⋁N-join : {![ isLUB ? ? ]!}
⋁N-join = {!!}
```

Distributivity
--------------

```agda
distr-N : [ isDist poset-of-nuclei _⊓N_ ⋁N_ ]
distr-N = {!!}
```

```agda
frame-of-nuclei-raw-str : RawFrameStr (ℓ-max ℓ₀ ℓ₁) ℓ₂ (Nucleus F)
frame-of-nuclei-raw-str = poset-of-nuclei-str , 𝟏 , _⊓N_ , ⋁N_

frame-of-nuclei-str : FrameStr (ℓ-max ℓ₀ ℓ₁) ℓ₂ (Nucleus F)
frame-of-nuclei-str = frame-of-nuclei-raw-str , axioms
  where
    axioms : [ FrameAx (poset-of-nuclei-str , 𝟏 , _⊓N_ , ⋁N_) ]
    axioms = 𝟏-top , (⊓N-meet , {!!} , {!!})
```

The final definition
--------------------

```agda
frame-of-nuclei : Frame (ℓ-max ℓ₀ ℓ₁) (ℓ-max ℓ₀ ℓ₁) ℓ₂
frame-of-nuclei =
  Nucleus F , frame-of-nuclei-raw-str , 𝟏-top , ⊓N-meet , {!!} , distr-N
```
