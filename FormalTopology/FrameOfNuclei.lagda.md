---
title: The Patch Frame in Univalent Type Theory
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Poset
open import Frame
open import Nucleus
open import Prenucleus
open import Cubical.Functions.Logic      hiding   (_⊓_)
open import Cubical.Data.Sigma           using    (Σ≡Prop; _×_)
open import Cubical.Foundations.Function using    (const; _∘_; idfun; uncurry)
open import Cubical.Data.List            hiding   ([_])
open import Cubical.Data.List.Properties
open import Basis                        renaming (_⊓_ to _∧_; π₀ to fst; π₁ to snd) hiding (J)
```
-->

**Based on work by Martín Escardó.**

Preliminaries
=============

We assume a fixed frame `F` on which to define the frame of nuclei.

```agda
module FrameOfNuclei (F : Frame 𝒰 𝒱 𝒲) where
```

```agda
open PosetReasoning (pos F) using (_⊑⟨_⟩_; _■)
```

For simplicity, we will refer to the order, the meet, and the join of `F` simply
as `⊑`, _⊓_`, and `⋁_`.

```agda
_⊑_ : ∣ F ∣F → ∣ F ∣F → hProp 𝒱
x ⊑ y = x ⊑[ pos F ] y

_⊓_ : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
x ⊓ y = x ⊓[ F ] y

⋁_ : Fam 𝒲 ∣ F ∣F → ∣ F ∣F
⋁ U = ⋁[ F ] U
```

We define the notion of Scott-continuity of a nucleus on `F` as follows:

```agda
isScottCont′ : (∣ F ∣F → ∣ F ∣F) → (𝒰 ∨ 𝒱 ∨ 𝒲 ⁺) ̇
isScottCont′ j =
  (U : Fam 𝒲 ∣ F ∣F) →
    [ isDirected (pos F) U ] → j (⋁ U) ≡ ⋁[ F ] ⁅ j x ∣ x ε U ⁆

isScottCont : Nucleus F → (𝒰 ∨ 𝒱 ∨ 𝒲 ⁺) ̇
isScottCont (j , _) = isScottCont′ j
```

The type expression the notion of being Scott-continuous is an h-proposition
as one would expect:

```agda
isScottCont-prop : (𝒿 : Nucleus F) → isProp (isScottCont 𝒿)
isScottCont-prop j =
  isPropΠ λ U → isPropΠ λ d → carrier-is-set (pos F) _ _
```

We define a shorthand for the type of Scott-continuous nuclei as we will be
primarily interested in those:

```agda
ScottContNucleus : (𝒰 ∨ 𝒱 ∨ 𝒲 ⁺) ̇
ScottContNucleus = Σ[ j ∈ Nucleus F ] isScottCont j

ScottContNucleus-set : isSet ScottContNucleus
ScottContNucleus-set =
  isSetΣ (Nucleus-set F) (isProp→isSet ∘ isScottCont-prop)
```

Poset of nuclei on `F` (`𝔑`)
======================

The set of endofunctions on a given frame forms a poset under the pointwise
order; we denote by `_⊑f_` this pointwise order and by `𝔉` this poset.

```agda
_⊑f_ : (∣ F ∣F → ∣ F ∣F) → (∣ F ∣F → ∣ F ∣F) → hProp (𝒰 ∨ 𝒱)
f ⊑f g = ∀[ x ∶ ∣ F ∣F ] f x ⊑[ pos F ] g x

⊑f-refl : [ isReflexive _⊑f_ ]
⊑f-refl f x = ⊑[ pos F ]-refl (f x)

⊑f-trans : [ isTransitive _⊑f_ ]
⊑f-trans f g h f⊑g g⊑h x = f x ⊑⟨ f⊑g x ⟩ g x ⊑⟨ g⊑h x ⟩ h x ■

is-set : isSet (∣ F ∣F → ∣ F ∣F)
is-set = isSetΠ λ x → carrier-is-set (pos F)

⊑f-antisym : [ isAntisym is-set _⊑f_ ]
⊑f-antisym f g f⊑g g⊑h =
  funExt λ x → ⊑[ pos F ]-antisym (f x) (g x) (f⊑g x) (g⊑h x)

𝔉 : Poset 𝒰 (𝒰 ∨ 𝒱)
𝔉 = (∣ F ∣F → ∣ F ∣F) , _⊑f_ , is-set , ⊑f-refl , ⊑f-trans , ⊑f-antisym

_∙∧∙_ : (∣ F ∣F → ∣ F ∣F) → (∣ F ∣F → ∣ F ∣F) → ∣ F ∣F → ∣ F ∣F
j ∙∧∙ k = λ x → j x ⊓[ F ] k x
```

We denote by `𝔑` the poset of nuclei:

```agda
poset-of-nuclei-str : PosetStr (𝒰 ∨ 𝒱) (Nucleus F)
poset-of-nuclei-str = _⊑n_ , Nucleus-set F , ⊑f-refl ∘ fst , ⊑-trans , ⊑-antisym
  where
  _⊑n_ : Order (𝒰 ∨ 𝒱) (Nucleus F)
  (j , _) ⊑n (k , _) = j ⊑f k

  ⊑-trans : [ isTransitive _⊑n_ ]
  ⊑-trans (j , _) (k , _) (l , _) j⊑k k⊑l = ⊑f-trans j k l j⊑k k⊑l

  ⊑-antisym : [ isAntisym (Nucleus-set F)  _⊑n_ ]
  ⊑-antisym (j , _) (k , _) j⊑k k⊑j =
    Σ≡Prop (isNuclear-prop F) (⊑f-antisym j k j⊑k k⊑j)

𝔑 : Poset (𝒰 ∨ 𝒱) (𝒰 ∨ 𝒱)
fst 𝔑 = Nucleus F
snd 𝔑 = poset-of-nuclei-str
```

Frame of Scott-continuous nuclei on `F`
=======================================

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
𝟏-top : (j : Nucleus F) → [ j ⊑[ 𝔑 ] 𝟏 ]
𝟏-top (j , _) = ⊤[ F ]-top ∘ j
```

```agda
-- 𝟏-sc : isScottCont (const ⊤[ F ])
-- 𝟏-sc U (∣i∣ , _) = ⊑[ pos F ]-antisym _ _ down up where

--   down : [ ⊤[ F ] ⊑[ pos F ] (⋁[ F ] fmap (const ⊤[ F ]) U) ]
--   down = ∥∥-rec (isProp[] (_ ⊑[ pos F ] _)) rem ∣i∣ where

--     rem : _
--     rem i = ⋁[ F ]-upper ((const ⊤[ F ]) ⟨$⟩ U) ⊤[ F ] (i , refl)

--   up : [ (⋁[ F ] ((const ⊤[ F ]) ⟨$⟩ U)) ⊑[ pos F ] ⊤[ F ] ]
--   up = ⊤[ F ]-top (⋁[ F ] ((const ⊤[ F ]) ⟨$⟩ U))

𝟏sc : ScottContNucleus
fst 𝟏sc = 𝟏
snd 𝟏sc U (∣i∣ , _) =
  ⊑[ pos F ]-antisym _ _ down (⊤[ F ]-top _)
  where
  down : [ ⊤[ F ] ⊑[ pos F ] ⋁[ F ] (const ⊤[ F ] ⟨$⟩ U) ]
  down = ∥∥-rec (isProp[] (_ ⊑ _)) (λ i → ⋁[ F ]-upper _ _ (i , refl)) ∣i∣
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
⊓N-meet : [ isGLB 𝔑 _⊓N_ ]
⊓N-meet = lb , greatest where

  lb : (j k : Nucleus F) → [ (j ⊓N k) ⊑[ 𝔑 ] j ∧ (j ⊓N k) ⊑[ 𝔑 ] k ]
  lb (j , _) (k , _) = (λ x → ⊓[ F ]-lower₀ (j x) (k x))
                      , (λ x → ⊓[ F ]-lower₁ (j x) (k x))

  greatest : (j k l : Nucleus F) → [ l ⊑[ 𝔑 ] j ∧ l ⊑[ 𝔑 ] k ⇒ l ⊑[ 𝔑 ] (j ⊓N k) ]
  greatest (j , _) (k , _) (l , _) (l⊑j , l⊑k) x =
    ⊓[ F ]-greatest (j x) (k x) (l x) (l⊑j x) (l⊑k x)

```

The meet of two Scott-continuous nuclei is Scott-continuous.

```agda
⊓N-sc : (𝒿 𝓀 : Nucleus F) → isScottCont 𝒿 → isScottCont 𝓀 → isScottCont (𝒿 ⊓N 𝓀)
⊓N-sc 𝒿@(j , _) 𝓀@(k , _) j-sc k-sc U U-dir@(_ , U-up) =
  j (⋁ U) ⊓ k (⋁ U)                                             ≡⟨ ⦅𝟏⦆ ⟩
  (⋁ ⁅ j x ∣ x ε U ⁆) ⊓ k (⋁ U)                                 ≡⟨ ⦅𝟐⦆ ⟩
  (⋁ ⁅ j x ∣ x ε U ⁆) ⊓ (⋁ ⁅ k x ∣ x ε U ⁆)                     ≡⟨ ⦅𝟑⦆ ⟩
  ⋁ (⁅ j (U $ m) ⊓ k (U $ n) ∣ (m , n) ∶ (index U × index U) ⁆) ≡⟨ ⦅𝟒⦆ ⟩
  ⋁ ⁅ j x ⊓ k x ∣ x ε U ⁆ ∎
  where
    ⦅𝟒c⦆ : [ ∀[ z ε _ ] (z ⊑[ pos F ] ⋁ ⁅ j x ⊓ k x ∣ x ε U ⁆) ]
    ⦅𝟒c⦆ z ((m , n) , eq) =
      ∥∥-rec (isProp[] (z ⊑[ pos F ] _)) nts (U-up m n) where

        nts : _
        nts (o , (Uₘ⊑Uₒ , Uₙ⊑Uₒ)) =
          z                       ⊑⟨ ≡⇒⊑ (pos F) (sym eq)            ⟩
          j (U $ m) ⊓ k (U $ n)   ⊑⟨ cleft F _ (mono F 𝒿 _ _ Uₘ⊑Uₒ ) ⟩
          j (U $ o) ⊓ k (U $ n)   ⊑⟨ cright F _ (mono F 𝓀 _ _ Uₙ⊑Uₒ) ⟩
          j (U $ o) ⊓ k (U $ o)   ⊑⟨ ⋁[ F ]-upper _ _ (o , refl)     ⟩
          ⋁ ⁅ j x ⊓ k x ∣ x ε U ⁆ ■

    ⦅𝟒a⦆ = ⋁[ F ]-least _ _ ⦅𝟒c⦆

    ⦅𝟒b⦆ = ⋁[ F ]-least _ _ λ { z (i , eq) → ⋁[ F ]-upper _ _ ((i , i) , eq) }

    ⦅𝟏⦆  = cong (λ - → - ⊓ _) (j-sc U U-dir)
    ⦅𝟐⦆  = cong (λ - → _ ⊓ -) (k-sc U U-dir)
    ⦅𝟑⦆  = sym-distr F ⁅ j x ∣ x ε U ⁆ ⁅ k x ∣ x ε U ⁆
    ⦅𝟒⦆  = ⊑[ pos F ]-antisym _ _ ⦅𝟒a⦆ ⦅𝟒b⦆
```

```agda
_⊓sc_ : ScottContNucleus → ScottContNucleus → ScottContNucleus
_⊓sc_ (𝒿@(j , _) , j-sc) (𝓀@(k , _) , k-sc) = 𝒿 ⊓N 𝓀 , ⊓N-sc 𝒿 𝓀 j-sc k-sc
```

Arbitrary join of nuclei
------------------------

### Directification of a family of nuclei

This is the non-trivial part of this development.

We first define following function `ℜ` such that, given a family `U ≔ { fᵢ : A →
A ∣ i ∈ I }` of endofunctions, and a list `i₀, …, iₙ` of indices from `I`, `ℜ U
[i₀, …, iₙ]` denotes the composition `fᵢₙ ∘ ⋯ ∘ fᵢ₀`.

```agda
ℜ : {A : Type ℓ} → (α : Fam ℓ′ (A → A)) → List (index α) → A → A
ℜ α []       = idfun _
ℜ α (i ∷ is) = ℜ α is ∘ (α $ i)
```

Using `ℜ`, we define the family obtained from such a family of endofunctions
that consists of all such compositions.

```agda
ℜ-fam : {A : Type ℓ₀} (α : Fam ℓ₂ (A → A)) → Fam ℓ₂ (A → A)
ℜ-fam {A = A} α = List (index α) , ℜ α
```

We will use this function to compute the join of a family of nuclei. The key
idea is that the family of compositions is a directed family even if the family
we start with is not.

Notice that the identity function is always a (pre)nucleus.

```agda
id-is-nuclear : (F : Frame ℓ₀ ℓ₁ ℓ₂) → isPrenuclear F (idfun ∣ F ∣F)
id-is-nuclear F = (λ _ _ → refl) , ⊑[ pos F ]-refl
```

Compositions of prenuclei are prenuclei meaning given a family of nuclei, its
`ℜ-fam` is a family of prenuclei

```agda
ℜ-fam-prenucleus : (α : Fam ℓ₂ (∣ F ∣F → ∣ F ∣F))
                   → ((i : index α) → isPrenuclear F (α $ i))
                   → (is : List (index α)) → isPrenuclear F ((ℜ-fam α) $ is)
ℜ-fam-prenucleus α φ []       = id-is-nuclear F
ℜ-fam-prenucleus α φ (i ∷ is) = n₀ , n₁
  where
  j = ℜ-fam α $ (i ∷ is)

  j′ : ∣ F ∣F → ∣ F ∣F
  j′ = ℜ-fam α $ is

  ih : isPrenuclear F j′
  ih = ℜ-fam-prenucleus α φ is

  j′-n₀ : (x y : ∣ F ∣F) → j′ (x ⊓ y) ≡ j′ x ⊓ j′ y
  j′-n₀ = fst ih

  j′-n₁ : (x : ∣ F ∣F) → [ x ⊑[ pos F ] j′ x ]
  j′-n₁ = snd ih

  n₀ : (x y : ∣ F ∣F)
     → (ℜ-fam α $ (i ∷ is)) (x ⊓ y)
     ≡ (ℜ-fam α $ (i ∷ is)) x ⊓ (ℜ-fam α $ (i ∷ is)) y
  n₀ x y =
    j′ ((α $ i) (x ⊓ y))                            ≡⟨ cong j′ (fst (φ i) x y) ⟩
    j′ ((α $ i) x ⊓ (α $ i) y)                      ≡⟨ j′-n₀ _ _               ⟩
    (ℜ-fam α $ (i ∷ is)) x ⊓ (ℜ-fam α $ (i ∷ is)) y ∎

  n₁ : (x : ∣ F ∣F) → [ x ⊑[ pos F ] j x ]
  n₁ x = x ⊑⟨ snd (φ i) x ⟩ (α $ i) x ⊑⟨ j′-n₁ _ ⟩ j′ ((α $ i) x) ■
```

For convenience, we introduce the following notation: given a some family
`J` of nuclei, `J ^*` denotes its `ℜ-fam`.

```agda
_^* : Fam ℓ₂ (Nucleus F) → Fam ℓ₂ (∣ F ∣F → ∣ F ∣F)
J ^* = ℜ-fam ⁅ j ∣ (j , _) ε J ⁆
```

```agda
J*-++-lemma : (J : Fam ℓ₂ (Nucleus F))
            → (is js : index (J ^*))
            → (x : ∣ F ∣F)
            → (J ^* $ (is ++ js)) x ≡ ((J ^* $ js) ∘ (J ^* $ is)) x
J*-++-lemma J []       js x = refl
J*-++-lemma J (i ∷ is) js x = J*-++-lemma J is js (fst (J $ i) x)

J*-++ : (J : Fam ℓ₂ (Nucleus F))
      → (is js : index (J ^*)) → J ^* $ (is ++ js) ≡ (J ^* $ js) ∘ (J ^* $ is)
J*-++ J is js = funExt (J*-++-lemma J is js)
```

`J ^*` is always inhabited.

```agda
J*-inhabited : (J : Fam ℓ₂ (Nucleus F)) → ∥ index (J ^*) ∥
J*-inhabited J = ∣ [] ∣
```

Some nice notation.

```agda
_⦅_⦆_ : (J : Fam ℓ₂ (Nucleus F)) → index J → ∣ F ∣F → ∣ F ∣F
J ⦅ i ⦆ x = fst (J $ i) x

_*⦅_⦆_ : (J : Fam ℓ₂ (Nucleus F)) → index (J ^*) → ∣ F ∣F → ∣ F ∣F
J *⦅ is ⦆ x = ((J ^*) $ is) x
```

```agda
J*-up : (J : Fam ℓ₂ (Nucleus F))
      → (is js : index (J ^*))
      → Σ[ ks ∈ index (J ^*) ]
         [ ⟨ J ^* $ is , J ^* $ js ⟩⊑[ 𝔉 ] (J ^* $ ks) ]
J*-up J is js =
  (is ++ js) , J*is⊑J*is++js is js , J*js⊑J*is++js is js where

  Jᵢ-prenuclear : (i : index J) → isPrenuclear F ((fst ⟨$⟩ J) $ i)
  Jᵢ-prenuclear i = fst (snd (J $ i)) , fst (snd (snd (J $ i)))

  J*-prenuclear : (is : index (J ^*)) → isPrenuclear F ((J ^*) $ is)
  J*-prenuclear = ℜ-fam-prenucleus (fst ⟨$⟩ J) Jᵢ-prenuclear

  J*is⊑J*is++js : (is js : index (J ^*))
                → [ J *⦅ is ⦆_ ⊑[ 𝔉 ] J *⦅ is ++ js ⦆_ ]
  J*is⊑J*is++js []       js x = snd (J*-prenuclear js) x
  J*is⊑J*is++js (i ∷ is) js x =
    J *⦅ is ⦆ (J ⦅ i ⦆ x)       ⊑⟨ J*is⊑J*is++js is js (J ⦅ i ⦆ x) ⟩
    J *⦅ is ++ js ⦆ (J ⦅ i ⦆ x) ■

  J*js⊑J*is++js : (is js : index (J ^*))
                → [ J *⦅ js ⦆_ ⊑[ 𝔉 ] J *⦅ is ++ js ⦆_ ]
  J*js⊑J*is++js is js =
    subst (λ - → [ _ ⊑[ 𝔉 ] - ]) (sym (J*-++ J is js)) rem
    where
      rem : [ ((J ^*) $ js) ⊑[ 𝔉 ] (((J ^*) $ js) ∘ ((J ^*) $ is)) ]
      rem x = monop F (_ , J*-prenuclear js) x _ (snd (J*-prenuclear is) x)
```

```
J*-directed : (J : Fam ℓ₂ (Nucleus F)) → [ isDirected 𝔉 (J ^*) ]
J*-directed J = J*-inhabited J , λ is js → ∣ J*-up J is js ∣
```

Given a family `J` of Scott-continuous nuclei, everything in `J ^*` is
Scott-continuous.

```agda
J*-scott-continuous : (J : Fam 𝒲 (Nucleus F))
                    → ((i : index J) → isScottCont′ (J ⦅ i ⦆_))
                    → (is : index (J ^*)) → isScottCont′ (J *⦅ is ⦆_)
J*-scott-continuous J J-sc []       U dir = refl
J*-scott-continuous J J-sc (i ∷ is) U dir =
  J *⦅ i ∷ is ⦆ (⋁[ F ] U)                 ≡⟨ refl                             ⟩
  J *⦅ is ⦆ (J ⦅ i ⦆ (⋁[ F ] U))           ≡⟨ cong (J *⦅ is ⦆_) (J-sc _ U dir) ⟩
  J *⦅ is ⦆ (⋁[ F ] ⁅ J ⦅ i ⦆ x ∣ x ε U ⁆) ≡⟨ ⦅𝟐⦆                              ⟩
  ⋁[ F ] ⁅ J *⦅ i ∷ is ⦆ x ∣ x ε U ⁆       ∎
  where
    J-prenucleus : (i : index J) → Prenucleus F
    J-prenucleus i = fst (J $ i) , (fst (snd (J $ i))) , fst (snd (snd (J $ i)))

    lem : (j k : index U)
        → Σ[ l ∈ index U ] [ ⟨ (U $ j) , (U $ k) ⟩⊑[ pos F ] (U $ l) ]
        → ∥ Σ[ l ∈ index U ] [ ⟨ J ⦅ i ⦆ (U $ j) , J ⦅ i ⦆ (U $ k) ⟩⊑[ pos F ] (J ⦅ i ⦆ (U $ l)) ] ∥
    lem j k (l , p , q) =
      ∣ l , (monop F (J-prenucleus i) _ _ p   , monop F (J-prenucleus i) _ _ q) ∣

    dir′ : [ isDirected (pos F) ⁅ J ⦅ i ⦆ x ∣ x ε U ⁆ ]
    dir′ = (fst dir) , (λ j k → ∥∥-rec (∥∥-prop _) (lem j k) (snd dir j k))

    ⦅𝟐⦆ : _
    ⦅𝟐⦆ = J*-scott-continuous J J-sc is (⁅ J ⦅ i ⦆ x ∣ x ε U ⁆) dir′
```

### A lemma

```agda
joins-commute : (J : Fam 𝒲 (Nucleus F)) (U : Fam 𝒲 ∣ F ∣F)
              → ⋁ ⁅ ⋁ ⁅ α x ∣ α ε (J ^*) ⁆ ∣ x ε U ⁆
              ≡ ⋁ ⁅ ⋁ ⁅ α x ∣ x ε U ⁆ ∣ α ε (J ^*) ⁆
joins-commute J U =
  ⋁[ F ] ⁅ (⋁[ F ] ⁅ α x ∣ α ε (J ^*) ⁆) ∣ x ε U ⁆               ≡⟨ ⦅𝟏⦆ ⟩
  ⋁[ F ] ⁅ J *⦅ j ⦆ (U $ i) ∣ (i , j) ∶ index U × index (J ^*) ⁆ ≡⟨ ⦅𝟐⦆ ⟩
  ⋁[ F ] ⁅ J *⦅ j ⦆ (U $ i) ∣ (j , i) ∶ index (J ^*) × index U ⁆ ≡⟨ ⦅𝟑⦆ ⟩
  ⋁[ F ] ⁅ ⋁[ F ] ⁅ α x ∣ x ε U ⁆ ∣ α ε (J ^*) ⁆                 ∎
  where
  down : _
  down = ⋁[ F ]-least _ _ λ { z ((i , j) , eq) → ⋁[ F ]-upper _ z ((j , i) , eq) }

  up : _
  up = ⋁[ F ]-least _ _ λ { z ((i , j) , eq) → ⋁[ F ]-upper _ z ((j , i) , eq) }

  ⦅𝟏⦆ = sym (flatten F (index U) (λ _ → index (J ^*)) λ i j → J *⦅ j ⦆ (U $ i))
  ⦅𝟐⦆ = ⊑[ pos F ]-antisym _ _ down up
  ⦅𝟑⦆ = flatten F (index (J ^*)) (λ _ → index U) (λ j i → J *⦅ j ⦆ (U $ i)) 
```

```agda
𝕚 : (J : Fam 𝒲 (Nucleus F)) → ∣ F ∣F → ∣ F ∣F
𝕚 J x = ⋁ ⁅ α x ∣ α ε J ^* ⁆
```

### The definition of the join

```agda
⋁N_ : (J : Fam 𝒲 ScottContNucleus) → ScottContNucleus
⋁N_ J₀ = N , N-sc
  where
  J = fst ⟨$⟩ J₀

  J* : Fam 𝒲 (∣ F ∣F → ∣ F ∣F)
  J* = J ^*

  J-sc : (i : index J) → isScottCont′ (J ⦅ i ⦆_)
  J-sc i = snd (J₀ $ i)

  J*-prenuclear : (is : index J*) → isPrenuclear F (J* $ is)
  J*-prenuclear = ℜ-fam-prenucleus _ λ i →
                   fst (snd (J $ i)) , fst (snd (snd (J $ i)))

  J*-sc : (is : index J*) → (isScottCont′ (J *⦅ is ⦆_))
  J*-sc = J*-scott-continuous J J-sc

  β-n₀ : (is : index J*) (x y : ∣ F ∣F)
       → (J* $ is) (x ⊓[ F ] y) ≡ ((J* $ is) x) ⊓[ F ] ((J* $ is) y)
  β-n₀ = fst ∘ J*-prenuclear

  n₀ : (x y : ∣ F ∣F) → 𝕚 J (x ⊓[ F ] y) ≡ (𝕚 J x) ⊓[ F ] (𝕚 J y)
  n₀ x y =
    ⋁[ F ] ⁅ γ (x ⊓[ F ] y)     ∣ γ ε J* ⁆                     ≡⟨ ⦅𝟏⦆  ⟩
    ⋁[ F ] ⁅ (γ x) ⊓[ F ] (γ y) ∣ γ ε J* ⁆                     ≡⟨ ⦅𝟐⦆  ⟩
    ⋁[ F ] ⁅ (J* $ i) x ⊓[ F ] (J* $ j) y ∣ (i , j) ∶ _ × _ ⁆  ≡⟨ ⦅𝟑⦆  ⟩
    (⋁ ⁅ α x ∣ α ε J* ⁆) ⊓ (⋁ ⁅ β y ∣ β ε J* ⁆) ∎
      where
      nts₀ : [ ⋁[ F ] ⁅ γ x ⊓[ F ] γ y ∣ γ ε J* ⁆ ⊑[ pos F ] _ ]
      nts₀ = ⋁[ F ]-least _ _ λ { z (i , eq) → ⋁[ F ]-upper _ _ ((i , i) , eq) }

      rem : [ ∀[ z ε ⁅ (J* $ i) x ⊓[ F ] (J* $ j) y ∣ (i , j) ∶ _ × _ ⁆ ]
                (z ⊑[ pos F ] (⋁[ F ] ⁅ γ x ⊓[ F ] γ y ∣ γ ε J* ⁆)) ]
      rem z ((i , j) , eq) = subst (λ - → [ - ⊑[ pos F ] ⋁[ F ] _ ]) eq nts₂ where

        k = fst (J*-up J i j)

        nts₂ : _
        nts₂ =
          (J* $ i) x ⊓[ F ] (J* $ j) y       ⊑⟨ ⦅a⦆                         ⟩
          (J* $ k) x ⊓[ F ] (J* $ j) y       ⊑⟨ ⦅b⦆                         ⟩
          (J* $ k) x ⊓[ F ] (J* $ k) y       ⊑⟨ ⋁[ F ]-upper _ _ (k , refl) ⟩
          ⋁[ F ] ⁅ γ x ⊓[ F ] γ y ∣ γ ε J* ⁆ ■
          where
            ⦅a⦆ = cleft F (J *⦅ j ⦆ y) (fst (snd (J*-up J i j)) x)
            ⦅b⦆ = cright F (J *⦅ k ⦆ x) (snd (snd (J*-up J i j)) y)

      nts₁ : [ (⋁[ F ] ⁅ (J* $ i) x ⊓[ F ] (J* $ j) y ∣ (i , j) ∶ _ × _ ⁆)
               ⊑[ pos F ]
               ⋁[ F ] ⁅ γ x ⊓[ F ] γ y ∣ γ ε J* ⁆ ]
      nts₁ = ⋁[ F ]-least _ (⋁[ F ] fmap (λ γ → γ x ⊓[ F ] γ y) J*) rem

      ⦅𝟏⦆ = cong (λ - → ⋁[ F ] (index J* , -)) (funExt λ is → β-n₀ is x y)
      ⦅𝟐⦆ = ⊑[ pos F ]-antisym _ _ nts₀ nts₁
      ⦅𝟑⦆ = sym (sym-distr F ⁅ α x ∣ α ε J* ⁆ ⁅ β y ∣ β ε J* ⁆)

  n₁ : (x : ∣ F ∣F) → [ x ⊑[ pos F ] 𝕚 J x ]
  n₁ x = ⋁[ F ]-upper (⁅ h x ∣ h ε J* ⁆) x ([] , refl)

  n₂ : (x : ∣ F ∣F) → [ 𝕚 J (𝕚 J x) ⊑[ pos F ] 𝕚 J x ]
  n₂ x = ⋁[ F ] ⁅ α (⋁[ F ] ⁅ β x ∣ β ε J* ⁆) ∣ α ε J* ⁆          ⊑⟨ ⦅𝟎⦆  ⟩
         ⋁[ F ] ⁅ ⋁[ F ] ⁅ α (β x) ∣ β ε J* ⁆ ∣ α ε J* ⁆          ⊑⟨ ⦅𝟏⦆  ⟩
         ⋁[ F ] ⁅ ((J* $ j) ((J* $ i) x)) ∣ (j , i) ∶ (_ × _) ⁆   ⊑⟨ ⦅𝟑⦆  ⟩
         ⋁[ F ] ⁅ β x ∣ β ε J* ⁆                                  ■
    where
      rem : [ ∀[ z ε _ ] (z ⊑[ pos F ] ⋁[ F ] ⁅ β x ∣ β ε J* ⁆) ]
      rem z ((js , is) , eq) = ⋁[ F ]-upper _ _ ((is ++ js) , (_ ≡⟨ J*-++-lemma J is js x ⟩ (((J ^*) $ js) ∘ ((J ^*) $ is)) x ≡⟨ eq ⟩ z ∎))

      dir : [ isDirected (pos F) ⁅ β x ∣ β ε J* ⁆ ]
      dir = ∣ [] ∣ , upper-bounds where

        upper-bounds : _
        upper-bounds is js = ∣ ks , fst (snd (J*-up J is js)) x , snd (snd (J*-up J is js)) x ∣ where

          ks : index (J ^*)
          ks = fst (J*-up J is js)

      goal : (λ is → (J* $ is) (⋁[ F ] fmap (λ β → β x) J*)) ≡ (λ is → ⋁[ F ] fmap (λ β → (J* $ is) (β x)) J*)
      goal = funExt λ is → J*-scott-continuous J J-sc is ⁅ β x ∣ β ε J* ⁆ dir

      ⦅𝟎⦆ = ≡⇒⊑ (pos F) (cong (λ - → ⋁[ F ] (index J* , -)) goal)
      ⦅𝟏⦆ = ≡⇒⊑ (pos F) (sym (flatten F (index J*) (λ _ → index J*) λ j i → (J* $ j) ((J* $ i) x)))
      ⦅𝟑⦆ = ⋁[ F ]-least _ _ rem


  N : Nucleus F
  N = 𝕚 J , n₀ , n₁ , n₂

  N-sc : isScottCont′ (𝕚 J)
  N-sc U U-dir =
    𝕚 J (⋁[ F ] U)                                 ≡⟨ refl ⟩
    ⋁[ F ] ⁅ γ (⋁[ F ] U) ∣ γ ε J* ⁆               ≡⟨ cong (λ - → ⋁[ F ] (index J* , -)) (funExt λ is → J*-sc is U U-dir) ⟩
    ⋁[ F ] ⁅ (⋁[ F ] ⁅ γ x ∣ x ε U ⁆) ∣ γ ε J* ⁆   ≡⟨ sym (joins-commute J U)  ⟩ -- I need a lemma. Prove that joins commute in general.
    ⋁[ F ] ⁅ (⋁[ F ] ⁅ γ x ∣ γ ε J* ⁆) ∣ x ε U ⁆   ≡⟨ refl ⟩
    ⋁[ F ] ⁅ 𝕚 J x ∣ x ε U ⁆                       ∎

```

```agda
scott-cont-nuclei-poset-str : PosetStr (𝒰 ∨ 𝒱) ScottContNucleus
scott-cont-nuclei-poset-str =
  _⊑sc_ , ScottContNucleus-set , ⊑sc-refl , ⊑sc-trans , ⊑sc-antisym

  where
  _⊑sc_ : ScottContNucleus → ScottContNucleus → hProp (𝒰 ∨ 𝒱)
  (j , _) ⊑sc (k , _) = j ⊑[ 𝔑 ] k

  ⊑sc-refl : [ isReflexive _⊑sc_ ]
  ⊑sc-refl ((j , _) , _) = ⊑f-refl j

  ⊑sc-trans : [ isTransitive _⊑sc_ ]
  ⊑sc-trans (j , _) (k , _) (l , _) = ⊑[ 𝔑 ]-trans j k l

  ⊑sc-antisym : [ isAntisym ScottContNucleus-set _⊑sc_ ]
  ⊑sc-antisym (𝒿 , j-scott-cont) (𝓀 , k-scott-cont) p q =
    Σ≡Prop isScottCont-prop (⊑[ 𝔑 ]-antisym 𝒿 𝓀 p q)

𝔖 : Poset (𝒰 ∨ 𝒱 ∨ 𝒲 ⁺) (𝒰 ∨ 𝒱)
fst 𝔖 = ScottContNucleus
snd 𝔖 = scott-cont-nuclei-poset-str
```

```agda
⊓sc-meet : [ isGLB 𝔖 _⊓sc_ ]
⊓sc-meet = lower , greatest
  where
  greatest : (x y z : ∣ 𝔖 ∣ₚ)
           → [ z ⊑[ 𝔖 ] x ∧ z ⊑[ 𝔖 ] y ⇒ z ⊑[ 𝔖 ] (x ⊓sc y) ]
  greatest ((j , _) , _) ((k , _) , _) ((l , _) , _) (p , q) x =
    ⊓[ F ]-greatest (j x) (k x) (l x) (p x) (q x)

  lower : (x y : ∣ 𝔖 ∣ₚ) → [ rel 𝔖 (x ⊓sc y) x ∧ rel 𝔖 (x ⊓sc y) y ]
  lower ((j , _) , _) ((k , _) , _) =
    (λ x → ⊓[ F ]-lower₀ (j x) (k x)) , (λ x → ⊓[ F ]-lower₁ (j x) (k x))
```

```agda
⋁sc-join : [ isLUB 𝔖 ⋁N_ ]
⋁sc-join = upper , least where

  upper : (U : Fam 𝒲 ∣ 𝔖 ∣ₚ) → [ ∀[ x ε U ] (x ⊑[ 𝔖 ] (⋁N U)) ]
  upper U 𝒿@((j , _) , _) (i , eq) x = ⋁[ F ]-upper _ _ ((i ∷ []) , Uᵢ~j x) where

    Uᵢ~j : (x : ∣ F ∣F) → fst (fst (U $ i)) x ≡ j x
    Uᵢ~j = funExt⁻ (fst (PathΣ→ΣPathTransport _ _ (fst (PathΣ→ΣPathTransport _ _ eq))))

  least : (J : Fam 𝒲 ∣ 𝔖 ∣ₚ) (j : ∣ 𝔖 ∣ₚ)
        → [ ∀[ k ε J ] (k ⊑[ 𝔖 ] j) ⇒ (⋁N J) ⊑[ 𝔖 ] j ]
  least J 𝒿@((j , _ , n₁ , n₂) , _) p x = ⋁[ F ]-least _ (j x) λ { y (is , eq) → subst (λ - → [ - ⊑[ pos F ] j x ]) eq (lemma is x) } where

    Jᵢ-prenuclear : (i : index J) → isPrenuclear F ((fst ⟨$⟩ (fst ⟨$⟩ J)) $ i)
    Jᵢ-prenuclear i = fst (snd ((fst ⟨$⟩ J) $ i)) , fst (snd (snd ((fst ⟨$⟩ J) $ i)))

    J*-prenuclear : (is : index ((fst ⟨$⟩ J) ^*)) → isPrenuclear F (((fst ⟨$⟩ J) ^*) $ is)
    J*-prenuclear = ℜ-fam-prenucleus (fst ⟨$⟩ (fst ⟨$⟩ J)) Jᵢ-prenuclear

    lemma : (is : List (index J)) → (x : ∣ F ∣F) → [ (((fst ⟨$⟩ J) ^*) $ is) x ⊑[ pos F ] j x ]
    lemma []       x = n₁ x
    lemma (i ∷ is) x =
      (((fst ⟨$⟩ J) ^*) $ is) (fst (fst (J $ i)) x) ⊑⟨ monop F (_ , (J*-prenuclear is)) _ _ (p (J $ i ) (i , refl) x ) ⟩
      (((fst ⟨$⟩ J) ^*) $ is) (j x) ⊑⟨ lemma is (j x) ⟩ j (j x) ⊑⟨ n₂ x ⟩ j x ■
```

```agda
-- J*-⊓-lemma : (J : Fam ℓ₂ (Nucleus F))
--            → (j : Nucleus F)
--            → (x : ∣ F ∣F)
--            → (⋁[ F ] ⁅ (fst j x ⊓ k x) ∣ k ε (J ^*) ⁆)
--            ≡ (⋁[ F ] ⁅ l x ∣ l ε (((j ⊓N_) ⟨$⟩ J) ^*) ⁆)
-- J*-⊓-lemma J 𝒿@(j , n₀ , n₁ , _) y = {!!} where

--   open import Cofinality F

--   Jᵢ-prenuclear : (i : index J) → isPrenuclear F ((fst ⟨$⟩ J) $ i)
--   Jᵢ-prenuclear i = fst (snd (J $ i)) , fst (snd (snd (J $ i)))

--   J*-prenuclear : (is : index (J ^*)) → isPrenuclear F ((J ^*) $ is)
--   J*-prenuclear = ℜ-fam-prenucleus (fst ⟨$⟩ J) Jᵢ-prenuclear

--   lemma⋆ : (x : ∣ F ∣F) → (is : List (index J)) → ((_⊓N_ 𝒿 ⟨$⟩ J) *⦅ is ⦆ x) ≡ j x ⊓[ F ] (J *⦅ is ⦆ x)
--   lemma⋆ x []       = ⊑[ pos F ]-antisym _ _ (⊓[ F ]-greatest _ _ _ (n₁ x) (⊑[ pos F ]-refl x)) (⊓[ F ]-lower₁ _ _)
--   lemma⋆ x (i ∷ is) =
--     ((_⊓N_ 𝒿 ⟨$⟩ J) *⦅ i ∷ is ⦆ x)
--     ≡⟨ refl ⟩
--     (((_⊓N_ 𝒿 ⟨$⟩ J) *⦅ is ⦆ (j x ⊓[ F ] (J ⦅ i ⦆ x))))
--     ≡⟨ lemma⋆ (j x ⊓[ F ] (J ⦅ i ⦆ x)) is ⟩
--     j (j x ⊓[ F ] (J ⦅ i ⦆ x)) ⊓[ F ] (J *⦅ is ⦆ (j x ⊓[ F ] (J ⦅ i ⦆ x)))
--     ≡⟨ cong (λ - → - ⊓[ F ] (J *⦅ is ⦆ (j x ⊓[ F ] (J ⦅ i ⦆ x)))) (n₀ (j x) (J ⦅ i ⦆ x)) ⟩
--     (j (j x) ⊓[ F ] j (J ⦅ i ⦆ x)) ⊓[ F ] (J *⦅ is ⦆ (j x ⊓[ F ] (J ⦅ i ⦆ x)))
--     ≡⟨ {!!} ⟩
--     j x ⊓[ F ] (J *⦅ is ⦆ (J ⦅ i ⦆ x)) ∎

--   goal : (x : ∣ F ∣F) (is : List (index J)) → j x ⊓[ F ] (J *⦅ is ⦆ x) ≡ ((𝒿 ⊓N_) ⟨$⟩ J) *⦅ is ⦆ x
--   goal x is = sym (lemma⋆ x is)
```

```agda
dupl : (x y : ∣ F ∣F) → [ x ⊓ y ⊑[ pos F ] x ⊓ (x ⊓ y) ]
dupl x y = ⊓[ F ]-greatest _ _ _ (⊓[ F ]-lower₀ x y) (⊑[ pos F ]-refl (x ⊓ y))

nucl-lemma₁-a : ((j , _) (k , _) : Nucleus F) → [ j ⊑[ 𝔉 ] (j ∘ k) ]
nucl-lemma₁-a 𝒿@(j , _) (k , _ , n₁ , _) x = mono F 𝒿 x (k x) (n₁ x)

nucl-lemma₁-b : ((j , _) (k , _) : Nucleus F) → [ k ⊑[ 𝔉 ] (j ∘ k) ]
nucl-lemma₁-b (j , n₀ , n₁ , n₂) (k , _) x = n₁ (k x)

nucl-lemma₂ : ((j , _) (k , _) (j′ , _) (k′ , _) : Nucleus F)
            → [ j ⊑[ 𝔉 ] j′ ]
            → [ k ⊑[ 𝔉 ] k′ ]
            → [ (j ∘ k) ⊑[ 𝔉 ] (j′ ∘ k′) ]
nucl-lemma₂ 𝒿@(j , _) (k , _) (j′ , _) (k′ , _) p q x =
  j (k x) ⊑⟨ mono F 𝒿 (k x) (k′ x) (q x) ⟩ j (k′ x) ⊑⟨ p (k′ x) ⟩ j′ (k′ x) ■

nucl-lemma₃ : ((j , _) (k , _) (l , _) : Nucleus F)
            → [ j ⊑[ 𝔉 ] k ]
            → [ j ⊑[ 𝔉 ] (j ∙∧∙ k) ]
nucl-lemma₃ (j , _) (k , _) (l , _) p x =
  ⊓[ F ]-greatest _ _ _ (⊑[ pos F ]-refl (j x)) (p x)

lemma-γ : (j : Nucleus F) (K : Fam ℓ₂ (Nucleus F))
        → (is : List (index K)) (x : ∣ F ∣F)
        → [ ((j ⊓N_) ⟨$⟩ K) *⦅ is ⦆ x ⊑[ pos F ] K *⦅ is ⦆ x ]
lemma-γ j         K []       x = ⊑[ pos F ]-refl x
lemma-γ j@(𝒿 , _) K (i ∷ is) x =
  ((_⊓N_ j ⟨$⟩ K) *⦅ is ⦆ (𝒿 x ⊓[ F ] (K ⦅ i ⦆ x))) ⊑⟨ ih                ⟩
  K *⦅ is ⦆ ((𝒿 x) ⊓[ F ] (K ⦅ i ⦆ x))              ⊑⟨ ≡⇒⊑ (pos F) (fst (ℜ-fam-prenucleus (fst ⟨$⟩ K) (λ i → (fst (snd (K $ i))) , fst (snd (snd (K $ i)))) is) _ _) ⟩
  (K *⦅ is ⦆ (𝒿 x)) ⊓[ F ] (K *⦅ is ⦆ (K ⦅ i ⦆ x))  ⊑⟨ ⊓[ F ]-lower₁ _ _              ⟩
  K *⦅ i ∷ is ⦆ x                                   ■
  where
  ih : [ ((_⊓N_ j ⟨$⟩ K) *⦅ is ⦆ ((𝒿 x) ⊓[ F ] (K ⦅ i ⦆ x))) ⊑[ pos F ] (K *⦅ is ⦆ ((𝒿 x) ⊓[ F ] (K ⦅ i ⦆ x))) ]
  ih = lemma-γ j K is (𝒿 x ⊓[ F ] (K ⦅ i ⦆ x))

lemma-δ : (𝒿 : Nucleus F) (𝒦 : Fam ℓ₂ (Nucleus F))
        → (x : ∣ F ∣F) (is : List (index 𝒦))
        → [ ((𝒿 ⊓N_) ⟨$⟩ 𝒦) *⦅ is ⦆ x ⊑[ pos F ] fst 𝒿 x ]
lemma-δ 𝒿@(j , n₀ , n₁ , n₂) 𝒦 x []       = n₁ x
lemma-δ 𝒿@(j , n₀ , n₁ , n₂) 𝒦 x (i ∷ is) =
  (_⊓N_ 𝒿 ⟨$⟩ 𝒦) *⦅ i ∷ is ⦆ x                      ⊑⟨ ⊑[ pos F ]-refl _ ⟩
  ((_⊓N_ 𝒿 ⟨$⟩ 𝒦) *⦅ is ⦆ (j x ⊓[ F ] (𝒦 ⦅ i ⦆ x))) ⊑⟨ ≡⇒⊑ (pos F) (fst (ℜ-fam-prenucleus (fst ⟨$⟩ (_⊓N_ 𝒿 ⟨$⟩ 𝒦)) (λ i → (fst (snd ((_⊓N_ 𝒿 ⟨$⟩ 𝒦) $ i))) , fst (snd (snd ((_⊓N_ 𝒿 ⟨$⟩ 𝒦) $ i)))) is) _ _)  ⟩
  ((_⊓N_ 𝒿 ⟨$⟩ 𝒦) *⦅ is ⦆ (j x)) ⊓[ F ] ((_⊓N_ 𝒿 ⟨$⟩ 𝒦) *⦅ is ⦆ (𝒦 ⦅ i ⦆ x)) ⊑⟨ ⊓[ F ]-lower₀ _ _ ⟩
  ((_⊓N_ 𝒿 ⟨$⟩ 𝒦) *⦅ is ⦆ (j x))                    ⊑⟨ lemma-δ 𝒿 𝒦 (j x) is ⟩
  _                                                 ⊑⟨ n₂ x ⟩
  j x ■

sc-dist : [ isDist 𝔖 _⊓sc_ ⋁N_ ] -- The proof is written in the paper.
sc-dist j@(jn@(𝒿 , n₀ , n₁ , n₂) , _) J = Σ≡Prop isScottCont-prop (Σ≡Prop (isNuclear-prop F) nts) where

  open import Cofinality F

  K : Fam 𝒲 (Nucleus F)
  K = fst ⟨$⟩ J

  ∣J∣ : Fam 𝒲 (∣ F ∣F → ∣ F ∣F)
  ∣J∣ = fst ⟨$⟩ (fst ⟨$⟩ J)

  Jᵢ-prenuclear : (i : index J) → isPrenuclear F (∣J∣ $ i)
  Jᵢ-prenuclear i = fst (snd (K $ i)) , fst (snd (snd (K $ i)))

  J*-prenuclear : (is : index (K ^*)) → isPrenuclear F ((K ^*) $ is)
  J*-prenuclear = ℜ-fam-prenucleus ∣J∣ Jᵢ-prenuclear

  cofinal₀ : (x : ∣ F ∣F) → ⁅ 𝒿 x ⊓[ F ] α x ∣ α ε K ^* ⁆ cofinal-in ⁅ β x ∣ β ε ((jn ⊓N_) ⟨$⟩ K) ^* ⁆
  cofinal₀ x []       = [] , (⊓[ F ]-lower₁ _ _)
  cofinal₀ x (i ∷ is) = i ∷ js , rem
    where
    ih : _
    ih = cofinal₀ (𝒿 x ⊓[ F ] (K ⦅ i ⦆ x)) is

    js = fst ih

    φ : [ 𝒿 x ⊓[ F ] (K *⦅ is ⦆ (K ⦅ i ⦆ x)) ⊑[ pos F ] (𝒿 (𝒿 x)) ⊓[ F ] (𝒿 (K ⦅ i ⦆ x)) ]
    φ = 𝒿 x ⊓[ F ] (K *⦅ is ⦆ (K ⦅ i ⦆ x)) ⊑⟨ ⊓[ F ]-lower₀ _ _ ⟩ 𝒿 x ⊑⟨ ⊓[ F ]-greatest _ _ _ (n₁ (𝒿 x)) (mono F jn _ _ (snd (Jᵢ-prenuclear i) x)) ⟩ _ ■

    ψ : [ 𝒿 x ⊓[ F ] (K *⦅ is ⦆ (K ⦅ i ⦆ x)) ⊑[ pos F ] (K *⦅ is ⦆ (𝒿 x)) ⊓[ F ] (K *⦅ is ⦆ (K ⦅ i ⦆ x)) ]
    ψ = ⊓[ F ]-greatest _ _ _ (_ ⊑⟨ ⊓[ F ]-lower₀ _ _ ⟩ 𝒿 x ⊑⟨ snd (J*-prenuclear is) (𝒿 x) ⟩ _ ■) (⊓[ F ]-lower₁ _ _)

    rem : [ (𝒿 x ⊓[ F ] (K *⦅ is ⦆ (K ⦅ i ⦆ x))) ⊑[ pos F ] (fmap (λ β → β x) ((_⊓N_ jn ⟨$⟩ K) ^*) $ (i ∷ js)) ]
    rem = 𝒿 x ⊓[ F ] (K *⦅ is ⦆ (K ⦅ i ⦆ x))                                                           ⊑⟨ ⊓[ F ]-greatest _ _ _ φ ψ ⟩
         fmap (λ α → (𝒿 (𝒿 x) ⊓[ F ] 𝒿 (K ⦅ i ⦆ x)) ⊓[ F ] (α (𝒿 x) ⊓[ F ] α (K ⦅ i ⦆ x))) (K ^*) $ is ⊑⟨ ≡⇒⊑ (pos F) (cong (λ - → fmap (λ α → (𝒿 (𝒿 x) ⊓[ F ] 𝒿 (K ⦅ i ⦆ x)) ⊓[ F ] -) (K ^*) $ is) (sym (fst (J*-prenuclear is) _ _)))       ⟩
         fmap (λ α → (𝒿 (𝒿 x) ⊓[ F ] 𝒿 (K ⦅ i ⦆ x)) ⊓[ F ] (α (𝒿 x ⊓[ F ] (K ⦅ i ⦆ x)))) (K ^*) $ is   ⊑⟨ ≡⇒⊑ (pos F) (cong (λ - → fmap (λ α → - ⊓[ F ] (α (𝒿 x ⊓[ F ] (K ⦅ i ⦆ x)))) (K ^*) $ is) (sym (n₀ (𝒿 x) _)))       ⟩
         fmap (λ α → (𝒿 (𝒿 x ⊓[ F ] (K ⦅ i ⦆ x))) ⊓[ F ] (α (𝒿 x ⊓[ F ] (K ⦅ i ⦆ x)))) (K ^*) $ is     ⊑⟨ snd ih     ⟩
         fmap (λ β → β x) ((_⊓N_ jn ⟨$⟩ K) ^*) $ (i ∷ js)                                              ■

  cofinal₁ : (x : ∣ F ∣F) → ⁅ β x ∣ β ε ((jn ⊓N_) ⟨$⟩ K) ^* ⁆ cofinal-in ⁅ 𝒿 x ⊓[ F ] α x ∣ α ε K ^* ⁆
  cofinal₁ x is =
    is , ⊓[ F ]-greatest _ _ _ (lemma-δ jn K x is) (lemma-γ jn K is x)

  nts′ : (x : ∣ F ∣F) → 𝒿 x ⊓[ F ] (⋁[ F ] ⁅ α x ∣ α ε K ^* ⁆) ≡ ⋁[ F ] ⁅ β x ∣ β ε ((jn ⊓N_) ⟨$⟩ K) ^* ⁆
  nts′ x =
    𝒿 x ⊓ 𝕚 K x                            ≡⟨ dist F (𝒿 x) ⁅ 𝓀 x ∣ 𝓀 ε (K ^*) ⁆ ⟩
    ⋁[ F ] ⁅ 𝒿 x ⊓[ F ] α x ∣ α ε K ^* ⁆   ≡⟨ bicofinal→same-join _ _ (cofinal₀ x , cofinal₁ x) ⟩
    ⋁ ⁅ l x ∣ l ε ((jn ⊓N_) ⟨$⟩ K) ^* ⁆    ≡⟨ refl ⟩
    𝕚 ((jn ⊓N_) ⟨$⟩ K) x                   ∎

  nts : (𝒿 ∙∧∙ 𝕚 K) ≡ 𝕚 ((jn ⊓N_) ⟨$⟩ K)
  nts = funExt nts′
```

```agda
𝟏sc-top : [ ∀[ j ∶ ScottContNucleus ] j ⊑[ 𝔖 ] 𝟏sc ]
𝟏sc-top ((j , _) , _) x = ⊤[ F ]-top (j x)

ScottContNucleiFrame : Frame (𝒰 ∨ 𝒱 ∨ 𝒲 ⁺) (𝒰 ∨ 𝒱) 𝒲
fst ScottContNucleiFrame = ScottContNucleus
snd ScottContNucleiFrame =
  (snd 𝔖 , 𝟏sc , _⊓sc_ , ⋁N_) , 𝟏sc-top , ⊓sc-meet , ⋁sc-join , sc-dist
```

-- --}
-- --}
-- --}
```
