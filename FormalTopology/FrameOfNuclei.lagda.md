```agda
{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything hiding (_∧_)

open import Poset
open import Frame
open import Nucleus
open import Prenucleus
open import Cubical.Functions.Logic      hiding   (_⊓_)
open import Cubical.Foundations.Prelude  using    (refl; sym; cong; _≡⟨_⟩_; _∎)
open import Cubical.Data.Sigma           using    (Σ≡Prop; _×_)
open import Cubical.Foundations.Function using    (const; _∘_; idfun; uncurry)
open import Cubical.Data.List            hiding   ([_])
open import Cubical.Data.List.Properties
open import Basis                        renaming (_⊓_ to _∧_) hiding (J)

module FrameOfNuclei (F : Frame ℓ₀ ℓ₁ ℓ₂) where
```

**Based on work by Martín Escardó.**

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

```agda
isScottContinuous : (∣ F ∣F → ∣ F ∣F) → Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-suc ℓ₂))
isScottContinuous j =
  (U : Fam ℓ₂ ∣ F ∣F) →
    [ isDirected (pos F) U ] → j (⋁[ F ] U) ≡ ⋁[ F ] ⁅ j x ∣ x ε U ⁆
```

```agda
isScottContinuous-prop : (j : ∣ F ∣F → ∣ F ∣F)
                       → isProp (isScottContinuous j)
isScottContinuous-prop j =
  isPropΠ λ U → isPropΠ λ d → carrier-is-set (pos F) _ _
```

Poset of nuclei on `F`
======================

The set of endofunctions on a given frame forms a poset.

```agda
_⊑f_ : (∣ F ∣F → ∣ F ∣F) → (∣ F ∣F → ∣ F ∣F) → hProp (ℓ-max ℓ₀ ℓ₁)
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

endopos : Poset ℓ₀ (ℓ-max ℓ₀ ℓ₁)
endopos = (∣ F ∣F → ∣ F ∣F) , _⊑f_ , is-set , ⊑f-refl , ⊑f-trans , ⊑f-antisym
```

Therefore, the poset of nuclei on a frame forms a poset.

```agda
isScottCont : Nucleus F → Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-suc ℓ₂))
isScottCont = isScottContinuous ∘ fst

isScottCont-prop : (j : Nucleus F) → isProp (isScottCont j)
isScottCont-prop (j , _) = isScottContinuous-prop j

ScottContNucleus : Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-suc ℓ₂))
ScottContNucleus = Σ[ j ∈ Nucleus F ] isScottCont j

ScottContNucleus-set : isSet ScottContNucleus
ScottContNucleus-set =
  isSetΣ (Nucleus-set F) (isProp→isSet ∘ isScottContinuous-prop ∘ fst)
```

```agda
_⊑N_ : Order (ℓ-max ℓ₀ ℓ₁) (Nucleus F)
(j , _) ⊑N (k , _) = j ⊑f k

poset-of-nuclei-str : PosetStr (ℓ-max ℓ₀ ℓ₁) (Nucleus F)
poset-of-nuclei-str = _⊑N_ , Nucleus-set F , ⊑f-refl ∘ fst , ⊑-trans , ⊑-antisym
  where
    ⊑-trans : [ isTransitive _⊑N_ ]
    ⊑-trans (j , _) (k , _) (l , _) j⊑k k⊑l = ⊑f-trans j k l j⊑k k⊑l

    ⊑-antisym : [ isAntisym (Nucleus-set F)  _⊑N_ ]
    ⊑-antisym (j , _) (k , _) j⊑k k⊑j =
      Σ≡Prop (isNuclear-prop F) (⊑f-antisym j k j⊑k k⊑j)

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

```agda
𝟏-sc : isScottContinuous (const ⊤[ F ])
𝟏-sc U (∣i∣ , _) = ⊑[ pos F ]-antisym _ _ down up where

  down : [ ⊤[ F ] ⊑[ pos F ] (⋁[ F ] fmap (const ⊤[ F ]) U) ]
  down = ∥∥-rec (isProp[] (_ ⊑[ pos F ] _)) rem ∣i∣ where

    rem : _
    rem i = ⋁[ F ]-upper ((const ⊤[ F ]) ⟨$⟩ U) ⊤[ F ] (i , refl)

  up : [ (⋁[ F ] ((const ⊤[ F ]) ⟨$⟩ U)) ⊑[ pos F ] ⊤[ F ] ]
  up = ⊤[ F ]-top (⋁[ F ] ((const ⊤[ F ]) ⟨$⟩ U))

𝟏sc : ScottContNucleus
𝟏sc = 𝟏 , 𝟏-sc
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

```agda
_⊓sc_ : ScottContNucleus → ScottContNucleus → ScottContNucleus
_⊓sc_ (j , j-sc) (k , k-sc) = (j ⊓N k) , nts where

  nts : isScottCont (j ⊓N k)
  nts U U-dir =
    π₀ (j ⊓N k) (⋁[ F ] U) ≡⟨ refl ⟩
    (π₀ j (⋁[ F ] U) ⊓[ F ] π₀ k (⋁[ F ] U)) ≡⟨ cong (λ - → - ⊓[ F ] _) (j-sc U U-dir) ⟩
    ((⋁[ F ] ((π₀ j) ⟨$⟩ U)) ⊓[ F ] π₀ k (⋁[ F ] U)) ≡⟨ cong (λ - → glb-of F _ -) (k-sc U U-dir) ⟩
    (⋁[ F ] ⁅ π₀ j x ∣ x ε U ⁆) ⊓[ F ] (⋁[ F ] ⁅ π₀ k x ∣ x ε U ⁆) ≡⟨ sym-distr F _ _  ⟩
    (⋁[ F ] ⁅ ((π₀ j (U $ m)) ⊓[ F ] (π₀ k (U $ n))) ∣ (m , n) ∶ (index U × index U) ⁆) ≡⟨ ⊑[ pos F ]-antisym _ _ rem₀ rem₁ ⟩
    ⋁[ F ] ⁅ (π₀ j x ⊓[ F ] π₀ k x) ∣ x ε U ⁆ ∎
    where
      aux : [ (⋁[ F ] ⁅ π₀ j (U $ m) ⊓[ F ] π₀ k (U $ n) ∣ (m , n) ∶ (index U × index U) ⁆) ⊑[ pos F ] (⋁[ F ] ⁅ π₀ j (U $ o) ⊓[ F ] π₀ k (U $ o) ∣ o ∶ index U ⁆) ]
      aux = ⋁[ F ]-least _ _ nts-α where

        nts-α : _
        nts-α z ((m , n) , p) = ∥∥-rec (isProp[] (_ ⊑[ pos F ] _)) nts-β (snd U-dir m n) where

          nts-β : _
          nts-β (o , (a , b)) = subst (λ - → [ - ⊑[ pos F ] _ ]) p foo where

            foo : _
            foo = (π₀ j (U $ m)) ⊓[ F ] (π₀ k (U $ n)) ⊑⟨ cleft F (π₀ k (U $ n)) (mono F j (U $ m) (U $ o) a ) ⟩
                  (π₀ j (U $ o)) ⊓[ F ] (π₀ k (U $ n)) ⊑⟨ cright F (π₀ j (U $ o)) (mono F k (U $ n) (U $ o) b) ⟩
                  (π₀ j (U $ o)) ⊓[ F ] (π₀ k (U $ o)) ⊑⟨ ⋁[ F ]-upper _ _ (o , refl) ⟩
                  (⋁[ F ] ⁅ π₀ j (U $ o) ⊓[ F ] π₀ k (U $ o) ∣ o ∶ index U ⁆) ■

      rem₀ : [ (⋁[ F ] ⁅ π₀ j (U $ m) ⊓[ F ] π₀ k (U $ n) ∣ (m , n) ∶ (index U × index U) ⁆) ⊑[ pos F ] ⋁[ F ] ⁅ (π₀ j x ⊓[ F ] π₀ k x) ∣ x ε U ⁆ ]
      rem₀ = aux

      rem₁ : [ ⋁[ F ] ⁅ (π₀ j x ⊓[ F ] π₀ k x) ∣ x ε U ⁆ ⊑[ pos F ] (⋁[ F ] ⁅ ((π₀ j (U $ m)) ⊓[ F ] (π₀ k (U $ n))) ∣ (m , n) ∶ (index U × index U) ⁆) ]
      rem₁ = ⋁[ F ]-least _ (⋁[ F ] _) λ { z (i , p) → ⋁[ F ]-upper _ _ ((i , i) , p) }
```

Arbitrary join of nuclei
------------------------

This is the non-trivial part of this development.

Given a family `α` of endofunctions on a type, we denote by `compFam α` the
family obtained by taking compositions of functions in `α`.

```agda
compFam : {A : Type ℓ₀} (α : Fam ℓ₂ (A → A)) → Fam ℓ₂ (A → A)
compFam {A = A} α = List (index α) , f where

  f : List (index α) → A → A
  f []       = idfun A
  f (i ∷ is) = f is ∘ (α $ i)
```

We will use this function to compute the join of a family of nuclei.

Notice that the identity function is always a (pre)nucleus.

```agda
id-is-nuclear : (F : Frame ℓ₀ ℓ₁ ℓ₂) → isPrenuclear F (idfun ∣ F ∣F)
id-is-nuclear F = (λ _ _ → refl) , ⊑[ pos F ]-refl
```

Compositions of prenuclei are prenuclei meaning given a family of nuclei, its
`compFam` is a family of prenuclei

```agda
compFam-prenucleus : (α : Fam ℓ₂ (∣ F ∣F → ∣ F ∣F))
                   → ((i : index α) → isPrenuclear F (α $ i))
                   → (is : List (index α)) → isPrenuclear F ((compFam α) $ is)
compFam-prenucleus α φ []       = id-is-nuclear F
compFam-prenucleus α φ (i ∷ is) = n₀ , n₁ where

  j = compFam α $ (i ∷ is)

  j′ : ∣ F ∣F → ∣ F ∣F
  j′ = compFam α $ is

  ih : isPrenuclear F j′
  ih = compFam-prenucleus α φ is

  j′-n₀ : (x y : ∣ F ∣F) → j′ (x ⊓[ F ] y) ≡ j′ x ⊓[ F ] j′ y
  j′-n₀ = fst ih

  j′-n₁ : (x : ∣ F ∣F) → [ x ⊑[ pos F ] j′ x ]
  j′-n₁ = snd ih

  n₀ : (x y : ∣ F ∣F)
     → (compFam α $ (i ∷ is)) (x ⊓[ F ] y)
     ≡ (compFam α $ (i ∷ is)) x ⊓[ F ] (compFam α $ (i ∷ is)) y
  n₀ x y =
    j′ ((α $ i) (x ⊓[ F ] y))       ≡⟨ cong j′ (fst (φ i) x y)   ⟩
    j′ ((α $ i) x ⊓[ F ] (α $ i) y) ≡⟨ j′-n₀ _ _                 ⟩
    (compFam α $ (i ∷ is)) x ⊓[ F ] (compFam α $ (i ∷ is)) y ∎

  n₁ : (x : ∣ F ∣F) → [ x ⊑[ pos F ] j x ]
  n₁ x = x ⊑⟨ snd (φ i) x ⟩ (α $ i) x ⊑⟨ j′-n₁ _ ⟩ j′ ((α $ i) x) ■
```

For convenience, we introduce the following notation: given a some family
`J` of nuclei, `J ^*` denotes its `compFam`.

```agda
_^* : Fam ℓ₂ (Nucleus F) → Fam ℓ₂ (∣ F ∣F → ∣ F ∣F)
J ^* = compFam ⁅ j ∣ (j , _) ε J ⁆
```

```agda
J*-++-ext : (J : Fam ℓ₂ (Nucleus F))
          → (is js : index (J ^*))
          → (x : ∣ F ∣F)
          → (J ^* $ (is ++ js)) x ≡ ((J ^* $ js) ∘ (J ^* $ is)) x
J*-++-ext J []       js x = refl
J*-++-ext J (i ∷ is) js x = J*-++-ext J is js (fst (J $ i) x)

J*-++ : (J : Fam ℓ₂ (Nucleus F))
      → (is js : index (J ^*)) → J ^* $ (is ++ js) ≡ (J ^* $ js) ∘ (J ^* $ is)
J*-++ J is js = funExt (J*-++-ext J is js)
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
J*-upwards-directed : (J : Fam ℓ₂ (Nucleus F))
                  → (is js : index (J ^*))
                  → Σ[ ks ∈ index (J ^*) ]
                     [ ⟨ J ^* $ is , J ^* $ js ⟩⊑[ endopos ] (J ^* $ ks) ]
J*-upwards-directed J is js =
  (is ++ js) , J*is⊑J*is++js is js , J*js⊑J*is++js is js where

  Jᵢ-prenuclear : (i : index J) → isPrenuclear F ((fst ⟨$⟩ J) $ i)
  Jᵢ-prenuclear i = fst (snd (J $ i)) , fst (snd (snd (J $ i)))

  J*-prenuclear : (is : index (J ^*)) → isPrenuclear F ((J ^*) $ is)
  J*-prenuclear = compFam-prenucleus (fst ⟨$⟩ J) Jᵢ-prenuclear

  J*is⊑J*is++js : (is js : index (J ^*))
                → [ J *⦅ is ⦆_ ⊑[ endopos ] J *⦅ is ++ js ⦆_ ]
  J*is⊑J*is++js []       js x = π₁ (J*-prenuclear js) x
  J*is⊑J*is++js (i ∷ is) js x =
    J *⦅ is ⦆ (J ⦅ i ⦆ x)       ⊑⟨ J*is⊑J*is++js is js (J ⦅ i ⦆ x) ⟩
    J *⦅ is ++ js ⦆ (J ⦅ i ⦆ x) ■

  J*js⊑J*is++js : (is js : index (J ^*))
                → [ J *⦅ js ⦆_ ⊑[ endopos ] J *⦅ is ++ js ⦆_ ]
  J*js⊑J*is++js is js =
    subst (λ - → [ _ ⊑[ endopos ] - ]) (sym (J*-++ J is js)) rem
    where
      rem : [ ((J ^*) $ js) ⊑[ endopos ] (((J ^*) $ js) ∘ ((J ^*) $ is)) ]
      rem x = monop F (_ , J*-prenuclear js) x _ (π₁ (J*-prenuclear is) x)
```

```
J*-directed : (J : Fam ℓ₂ (Nucleus F)) → [ isDirected endopos (J ^*) ]
J*-directed J = J*-inhabited J , λ is js → ∣ J*-upwards-directed J is js ∣
```

Given a family `J` of Scott-continuous nuclei, everything in `J ^*` is
Scott-continuous.

```agda
J*-scott-continuous : (J : Fam ℓ₂ (Nucleus F))
                    → ((i : index J) → isScottContinuous (J ⦅ i ⦆_))
                    → (is : index (J ^*)) → (isScottContinuous (J *⦅ is ⦆_))
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

The join
========

```agda
joins-commute : (J : Fam ℓ₂ (Nucleus F)) (U : Fam ℓ₂ ∣ F ∣F)
              → ⋁[ F ] ⁅ (⋁[ F ] ⁅ α x ∣ α ε (J ^*) ⁆) ∣ x ε U ⁆
              ≡ ⋁[ F ] ⁅ ⋁[ F ] ⁅ α x ∣ x ε U ⁆ ∣ α ε (J ^*) ⁆
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
⋁N_ : (J : Fam ℓ₂ ScottContNucleus) → ScottContNucleus
⋁N_ J₀ = N , N-sc where

  J = fst ⟨$⟩ J₀

  J* : Fam ℓ₂ (∣ F ∣F → ∣ F ∣F)
  J* = J ^*

  J-sc : (is : index J) → isScottContinuous (J ⦅ is ⦆_)
  J-sc is = snd (J₀ $ is)

  J*-prenuclear : (is : index J*) → isPrenuclear F (J* $ is)
  J*-prenuclear = compFam-prenucleus _ λ i →
                   fst (snd (J $ i)) , fst (snd (snd (J $ i)))

  J*-sc : (is : index J*) → (isScottContinuous (J *⦅ is ⦆_))
  J*-sc = J*-scott-continuous J J-sc

  β-n₀ : (is : index J*) (x y : ∣ F ∣F)
       → (J* $ is) (x ⊓[ F ] y) ≡ ((J* $ is) x) ⊓[ F ] ((J* $ is) y)
  β-n₀ = fst ∘ J*-prenuclear

  𝕚 : ∣ F ∣F → ∣ F ∣F
  𝕚 x = ⋁[ F ] ⁅ α x ∣ α ε J* ⁆

  n₀ : (x y : ∣ F ∣F) → 𝕚 (x ⊓[ F ] y) ≡ (𝕚 x) ⊓[ F ] (𝕚 y)
  n₀ x y =
    𝕚 (x ⊓[ F ] y)                                             ≡⟨ refl ⟩
    ⋁[ F ] ⁅ γ (x ⊓[ F ] y)     ∣ γ ε J* ⁆                     ≡⟨ ⦅𝟏⦆  ⟩
    ⋁[ F ] ⁅ (γ x) ⊓[ F ] (γ y) ∣ γ ε J* ⁆                     ≡⟨ ⦅𝟐⦆  ⟩
    ⋁[ F ] ⁅ (J* $ i) x ⊓[ F ] (J* $ j) y ∣ (i , j) ∶ _ × _ ⁆  ≡⟨ ⦅𝟑⦆  ⟩
    (⋁[ F ] ⁅ α x ∣ α ε J* ⁆) ⊓[ F ] (⋁[ F ] ⁅ β y ∣ β ε J* ⁆) ≡⟨ refl ⟩
    𝕚 x ⊓[ F ] 𝕚 y                                             ∎ where

      nts₀ : [ ⋁[ F ] ⁅ γ x ⊓[ F ] γ y ∣ γ ε J* ⁆ ⊑[ pos F ] _ ]
      nts₀ = ⋁[ F ]-least _ _ λ { z (i , eq) → ⋁[ F ]-upper _ _ ((i , i) , eq) }

      rem : [ ∀[ z ε ⁅ (J* $ i) x ⊓[ F ] (J* $ j) y ∣ (i , j) ∶ _ × _ ⁆ ]
                (z ⊑[ pos F ] (⋁[ F ] ⁅ γ x ⊓[ F ] γ y ∣ γ ε J* ⁆)) ]
      rem z ((i , j) , eq) = subst (λ - → [ - ⊑[ pos F ] ⋁[ F ] _ ]) eq nts₂ where

        k = fst (J*-upwards-directed J i j)

        nts₂ : _
        nts₂ =
          (J* $ i) x ⊓[ F ] (J* $ j) y       ⊑⟨ ⦅a⦆                         ⟩
          (J* $ k) x ⊓[ F ] (J* $ j) y       ⊑⟨ ⦅b⦆                         ⟩
          (J* $ k) x ⊓[ F ] (J* $ k) y       ⊑⟨ ⋁[ F ]-upper _ _ (k , refl) ⟩
          ⋁[ F ] ⁅ γ x ⊓[ F ] γ y ∣ γ ε J* ⁆ ■
          where
            ⦅a⦆ = cleft F (J *⦅ j ⦆ y) (fst (snd (J*-upwards-directed J i j)) x)
            ⦅b⦆ = cright F (J *⦅ k ⦆ x) (snd (snd (J*-upwards-directed J i j)) y)

      nts₁ : [ (⋁[ F ] ⁅ (J* $ i) x ⊓[ F ] (J* $ j) y ∣ (i , j) ∶ _ × _ ⁆)
               ⊑[ pos F ]
               ⋁[ F ] ⁅ γ x ⊓[ F ] γ y ∣ γ ε J* ⁆ ]
      nts₁ = ⋁[ F ]-least _ (⋁[ F ] fmap (λ γ → γ x ⊓[ F ] γ y) J*) rem

      ⦅𝟏⦆ = cong (λ - → ⋁[ F ] (index J* , -)) (funExt λ is → β-n₀ is x y)
      ⦅𝟐⦆ = ⊑[ pos F ]-antisym _ _ nts₀ nts₁
      ⦅𝟑⦆ = sym (sym-distr F ⁅ α x ∣ α ε J* ⁆ ⁅ β y ∣ β ε J* ⁆)

  n₁ : (x : ∣ F ∣F) → [ x ⊑[ pos F ] 𝕚 x ]
  n₁ x = ⋁[ F ]-upper (⁅ h x ∣ h ε J* ⁆) x ([] , refl)

  n₂ : (x : ∣ F ∣F) → [ 𝕚 (𝕚 x) ⊑[ pos F ] 𝕚 x ]
  n₂ x = ⋁[ F ] ⁅ α (⋁[ F ] ⁅ β x ∣ β ε J* ⁆) ∣ α ε J* ⁆          ⊑⟨ ⦅𝟎⦆  ⟩
         ⋁[ F ] ⁅ ⋁[ F ] ⁅ α (β x) ∣ β ε J* ⁆ ∣ α ε J* ⁆          ⊑⟨ ⦅𝟏⦆  ⟩
         ⋁[ F ] ⁅ ((J* $ j) ((J* $ i) x)) ∣ (j , i) ∶ (_ × _) ⁆   ⊑⟨ ⦅𝟑⦆  ⟩
         ⋁[ F ] ⁅ β x ∣ β ε J* ⁆                                  ■
    where
      rem : [ ∀[ z ε _ ] (z ⊑[ pos F ] ⋁[ F ] ⁅ β x ∣ β ε J* ⁆) ]
      rem z ((js , is) , eq) = ⋁[ F ]-upper _ _ ((is ++ js) , (_ ≡⟨ J*-++-ext J is js x ⟩ (((J ^*) $ js) ∘ ((J ^*) $ is)) x ≡⟨ eq ⟩ z ∎))

      dir : [ isDirected (pos F) ⁅ β x ∣ β ε J* ⁆ ]
      dir = ∣ [] ∣ , upper-bounds where

        upper-bounds : _
        upper-bounds is js = ∣ ks , fst (snd (J*-upwards-directed J is js)) x , snd (snd (J*-upwards-directed J is js)) x ∣ where

          ks : index (J ^*)
          ks = fst (J*-upwards-directed J is js)

      goal : (λ is → (J* $ is) (⋁[ F ] fmap (λ β → β x) J*)) ≡ (λ is → ⋁[ F ] fmap (λ β → (J* $ is) (β x)) J*)
      goal = funExt λ is → J*-scott-continuous J J-sc is ⁅ β x ∣ β ε J* ⁆ dir

      ⦅𝟎⦆ = ≡⇒⊑ (pos F) (cong (λ - → ⋁[ F ] (index J* , -)) goal)
      ⦅𝟏⦆ = ≡⇒⊑ (pos F) (sym (flatten F (index J*) (λ _ → index J*) λ j i → (J* $ j) ((J* $ i) x)))
      ⦅𝟑⦆ = ⋁[ F ]-least _ _ rem


  N : Nucleus F
  N = 𝕚 , n₀ , n₁ , n₂

  N-sc : isScottContinuous 𝕚
  N-sc U U-dir =
    𝕚 (⋁[ F ] U)                                   ≡⟨ refl ⟩
    ⋁[ F ] ⁅ γ (⋁[ F ] U) ∣ γ ε J* ⁆               ≡⟨ cong (λ - → ⋁[ F ] (index J* , -)) (funExt λ is → J*-sc is U U-dir) ⟩
    ⋁[ F ] ⁅ (⋁[ F ] ⁅ γ x ∣ x ε U ⁆) ∣ γ ε J* ⁆   ≡⟨ sym (joins-commute J U)  ⟩ -- I need a lemma. Prove that joins commute in general.
    ⋁[ F ] ⁅ (⋁[ F ] ⁅ γ x ∣ γ ε J* ⁆) ∣ x ε U ⁆   ≡⟨ refl ⟩
    ⋁[ F ] ⁅ 𝕚 x ∣ x ε U ⁆                         ∎
```

```agda
scott-cont-nuclei-poset-str : PosetStr (ℓ-max ℓ₀ ℓ₁) ScottContNucleus
scott-cont-nuclei-poset-str =
  _⊑sc_ , ScottContNucleus-set , ⊑sc-refl , ⊑sc-trans , ⊑sc-antisym where

  _⊑sc_ : ScottContNucleus → ScottContNucleus → hProp (ℓ-max ℓ₀ ℓ₁)
  (j , _) ⊑sc (k , _) = j ⊑N k

  ⊑sc-refl : [ isReflexive _⊑sc_ ]
  ⊑sc-refl ((j , _) , _) = ⊑f-refl j

  ⊑sc-trans : [ isTransitive _⊑sc_ ]
  ⊑sc-trans (j , _) (k , _) (l , _) = ⊑[ poset-of-nuclei ]-trans j k l

  ⊑sc-antisym : [ isAntisym ScottContNucleus-set _⊑sc_ ]
  ⊑sc-antisym (j , j-scott-cont) (k , k-scott-cont) j⊑k k⊑j =
    Σ≡Prop
      (isScottContinuous-prop ∘ fst)
      (⊑[ poset-of-nuclei ]-antisym j k j⊑k k⊑j)


scn-pos : Poset (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-suc ℓ₂)) (ℓ-max ℓ₀ ℓ₁)
scn-pos = ScottContNucleus , scott-cont-nuclei-poset-str
```

```agda
⊓sc-meet : [ isGLB scn-pos _⊓sc_ ]
⊓sc-meet = lower , greatest where

  greatest : (x y z : ∣ scn-pos ∣ₚ)
           → [ z ⊑[ scn-pos ] x ∧ z ⊑[ scn-pos ] y ⇒ z ⊑[ scn-pos ] (x ⊓sc y) ]
  greatest ((j , _) , _) ((k , _) , _) ((l , _) , _) (p , q) x =
    ⊓[ F ]-greatest (j x) (k x) (l x) (p x) (q x)

  lower : (x y : ∣ scn-pos ∣ₚ) → [ rel scn-pos (x ⊓sc y) x ∧ rel scn-pos (x ⊓sc y) y ]
  lower ((j , _) , _) ((k , _) , _) =
    (λ x → ⊓[ F ]-lower₀ (j x) (k x)) , (λ x → ⊓[ F ]-lower₁ (j x) (k x))
```

```agda
⋁sc-join : [ isLUB scn-pos ⋁N_ ]
⋁sc-join = upper , least where

  upper : (U : Fam ℓ₂ ∣ scn-pos ∣ₚ) → [ ∀[ x ε U ] (x ⊑[ scn-pos ] (⋁N U)) ]
  upper U 𝒿@((j , _) , _) (i , eq) x = ⋁[ F ]-upper _ _ ((i ∷ []) , Uᵢ~j x) where

    Uᵢ~j : (x : ∣ F ∣F) → fst (fst (U $ i)) x ≡ j x
    Uᵢ~j = funExt⁻ (fst (PathΣ→ΣPathTransport _ _ (fst (PathΣ→ΣPathTransport _ _ eq))))

  least : (J : Fam ℓ₂ ∣ scn-pos ∣ₚ) (j : ∣ scn-pos ∣ₚ)
        → [ ∀[ k ε J ] (k ⊑[ scn-pos ] j) ⇒ (⋁N J) ⊑[ scn-pos ] j ]
  least J 𝒿@((j , _ , n₁ , n₂) , _) p x = ⋁[ F ]-least _ (j x) λ { y (is , eq) → subst (λ - → [ - ⊑[ pos F ] j x ]) eq (lemma is x) } where

    Jᵢ-prenuclear : (i : index J) → isPrenuclear F ((fst ⟨$⟩ (fst ⟨$⟩ J)) $ i)
    Jᵢ-prenuclear i = fst (snd ((fst ⟨$⟩ J) $ i)) , fst (snd (snd ((fst ⟨$⟩ J) $ i)))

    J*-prenuclear : (is : index ((fst ⟨$⟩ J) ^*)) → isPrenuclear F (((fst ⟨$⟩ J) ^*) $ is)
    J*-prenuclear = compFam-prenucleus (fst ⟨$⟩ (fst ⟨$⟩ J)) Jᵢ-prenuclear

    lemma : (is : List (index J)) → (x : ∣ F ∣F) → [ (((fst ⟨$⟩ J) ^*) $ is) x ⊑[ pos F ] j x ]
    lemma []       x = n₁ x
    lemma (i ∷ is) x =
      (((fst ⟨$⟩ J) ^*) $ is) (fst (fst (J $ i)) x) ⊑⟨ monop F (_ , (J*-prenuclear is)) _ _ (p (J $ i ) (i , refl) x ) ⟩
      (((fst ⟨$⟩ J) ^*) $ is) (j x) ⊑⟨ lemma is (j x) ⟩ j (j x) ⊑⟨ n₂ x ⟩ j x ■
```

```agda
J*-⊓-lemma : (J : Fam ℓ₂ (Nucleus F))
           → (j : Nucleus F)
           → (x : ∣ F ∣F)
           → ⁅ (fst j x ⊓[ F ] k x) ∣ k ε (J ^*) ⁆ ≡ ⁅ k x ∣ k ε (((j ⊓N_) ⟨$⟩ J) ^*) ⁆
J*-⊓-lemma J 𝒿@(j , n₀ , n₁ , _) y = cong (λ - → (List (index J) , -)) (funExt (goal y)) where

  Jᵢ-prenuclear : (i : index J) → isPrenuclear F ((fst ⟨$⟩ J) $ i)
  Jᵢ-prenuclear i = fst (snd (J $ i)) , fst (snd (snd (J $ i)))

  J*-prenuclear : (is : index (J ^*)) → isPrenuclear F ((J ^*) $ is)
  J*-prenuclear = compFam-prenucleus (fst ⟨$⟩ J) Jᵢ-prenuclear


  lemma⋆ : (x : ∣ F ∣F) → (is : List (index J)) → ((_⊓N_ 𝒿 ⟨$⟩ J) *⦅ is ⦆ x) ≡ j x ⊓[ F ] (J *⦅ is ⦆ x)
  lemma⋆ x []       = ⊑[ pos F ]-antisym _ _ (⊓[ F ]-greatest _ _ _ (n₁ x) (⊑[ pos F ]-refl x)) (⊓[ F ]-lower₁ _ _)
  lemma⋆ x (i ∷ is) =
    ((_⊓N_ 𝒿 ⟨$⟩ J) *⦅ i ∷ is ⦆ x)
    ≡⟨ refl ⟩
    (((_⊓N_ 𝒿 ⟨$⟩ J) *⦅ is ⦆ (j x ⊓[ F ] (J ⦅ i ⦆ x))))
    ≡⟨ lemma⋆ (j x ⊓[ F ] (J ⦅ i ⦆ x)) is ⟩
    j (j x ⊓[ F ] (J ⦅ i ⦆ x)) ⊓[ F ] (J *⦅ is ⦆ (j x ⊓[ F ] (J ⦅ i ⦆ x)))
    ≡⟨ cong (λ - → - ⊓[ F ] (J *⦅ is ⦆ (j x ⊓[ F ] (J ⦅ i ⦆ x)))) (n₀ (j x) (J ⦅ i ⦆ x)) ⟩
    (j (j x) ⊓[ F ] j (J ⦅ i ⦆ x)) ⊓[ F ] (J *⦅ is ⦆ (j x ⊓[ F ] (J ⦅ i ⦆ x)))
    ≡⟨ {!!} ⟩
    j x ⊓[ F ] (J *⦅ is ⦆ (J ⦅ i ⦆ x)) ∎

  goal : (x : ∣ F ∣F) (is : List (index J)) → j x ⊓[ F ] (J *⦅ is ⦆ x) ≡ ((𝒿 ⊓N_) ⟨$⟩ J) *⦅ is ⦆ x
  goal x is = sym (lemma⋆ x is)
```

```agda
sc-dist : [ isDist scn-pos _⊓sc_ ⋁N_ ] -- The proof is written in the paper.
sc-dist j@((𝒿 , _) , _) J = Σ≡Prop isScottCont-prop (Σ≡Prop (isNuclear-prop F) nts) where

  J₀ = fst ⟨$⟩ J

  nts : (j ⊓sc (⋁N J)) .π₀ .π₀ ≡ (⋁N ⁅ j ⊓sc k ∣ k ε J ⁆) .π₀ .π₀
  nts = funExt rem
    where
      rem : _
      rem x = _ ≡⟨ dist F (𝒿 x) _ ⟩
              ⋁[ F ] ⁅ 𝒿 x ⊓[ F ] (J₀ *⦅ is ⦆ x) ∣ is ∶ List (index J) ⁆ ≡⟨ cong (λ - → ⋁[ F ] -) (J*-⊓-lemma J₀ (fst j) x) ⟩
              (⋁[ F ] ⁅ l x ∣ l ε (⁅ fst (j ⊓sc k) ∣ k ε J ⁆ ^*) ⁆)   ≡⟨ refl ⟩
              (⋁[ F ] (List (index J) , λ is → ((⁅ (π₀ j) ⊓N (π₀ k) ∣ k ε J ⁆ ^*) $ is) x))   ≡⟨ refl ⟩
              π₀ (π₀ (⋁N fmap (λ k → j ⊓sc k) J)) x ∎
```

```agda
ScottContNucleiFrame : Frame (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-suc ℓ₂)) (ℓ-max ℓ₀ ℓ₁) ℓ₂
ScottContNucleiFrame =
  ScottContNucleus , (snd scn-pos , 𝟏sc , _⊓sc_ , ⋁N_) , 𝟏sc-top , ⊓sc-meet , ⋁sc-join , sc-dist where

  𝟏sc-top : [ ∀[ j ∶ ScottContNucleus ] j ⊑[ scn-pos ] 𝟏sc ]
  𝟏sc-top ((j , _) , _) x = ⊤[ F ]-top (j x)
```

Distributivity
--------------

```agda
{--
distr-N : [ isDist poset-of-nuclei _⊓N_ ⋁N_ ]
distr-N = {!!}

frame-of-nuclei-raw-str : RawFrameStr (ℓ-max ℓ₀ ℓ₁) ℓ₂ (Nucleus F)
frame-of-nuclei-raw-str = poset-of-nuclei-str , 𝟏 , _⊓N_ , ⋁N_

frame-of-nuclei-str : FrameStr (ℓ-max ℓ₀ ℓ₁) ℓ₂ (Nucleus F)
frame-of-nuclei-str = frame-of-nuclei-raw-str , axioms
  where
    axioms : [ FrameAx (poset-of-nuclei-str , 𝟏 , _⊓N_ , ⋁N_) ]
    axioms = 𝟏-top , (⊓N-meet , {!!} , {!!})

The final definition
--------------------

frame-of-nuclei : Frame (ℓ-max ℓ₀ ℓ₁) (ℓ-max ℓ₀ ℓ₁) ℓ₂
frame-of-nuclei =
  Nucleus F , frame-of-nuclei-raw-str , 𝟏-top , ⊓N-meet , {!!} , distr-N

-- --}
-- --}
-- --}
```
