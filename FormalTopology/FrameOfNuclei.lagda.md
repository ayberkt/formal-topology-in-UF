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
_⊑f_ : (∣ F ∣F → ∣ F ∣F) → (∣ F ∣F → ∣ F ∣F) → hProp (ℓ-max ℓ₀ ℓ₁)
f ⊑f g = ∀[ x ∶ ∣ F ∣F ] f x ⊑[ pos F ] g x

_⊑N_ : Order (ℓ-max ℓ₀ ℓ₁) (Nucleus F)
(j , _) ⊑N (k , _) = j ⊑f k

endopos : Poset ℓ₀ (ℓ-max ℓ₀ ℓ₁)
endopos =
  (∣ F ∣F → ∣ F ∣F) , _⊑f_ , is-set , ⊑f-refl , ⊑f-trans , ⊑f-antisym where

  ⊑f-refl : [ isReflexive _⊑f_ ]
  ⊑f-refl f x = ⊑[ pos F ]-refl (f x)

  ⊑f-trans : [ isTransitive _⊑f_ ]
  ⊑f-trans f g h f⊑g g⊑h x = f x ⊑⟨ f⊑g x ⟩ g x ⊑⟨ g⊑h x ⟩ h x ■

  is-set : isSet (∣ F ∣F → ∣ F ∣F)
  is-set = isSetΠ λ x → carrier-is-set (pos F)

  ⊑f-antisym : [ isAntisym is-set _⊑f_ ]
  ⊑f-antisym f g f⊑g g⊑h =
    funExt λ x → ⊑[ pos F ]-antisym (f x) (g x) (f⊑g x) (g⊑h x)

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
compFam : {A : Type ℓ₀} (α : Fam ℓ₂ (A → A)) → Fam ℓ₂ (A → A)
compFam {A = A} α = List (index α) , f where

  f : List (index α) → A → A
  f []       = idfun A
  f (i ∷ is) = f is ∘ (α $ i)

id-is-nuclear : (F : Frame ℓ₀ ℓ₁ ℓ₂) → isPrenuclear F (idfun ∣ F ∣F)
id-is-nuclear F = (λ _ _ → refl) , ⊑[ pos F ]-refl

compFam-of-nucleus-nucleus : (α : Fam ℓ₂ (∣ F ∣F → ∣ F ∣F))
                           → ((i : index α) → isPrenuclear F (α $ i))
                           → (i : List (index α)) → isPrenuclear F ((compFam α) $ i)
compFam-of-nucleus-nucleus α φ []       = id-is-nuclear F
compFam-of-nucleus-nucleus α φ (i ∷ is) = n₀ , n₁ where

  j = compFam α $ (i ∷ is)

  j′ : ∣ F ∣F → ∣ F ∣F
  j′ = compFam α $ is

  ih : isPrenuclear F j′
  ih = compFam-of-nucleus-nucleus α φ is

  j′-n₀ : (x y : ∣ F ∣F) → j′ (x ⊓[ F ] y) ≡ j′ x ⊓[ F ] j′ y
  j′-n₀ = fst ih

  j′-n₁ : (x : ∣ F ∣F) → [ x ⊑[ pos F ] j′ x ]
  j′-n₁ = snd ih

  n₀ : (x y : ∣ F ∣F)
     → (compFam α $ (i ∷ is)) (x ⊓[ F ] y)
     ≡ (compFam α $ (i ∷ is)) x ⊓[ F ] (compFam α $ (i ∷ is)) y
  n₀ x y = (j′ ∘ (α $ i)) (x ⊓[ F ] y)     ≡⟨ refl                      ⟩
           j′ ((α $ i) (x ⊓[ F ] y))       ≡⟨ cong j′ (fst (φ i) x y)   ⟩
           j′ ((α $ i) x ⊓[ F ] (α $ i) y) ≡⟨ j′-n₀ _ _                 ⟩
           ((compFam α $ (i ∷ is)) x) ⊓[ F ] ((compFam α $ (i ∷ is)) y) ∎

  n₁ : (x : ∣ F ∣F) → [ x ⊑[ pos F ] j x ]
  n₁ x = x ⊑⟨ snd (φ i) x ⟩ (α $ i) x ⊑⟨ j′-n₁ _ ⟩ j′ ((α $ i) x) ■
```

```agda
_^* : Fam ℓ₂ (Nucleus F) → Fam ℓ₂ (∣ F ∣F → ∣ F ∣F)
J ^* = compFam ⁅ j ∣ (j , _) ε J ⁆
```

```agda
J*-++-lemma : (J : Fam ℓ₂ (Nucleus F))
            → (is js : index (J ^*))
            → (x : ∣ F ∣F)
            → ((J ^*) $ (is ++ js)) x ≡ (((J ^*) $ js) ∘ ((J ^*) $ is)) x
J*-++-lemma J []       js x = refl
J*-++-lemma J (i ∷ is) js x = J*-++-lemma J is js (fst (J $ i) x)

J*-++ : (J : Fam ℓ₂ (Nucleus F))
      → (is js : index (J ^*))
      → ((J ^*) $ (is ++ js)) ≡ (((J ^*) $ js) ∘ ((J ^*) $ is))
J*-++ J is js = funExt (J*-++-lemma J is js)
```

```agda
J*-inhabited : (J : Fam ℓ₂ (Nucleus F))
             → ∥ index (J ^*) ∥
J*-inhabited J = ∣ [] ∣
```


```agda
_⦅_⦆_ : (J : Fam ℓ₂ (Nucleus F)) → index J → ∣ F ∣F → ∣ F ∣F
J ⦅ i ⦆ x = fst (J $ i) x

_*⦅_⦆_ : (J : Fam ℓ₂ (Nucleus F)) → index (J ^*) → ∣ F ∣F → ∣ F ∣F
J *⦅ is ⦆ x = ((J ^*) $ is) x
```

```agda
J*-closed-under-⊓ : (J : Fam ℓ₂ (Nucleus F))
                  → (is js : index (J ^*))
                  → Σ[ ks ∈ index (J ^*) ]
                     [ ⟨ J ^* $ is , J ^* $ js ⟩⊑[ endopos ] (J ^* $ ks) ]
J*-closed-under-⊓ J is js =
  (is ++ js) , J*is⊑J*is++js is js , J*js⊑J*is++js is js where

  Jᵢ-prenuclear : (i : index J) → isPrenuclear F ((fst ⟨$⟩ J) $ i)
  Jᵢ-prenuclear i = fst (snd (J $ i)) , fst (snd (snd (J $ i)))

  J*-prenuclear : (is : index (J ^*)) → isPrenuclear F ((J ^*) $ is)
  J*-prenuclear = compFam-of-nucleus-nucleus (fst ⟨$⟩ J) Jᵢ-prenuclear

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
J*-directed J = J*-inhabited J , λ is js → ∣ J*-closed-under-⊓ J is js ∣
```

```agda
isScottContinuous : (∣ F ∣F → ∣ F ∣F) → hProp (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-suc ℓ₂))
isScottContinuous j =
  ∀[ U ∶ Fam ℓ₂ ∣ F ∣F ] isDirected (pos F) U ⇒ ((j (⋁[ F ] U) ≡ (⋁[ F ] ⁅ j x ∣ x ε U ⁆)) , carrier-is-set (pos F) _ _)
```

```agda
J*-scott-continuous : (J : Fam ℓ₂ (Nucleus F))
                    → [ ∀[ i ∶ index J ] isScottContinuous (J ⦅ i ⦆_) ]
                    → (is : index (J ^*)) → [ isScottContinuous (J *⦅ is ⦆_) ]
J*-scott-continuous J J-sc []       U dir = refl
J*-scott-continuous J J-sc (i ∷ is) U dir =
  J *⦅ i ∷ is ⦆ (⋁[ F ] U)                 ≡⟨ refl                             ⟩
  J *⦅ is ⦆ (J ⦅ i ⦆ (⋁[ F ] U))           ≡⟨ cong (J *⦅ is ⦆_) (J-sc _ U dir) ⟩
  J *⦅ is ⦆ (⋁[ F ] ⁅ J ⦅ i ⦆ x ∣ x ε U ⁆) ≡⟨ ⦅𝟐⦆  ⟩
  ⋁[ F ] ⁅ J *⦅ i ∷ is ⦆ x ∣ x ε U ⁆       ∎
  where
    J-prenucleus : (i : index J) → Prenucleus F
    J-prenucleus i = fst (J $ i) , (fst (snd (J $ i))) , fst (snd (snd (J $ i)))

    nts : (j k : index U)
        → Σ[ l ∈ index U ] [ ⟨ (U $ j) , (U $ k) ⟩⊑[ pos F ] (U $ l) ]
        → ∥ Σ[ l ∈ index U ] [ rel₂ (pos F) (J ⦅ i ⦆ (U $ j)) (J ⦅ i ⦆ (U $ k)) (J ⦅ i ⦆ (U $ l)) ] ∥
    nts j k (l , p , q) = ∣ l , (monop F (J-prenucleus i) _ _ p   , monop F (J-prenucleus i) _ _ q) ∣

    dir′ : [ isDirected (pos F) ⁅ J ⦅ i ⦆ x ∣ x ε U ⁆ ]
    dir′ = (fst dir) , (λ j k → ∥∥-rec (∥∥-prop _) (nts j k) (snd dir j k))

    ⦅𝟐⦆ : _
    ⦅𝟐⦆ = J*-scott-continuous J J-sc is (⁅ J ⦅ i ⦆ x ∣ x ε U ⁆) dir′
```

```agda
⋁N_ : (α : Fam ℓ₂ (Nucleus F))
    → [ ∀[ i ∶ index α ] (isScottContinuous (α ⦅ i ⦆_)) ]
    → Nucleus F
⋁N_ J α-sc = N where

  J* : Fam ℓ₂ (∣ F ∣F → ∣ F ∣F)
  J* = J ^*

  J*-prenuclear : (is : index J*) → isPrenuclear F (J* $ is)
  J*-prenuclear = compFam-of-nucleus-nucleus _ λ i →
                   fst (snd (J $ i)) , fst (snd (snd (J $ i)))

  J*-sec : (is : index J*) → [ isScottContinuous (J *⦅ is ⦆_) ]
  J*-sec = J*-scott-continuous J α-sc

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

        k = fst (J*-closed-under-⊓ J i j)

        nts₂ : _
        nts₂ = (J* $ i) x ⊓[ F ] (J* $ j) y ⊑⟨ cleft F (J *⦅ j ⦆ y)
                                               (fst (snd (J*-closed-under-⊓ J i j)) x) ⟩
               (J* $ k) x ⊓[ F ] (J* $ j) y ⊑⟨ cright F (J *⦅ k ⦆ x)
                                                        (snd (snd (J*-closed-under-⊓ J i j)) y) ⟩
               (J* $ k) x ⊓[ F ] (J* $ k) y ⊑⟨ ⋁[ F ]-upper _ _ (k , refl) ⟩
               (⋁[ F ] ⁅ γ x ⊓[ F ] γ y ∣ γ ε J* ⁆) ■

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
         ⋁[ F ] ⁅ ⋁[ F ] ⁅ α (β x) ∣ β ε J* ⁆ ∣ α ε J* ⁆          ⊑⟨ ⦅𝟏⦆   ⟩
         ⋁[ F ] ⁅ ((J* $ j) ((J* $ i) x)) ∣ (j , i) ∶ (_ × _) ⁆   ⊑⟨ ⦅𝟑⦆  ⟩
         ⋁[ F ] ⁅ β x ∣ β ε J* ⁆                                  ■
    where
      rem : [ ∀[ z ε _ ] (z ⊑[ pos F ] ⋁[ F ] ⁅ β x ∣ β ε J* ⁆) ]
      rem z ((js , is) , eq) = ⋁[ F ]-upper _ _ ((is ++ js) , (_ ≡⟨ J*-++-lemma J is js x ⟩ (((J ^*) $ js) ∘ ((J ^*) $ is)) x ≡⟨ eq ⟩ z ∎))

      dir : [ isDirected (pos F) ⁅ β x ∣ β ε J* ⁆ ]
      dir = ∣ [] ∣ , upper-bounds where

        upper-bounds : _
        upper-bounds is js = ∣ ks , fst (snd (J*-closed-under-⊓ J is js)) x , snd (snd (J*-closed-under-⊓ J is js)) x ∣ where

          ks : index (J ^*)
          ks = fst (J*-closed-under-⊓ J is js)

      goal : (λ is → (J* $ is) (⋁[ F ] fmap (λ β → β x) J*)) ≡ (λ is → ⋁[ F ] fmap (λ β → (J* $ is) (β x)) J*)
      goal = funExt λ is → J*-scott-continuous J α-sc is ⁅ β x ∣ β ε J* ⁆ dir

      ⦅𝟎⦆ = ≡⇒⊑ (pos F) (cong (λ - → ⋁[ F ] (index J* , -)) goal)
      ⦅𝟏⦆ = ≡⇒⊑ (pos F) (sym (flatten F (index J*) (λ _ → index J*) λ j i → (J* $ j) ((J* $ i) x)))
      ⦅𝟑⦆ = ⋁[ F ]-least _ _ rem


  N : Nucleus F
  N = 𝕚 , n₀ , n₁ , n₂

{--

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

-- --}
-- --}
-- --}
```
