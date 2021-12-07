---
title: Stone Locales
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Cubical.Functions.Logic
open import Frame

module Stone (F : Frame 𝓤 𝓥 𝓦) where

open import Poset
open import WayBelow
open import Regular
open import Base
open import Spectral
open import Cubical.Data.List hiding ([_])
```
-->

## Definition of Stone

```agda
isComplemented : Fam 𝓦 ∣ F ∣F → (𝓤 ∨ 𝓦) ̇
isComplemented S = (x : ∣ F ∣F) → x ε S → hasComplement F x
```

```agda
isZeroDimensionalₛ : (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇ 
isZeroDimensionalₛ = Σ[ ℬ ∈ Fam 𝓦 ∣ F ∣F ] isBasisFor F ℬ × isComplemented ℬ
```

```agda
isZeroDimensional : hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺)
isZeroDimensional = ∥ isZeroDimensionalₛ ∥Ω
```

```agda
isStone′ : hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺)
isStone′ = isCompact F ⊓ isZeroDimensional
```

```agda
isStoneₛ : (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇ 
isStoneₛ = [ isCompact F ] × isZeroDimensionalₛ
```

```agda
⋜→≪ : [ isCompact F ]
    → (x y : ∣ F ∣F) → x ⋜[ F ] y → [ _≪_ F x y ]
⋜→≪ F-comp x y (z , comp₀ , comp₁) S S-dir p =
  ∥∥-rec (∥∥-prop _) main rem
  where
  open PosetReasoning (pos F)

  nts : [ ⊤[ F ] ⊑[ pos F ] ⋁[ F ] ⁅ s ∨[ F ] z ∣ s ε S ⁆ ]
  nts = ⊤[ F ]                          ⊑⟨ ≡⇒⊑ (pos F) (sym comp₁) ⟩
        y ∨[ F ] z                      ⊑⟨ ∨-cleft F _ _ _ p       ⟩
        (⋁[ F ] S) ∨[ F ] z             ⊑⟨ G𝟏                      ⟩
        (⋁[ F ] ⁅ s ∨[ F ] z ∣ s ε S ⁆) ■
    where
    G𝟏 : [ (⋁[ F ] S) ∨[ F ] z ⊑[ pos F ] ⋁[ F ] ⁅ s ∨[ F ] z ∣ s ε S ⁆ ]
    G𝟏 = ⋁[ F ]-least _ _ G𝟐
      where
      G𝟐 : [ ∀[ w ε ⁅ (⋁[ F ] S) , z ⁆ ] (w ⊑[ pos F ] ⋁[ F ] ⁅ s ∨[ F ] z ∣ s ε S ⁆) ]
      G𝟐 = ∥∥-rec (isProp[] (∀[ w ε ⁅ (⋁[ F ] S) , z ⁆ ] (_ ⊑[ pos F ] _))) G𝟑 (π₀ S-dir)
        where
        G𝟑 : index S
           → [ ∀[ w ε ⁅ (⋁[ F ] S) , z ⁆ ] (w ⊑[ pos F ] ⋁[ F ] ⁅ s ∨[ F ] z ∣ s ε S ⁆) ]
        G𝟑 i w (true  , eq) = w                             ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩
                              ⋁[ F ] S                      ⊑⟨ ⋁[ F ]-least _ _ G𝟒  ⟩
                              ⋁[ F ] ⁅ s ∨[ F ] z ∣ s ε S ⁆ ■
          where
          G𝟒 : _
          G𝟒 v (k , eq′) =
            v                             ⊑⟨ ≡⇒⊑ (pos F) (sym eq′)          ⟩
            S $ k                         ⊑⟨ ⋁[ F ]-upper _ _ (true , refl) ⟩
            (S $ k) ∨[ F ] z              ⊑⟨ ⋁[ F ]-upper _ _ (k , refl)    ⟩
            ⋁[ F ] ⁅ s ∨[ F ] z ∣ s ε S ⁆ ■
        G𝟑 i w (false , eq) =
          w                ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩
          z                ⊑⟨ ⋁[ F ]-upper _ _ (false , refl) ⟩
          (S $ i) ∨[ F ] z ⊑⟨ ⋁[ F ]-upper _ _ (i , refl)  ⟩
          _                ■

  dir : [ isDirected (pos F) (⁅ s ∨[ F ] z ∣ s ε S ⁆) ]
  π₀ dir = π₀ S-dir
  π₁ dir i j = ∥∥-rec (∥∥-prop _) G𝟏 (π₁ S-dir i j)
    where
    G𝟏 : _
    G𝟏 (k , p , q) = ∣ k , (∨-cleft F _ _ _ p , ∨-cleft F _ _ _ q) ∣

  rem : ∥ Σ[ i ∈ index S ] (S $ i) ∨[ F ] z ≡ ⊤[ F ] ∥
  rem = ∥∥-rec (∥∥-prop _) goal (F-comp (⁅ s ∨[ F ] z ∣ s ε S ⁆) dir nts)
    where
    goal : _
    goal (i , ϕ) = ∣ i , ⊑[ pos F ]-antisym _ _ (⊤[ F ]-top _) ϕ ∣

  main : Σ[ i ∈ index S ] (S $ i) ∨[ F ] z ≡ ⊤[ F ]
       → ∥ Σ[ i ∈ index S ] [ x ⊑[ pos F ] (S $ i) ] ∥
  main (i , ϕ) = ∣ i , G𝟏 ∣
    where
    open SomePropertiesOf⋜ F

    G𝟏 : [ x ⊑[ pos F ] (S $ i) ]
    G𝟏 = a⋜b→a⊑b x (S $ i) (z , (comp₀ , ϕ))
```

```agda
clopen→compact-in-compact-locale : [ isCompact F ]
                                 → (x : ∣ F ∣F)
                                 → hasComplement F x
                                 → [ _≪_ F x x ]
clopen→compact-in-compact-locale ⊤≪⊤ x x-clop = ⋜→≪ ⊤≪⊤ x x x-clop
```

```agda
directify-clopen : (ℬ : Fam 𝓦 ∣ F ∣F)
                 → isComplemented ℬ
                 → isComplemented (directify F ℬ)
directify-clopen ℬ@(I , β) ψ b (is , eq) = subst (hasComplement F) eq (nts is)
  where
  nts : (is : List I) → hasComplement F (directify F ℬ $ is)
  nts []       = subst (hasComplement F) refl (⊤[ F ] , G𝟏 , G𝟐)
                   where
                   G𝟏 : ⊥[ F ] ⊓[ F ] ⊤[ F ] ≡ ⊥[ F ]
                   G𝟏 = x∧⊤=x F ⊥[ F ]

                   G𝟐 : ⊥[ F ] ∨[ F ] ⊤[ F ] ≡ ⊤[ F ]
                   G𝟐 = x∨⊥=x F ⊤[ F ]
  nts (i ∷ is) = subst (hasComplement F) refl goal
    where
    ¬βᵢ : ∣ F ∣F
    ¬βᵢ = π₀ (ψ (β i) (i , refl))

    ¬dir : ∣ F ∣F
    ¬dir = π₀ (nts is)

    goal : hasComplement F (β i ∨[ F ] (directify F ℬ $ is))
    goal = (¬βᵢ ⊓[ F ] ¬dir)
         , (complements-sym F (∧-complement F _ _ _ _ (complements-sym F (π₁ (ψ (β i) (i , refl)))) ((complements-sym F (π₁ (nts is))))))
```

```agda
clopen-basis-∧-complement : (ℬ : Fam 𝓦 ∣ F ∣F)
                          → isComplemented ℬ
                          → (i j : index ℬ)
                          → hasComplement F ((ℬ $ i) ⊓[ F ] (ℬ $ j))
clopen-basis-∧-complement ℬ κ i j =
    (¬ℬᵢ ∨[ F ] ¬ℬⱼ)
  , ∧-complement F (ℬ $ i) (ℬ $ j) ¬ℬᵢ ¬ℬⱼ ¬ℬᵢ-complements-ℬᵢ ¬ℬⱼ-complements-ℬⱼ
  where
  ¬ℬᵢ : ∣ F ∣F
  ¬ℬᵢ = π₀ (κ (ℬ $ i) (i , refl))

  ¬ℬⱼ : ∣ F ∣F
  ¬ℬⱼ = π₀ (κ (ℬ $ j) (j , refl))

  ¬ℬᵢ-complements-ℬᵢ : complements F (ℬ $ i) ¬ℬᵢ
  ¬ℬᵢ-complements-ℬᵢ = π₁ (κ (ℬ $ i) (i , refl))

  ¬ℬⱼ-complements-ℬⱼ : complements F (ℬ $ j) ¬ℬⱼ
  ¬ℬⱼ-complements-ℬⱼ = π₁ (κ (ℬ $ j) (j , refl))
```

```agda
compact→basic : (ℬ : Fam 𝓦 ∣ F ∣F) → isDirBasisFor F ℬ
              → (x : ∣ F ∣F) → [ _≪_ F x x ] → ∥ x ε ℬ ∥
compact→basic ℬ basis x x≪x = ∥∥-rec (∥∥-prop (x ε ℬ)) goal (x≪x C C-dir C-covers-x₀)
  where
  open PosetReasoning (pos F)

  𝒥 : Fam 𝓦 (index ℬ)
  𝒥 = π₀ (basis x)

  C : Fam 𝓦 ∣ F ∣F
  C = ⁅ ℬ $ j ∣ j ε 𝒥 ⁆

  C-dir : [ isDirected (pos F) C ]
  C-dir = π₀ (π₁ (basis x))

  C-covers-x : x ≡ (⋁[ F ] C)
  C-covers-x = ⋁-unique F _ _ (π₀ (π₁ (π₁ (basis x)))) (π₁ (π₁ (π₁ (basis x))))

  C-covers-x₀ : [ x ⊑[ pos F ] ⋁[ F ] C ]
  C-covers-x₀ = ≡⇒⊑ (pos F) C-covers-x

  goal : Σ[ i ∈ index C ] [ x ⊑[ pos F ] (C $ i) ] → ∥ x ε ℬ ∥
  goal (i , x≤cᵢ) = ∣ 𝒥 $ i , ⊑[ pos F ]-antisym _ _ down up ∣
    where
    down : [ (ℬ $ (𝒥 $ i)) ⊑[ pos F ] x ]
    down = ℬ $ 𝒥 $ i                ⊑⟨ ⋁[ F ]-upper _ _ (i , refl)  ⟩
           ⋁[ F ] ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ ⊑⟨ ≡⇒⊑ (pos F) (sym C-covers-x) ⟩
           x ■

    up : [ x ⊑[ pos F ] (ℬ $ (𝒥 $ i)) ]
    up = x≤cᵢ
```

```agda
clopen→basic-in-stone-locale : isStoneₛ
                             → (ℬ : Fam 𝓦 ∣ F ∣F)
                             → isDirBasisFor F ℬ
                             → (x : ∣ F ∣F) → hasComplement F x → ∥ x ε ℬ ∥
clopen→basic-in-stone-locale (⊤≪⊤ , _) ℬ basis x x-clop =
  compact→basic ℬ basis x (clopen→compact-in-compact-locale ⊤≪⊤ x x-clop)
  where
  𝒥 = π₀ (basis x)

  C : Fam 𝓦 ∣ F ∣F
  C = ⁅ ℬ $ j ∣ j ε 𝒥 ⁆
```

```agda
stone→spectral : isStoneₛ → isSpectralₛ F
stone→spectral stone@(⊤≪⊤ , ℬ , b , κ) = ℬ↑ , κ↑ , dir-basis , ∧-closure
  where
  ℬ↑ : Fam 𝓦 ∣ F ∣F
  ℬ↑ = directify F ℬ

  ζ : (is : index ℬ↑) → hasComplement F (ℬ↑ $ is)
  ζ  is = directify-clopen ℬ κ (ℬ↑ $ is) (is , refl)

  κ↑ : (is : List (index ℬ)) → [ isCompactOpen F (ℬ↑ $ is) ]
  κ↑ is = clopen→compact-in-compact-locale ⊤≪⊤ (ℬ↑ $ is) (ζ is)

  dir-basis : isDirBasisFor F ℬ↑
  dir-basis = directified-basis-gives-basis F ℬ b

  ∧-closure : closedUnderFinMeets F ℬ↑
  ∧-closure = G𝟏 , G𝟐
    where
    G𝟏 : ∥ Σ[ t ∈ index ℬ↑ ] [ isTop (pos F) (ℬ↑ $ t) ] ∥
    G𝟏 = ∥∥-rec (∥∥-prop _) G𝟏a ⊤-basic
      where
      G𝟏a : ⊤[ F ] ε ℬ↑ → ∥ Σ[ t ∈ index ℬ↑ ] [ isTop (pos F) (ℬ↑ $ t) ] ∥
      G𝟏a (t , eq) = ∣ t , subst ([_] ∘ isTop (pos F)) (sym eq) ⊤[ F ]-top ∣

      ⊤-basic : ∥ ⊤[ F ] ε ℬ↑ ∥
      ⊤-basic = compact→basic ℬ↑ dir-basis ⊤[ F ] ⊤≪⊤

    G𝟐 : (is js : index ℬ↑)
       → ∥ Σ[ ks ∈ index ℬ↑ ] [ isInf (pos F) (ℬ↑ $ ks) (ℬ↑ $ is) (ℬ↑ $ js) ] ∥
    G𝟐 is js = ∥∥-rec (∥∥-prop _) goal foo
      where
      ∧↑-clop : hasComplement F ((ℬ↑ $ is) ⊓[ F ] (ℬ↑ $ js))
      ∧↑-clop = ∧-has-complement F (ℬ↑ $ is) (ℬ↑ $ js) (ζ is) (ζ js)

      foo : ∥ ((ℬ↑ $ is) ⊓[ F ] (ℬ↑ $ js)) ε ℬ↑ ∥
      foo = clopen→basic-in-stone-locale stone ℬ↑ dir-basis ((ℬ↑ $ is) ⊓[ F ] (ℬ↑ $ js)) ∧↑-clop

      goal : ((ℬ↑ $ is) ⊓[ F ] (ℬ↑ $ js)) ε ℬ↑
           → ∥ Σ[ ks ∈ index ℬ↑ ] [ isInf (pos F) (ℬ↑ $ ks) (ℬ↑ $ is) (ℬ↑ $ js) ] ∥
      goal (ks , eq) =
        ∣ ks , subst (λ - → [ isInf (pos F) - (ℬ↑ $ is) (ℬ↑ $ js) ]) (sym eq) inf ∣
        where
        inf : [ isInf (pos F) ((ℬ↑ $ is) ⊓[ F ] (ℬ↑ $ js)) (ℬ↑ $ is) (ℬ↑ $ js) ]
        inf = (⊓[ F ]-lower₀ _ _  , ⊓[ F ]-lower₁ _ _)
            , λ z (p , q) → ⊓[ F ]-greatest (ℬ↑ $ is) (ℬ↑ $ js) z p q
```
