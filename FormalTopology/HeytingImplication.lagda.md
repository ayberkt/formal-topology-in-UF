---
title: Heyting Implication in a Frame
author: Ayberk Tosun (j.w.w. Martín Escardó)
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Poset
open import Frame
open import Spectral
open import Nucleus

module HeytingImplication where
```
-->

## Basis

Given a (𝓤, 𝓥, 𝓦)-frame F, we say that some 𝓦-family on ∣ F ∣ forms a basis for
it iff for every x : ∣ F ∣, there exists a family U of basic elements such that
⋁ U is the join of x.

```agda
formsBasis : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ∣ F ∣F → (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
formsBasis {𝓥 = 𝓥} {𝓦} F B =
  ((x : ∣ F ∣F) →
     Σ[ U ∈ Fam 𝓦 (index B) ]
       [ isDirected (pos F) ⁅ B $ u ∣ u ε U ⁆ ⊓ isSup (pos F) ⁅ B $ u ∣ u ε U ⁆ x ])

-- F has a compact basis iff there is some 𝓦-family B s.t.
--
--   1. what I now have in `formsBasis`,
--   2. the compact elements form a meet-sublattice.

hasBasis : (F : Frame 𝓤 𝓥 𝓦) → (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
hasBasis {𝓦 = 𝓦} F = Σ[ B ∈ Fam 𝓦 ∣ F ∣F ] formsBasis F B
```

## Definition of Heyting implication

```agda
module DefnOfHeytingImplication (F : Frame 𝓤 𝓥 𝓦) where
```

We say that some z is the Heyting implication for (x, y) iff for every w, w ≤ z
iff (w ∧ x) ≤ y.

```agda
  _isHeytingImplicationFor_ : ∣ F ∣F → ∣ F ∣F × ∣ F ∣F → hProp (𝓤 ∨ 𝓥)
  z isHeytingImplicationFor (x , y) =
    ∀[ w ∶ ∣ F ∣F ] (w ⊑[ pos F ] z) ⇔ ((x ⊓[ F ] w) ⊑[ pos F ] y)
```

Given a binary operation on the frame, we say that it is a Heyting implication
iff it gives the Heyting implication for any two opens.

```agda
  isHeytingImplication : (∣ F ∣F → ∣ F ∣F → ∣ F ∣F) → hProp (𝓤 ∨ 𝓥)
  isHeytingImplication _⇒_ =
    ∀[ x ∶ ∣ F ∣F ] ∀[ y ∶ ∣ F ∣F ]
      ((x ⇒ y) isHeytingImplicationFor (x , y))
```

```agda
module HeytingImplicationProperties (F : Frame 𝓤 𝓥 𝓦) where

  open DefnOfHeytingImplication F

  lemma₀ : {x y z u v w : ∣ F ∣F}
      → [ u isHeytingImplicationFor (x , (y ⊓[ F ] z)) ]
      → [ v isHeytingImplicationFor (x , y) ]
      → [ w isHeytingImplicationFor (x , z) ]
      → u ≡ v ⊓[ F ] w
  lemma₀ {x} {y} {z} {u} {v} {w} p q r = ⊓-unique F v w u β₀ β₁ γ
    where
    open PosetReasoning (pos F)

    δ₀ : [ (x ⊓[ F ] u) ⊑[ pos F ] y ]
    δ₀ = x ⊓[ F ] u ⊑⟨ π₀ (p u) (⊑[ pos F ]-refl u) ⟩
         y ⊓[ F ] z ⊑⟨ ⊓[ F ]-lower₀ y z            ⟩
         y          ■

    δ₁ : [ (x ⊓[ F ] u) ⊑[ pos F ] z ]
    δ₁ = x ⊓[ F ] u ⊑⟨ π₀ (p u) (⊑[ pos F ]-refl u) ⟩
         y ⊓[ F ] z ⊑⟨ ⊓[ F ]-lower₁ y z            ⟩
         z          ■

    β₀ : [ u ⊑[ pos F ] v ]
    β₀ = π₁ (q u) δ₀

    β₁ : [ u ⊑[ pos F ] w ]
    β₁ = π₁ (r u) δ₁

    γ : (t : ∣ F ∣F)
      → [ t ⊑[ pos F ] v ] → [ t ⊑[ pos F ] w ] → [ t ⊑[ pos F ] u ]
    γ t ϕ ψ = π₁ (p t) ((⊓[ F ]-greatest y z (x ⊓[ F ] t) ε) ζ)
      where
      ε : [ x ⊓[ F ] t ⊑[ pos F ] y ]
      ε = x ⊓[ F ] t     ⊑⟨ cright F x ϕ                 ⟩
          x ⊓[ F ] v     ⊑⟨ π₀ (q v) (⊑[ pos F ]-refl v) ⟩
          y              ■

      ζ : [ (x ⊓[ F ] t) ⊑[ pos F ] z ]
      ζ = x ⊓[ F ] t     ⊑⟨ cright F x ψ                 ⟩
          x ⊓[ F ] w     ⊑⟨ π₀ (r w) (⊑[ pos F ]-refl w) ⟩
          z              ■
```

## Construction of the Heyting implication

```agda
module Definition (F : Frame 𝓤 𝓥 𝓥) (basis : hasBasis F) where
```

```agda
  open DefnOfHeytingImplication F

  _≤_ : ∣ F ∣F → ∣ F ∣F → hProp 𝓥
  x ≤ y = x ⊑[ pos F ] y

  infix 3 _≤_

  _∧_ : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
  x ∧ y = x ⊓[ F ] y

  ℬ : 𝓥 ̇
  ℬ = π₀ (π₀ basis)

  β : ℬ → ∣ F ∣F
  β = π₁ (π₀ basis)
```

We define the implication as follows:

```agda
  _==>_ : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
  x ==> y =
    ⋁[ F ] ⁅ β b ∣ (b , _) ∶ Σ[ b ∈ ℬ ] [ (x ∧ β b) ≤ y ] ⁆
```

Of course, the first thing we prove is modus ponens:

```agda
  mp : (x y : ∣ F ∣F) → [ x ⊓[ F ] (x ==> y) ⊑[ pos F ] y ]
  mp x y =
    x ⊓[ F ] (x ==> y)                    ⊑⟨ ≡⇒⊑ (pos F ) (dist F _ _) ⟩
    ⋁[ F ] ⁅ x ⊓[ F ] β b ∣ (b , _) ∶ _ ⁆ ⊑⟨ ⋁[ F ]-least _ _ γ        ⟩
    y                                     ■
    where
    open PosetReasoning (pos F)

    γ : _
    γ z ((_ , q) , eq) = subst (λ - → [ - ⊑[ pos F ] _ ]) eq q

  mp-op : (x y : ∣ F ∣F) → [ (x ==> y) ⊓[ F ] x ⊑[ pos F ] y ]
  mp-op x y = (x ==> y) ⊓[ F ] x ⊑⟨ ≡⇒⊑ (pos F) (comm F (x ==> y) x) ⟩
              x ⊓[ F ] (x ==> y) ⊑⟨ mp x y                           ⟩
              y                  ■
    where
    open PosetReasoning (pos F)
```

We now proceed to prove that this is the Heyting implication:

```agda
  lemma : (x y : ∣ F ∣F) (c : ℬ)
        → [ (x ∧ β c ≤ y) ⇒ (β c ≤ x ==> y) ]
  lemma x y c p = ⋁[ F ]-upper _ (β c) ((c , p) , refl)

  ==>-is-HI : [ isHeytingImplication _==>_ ]
  ==>-is-HI x y z = forward , backward
    where
    open PosetReasoning (pos F)

    forward : [ (z ≤ x ==> y) ⇒ (x ∧ z ≤ y) ]
    forward p = x ⊓[ F ] z         ⊑⟨ cright F _ p ⟩
                x ⊓[ F ] (x ==> y) ⊑⟨ mp x y       ⟩
                y                  ■

    backward : [ ((x ∧ z) ≤ y) ⇒ (z ≤ x ==> y) ]
    backward p = z                       ⊑⟨ ≡⇒⊑ (pos F) ε        ⟩
                 ⋁[ F ] ⁅ β v ∣ v ε VV ⁆ ⊑⟨ ⋁[ F ]-least _ _ nts ⟩
                 x ==> y                 ■
      where
      VV : Fam 𝓥 ℬ
      VV = π₀ (π₁ basis z)

      ε : z ≡ ⋁[ F ] ⁅ β v ∣ v ε VV ⁆
      ε = ⋁-unique F ⁅ β v ∣ v ε VV ⁆ _ (π₀ lub) (π₁ lub)
        where
        lub = π₁ (π₁ (π₁ basis z))

      nts : _
      nts w (i , eq) = w          ⊑⟨ ≡⇒⊑ (pos F) (sym eq)                              ⟩
                       β (VV $ i) ⊑⟨ ⋁[ F ]-upper _ (β (VV $ i)) ((VV $ i , δ) , refl) ⟩
                       x ==> y    ■
        where
        δ : [ x ⊓[ F ] β (VV $ i) ≤ y ]
        δ = x ∧ β (VV $ i)                ⊑⟨ cright F _ (⋁[ F ]-upper _ _ (i , refl)) ⟩
            x ∧ (⋁[ F ] ⁅ β v ∣ v ε VV ⁆) ⊑⟨ cright F _ (≡⇒⊑ (pos F) (sym ε))         ⟩
            x ∧ z                         ⊑⟨ p                                        ⟩
            y                             ■

  ==>-id : (x : ∣ F ∣F) → x ==> x ≡ ⊤[ F ]
  ==>-id x = ⊑[ pos F ]-antisym (x ==> x) ⊤[ F ] (⊤[ F ]-top (x ==> x)) G𝟐
    where
    G𝟐 : [ ⊤[ F ] ⊑[ pos F ] (x ==> x) ]
    G𝟐 = π₁ (==>-is-HI x x ⊤[ F ]) (⊓[ F ]-lower₀ x ⊤[ F ])

  ==>-nucleus-lemma : (x y : ∣ F ∣F) (j : Nucleus F)
                    → [ (x ==> y) ⊑[ pos F ] (π₀ j x ==> π₀ j y) ]
  ==>-nucleus-lemma x y 𝒿@(j , 𝓃₀ , 𝓃₁ , 𝓃₂) =
    (x ==> y)      ⊑⟨ ⦅𝟏⦆ ⟩
    (x ==> j y)    ⊑⟨ ⦅𝟐⦆ ⟩
    (j x ==> j y)  ■
    where
    open PosetReasoning (pos F)

    ⦅𝟏⦆ : [ (x ==> y) ⊑[ pos F ] (x ==> j y) ]
    ⦅𝟏⦆ = π₁ (==>-is-HI x (j y) (x ==> y)) (_ ⊑⟨ mp x y ⟩ y ⊑⟨ 𝓃₁ y ⟩ j y ■)

    ⦅𝟐⦆ : [ (x ==> j y) ⊑[ pos F ] (j x ==> j y) ]
    ⦅𝟐⦆ = π₁ (==>-is-HI (j x) (j y) (x ==> j y)) ⦅𝟐a⦆
      where
      ⦅𝟐a⦆ : [ j x ⊓[ F ] (x ==> j y) ⊑[ pos F ] (j y) ]
      ⦅𝟐a⦆ =
        j x ⊓[ F ] (x ==> j y)   ⊑⟨ cright F (j x) (𝓃₁ (x ==> j y))      ⟩
        j x ⊓[ F ] j (x ==> j y) ⊑⟨ ≡⇒⊑ (pos F) (sym (𝓃₀ x (x ==> j y))) ⟩
        j (x ⊓[ F ] (x ==> j y)) ⊑⟨ mono F 𝒿 _ _ (mp x (j y))            ⟩
        j (j y)                  ⊑⟨ 𝓃₂ y                                 ⟩
        j y                      ■

  ∨-cright : (x y z : ∣ F ∣F)
           → [ y ⊑[ pos F ] z ] → [ (x ∨[ F ] y) ⊑[ pos F ] (x ∨[ F ] z) ]
  ∨-cright x y z p = ⋁[ F ]-least _ _ nts
    where
    open PosetReasoning (pos F)

    nts : _
    nts w (true  , eq) =
      w ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ x ⊑⟨ ⊔[ F ]-upper₀ x z ⟩ x ∨[ F ] z ■
    nts w (false , eq) =
      w ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ y ⊑⟨ p ⟩  z ⊑⟨ ⊔[ F ]-upper₁ x z ⟩ x ∨[ F ] z ■

  ∨-cleft : (x y z : ∣ F ∣F)
          → [ x ⊑[ pos F ] y ] → [ (x ∨[ F ] z) ⊑[ pos F ] (y ∨[ F ] z)  ]
  ∨-cleft x y z p = ⋁[ F ]-least _ _ nts
    where
    open PosetReasoning (pos F)

    nts : _
    nts w (true  , eq) = w            ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩
                         x            ⊑⟨ p                    ⟩
                         y            ⊑⟨ ⊔[ F ]-upper₀ y z    ⟩
                         y ∨[ F ] z   ■
    nts w (false , eq) = w ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ z ⊑⟨ ⊔[ F ]-upper₁ y z ⟩ y ∨[ F ] z ■

  ==>-∨-lemma : (x y z : ∣ F ∣F)
              → [ ((x ==> z) ⊓[ F ] (y ==> z)) ⊑[ pos F ] ((x ∨[ F ] y) ==> z) ]
  ==>-∨-lemma x y z = π₁ (==>-is-HI _ _ _) G𝟏
    where
    open PosetReasoning (pos F)

    G𝟏 : [ (x ∨[ F ] y) ⊓[ F ] ((x ==> z) ⊓[ F ] (y ==> z)) ⊑[ pos F ] z ]
    G𝟏 = (x ∨[ F ] y) ⊓[ F ] ((x ==> z) ⊓[ F ] (y ==> z))   ⊑⟨ ≡⇒⊑ (pos F) (comm F _ _) ⟩
         ((x ==> z) ⊓[ F ] (y ==> z)) ⊓[ F ](x ∨[ F ] y)    ⊑⟨ ≡⇒⊑ (pos F) (bin-dist F ((x ==> z) ⊓[ F ] (y ==> z)) x y)  ⟩
         (((x ==> z) ⊓[ F ] (y ==> z)) ⊓[ F ] x) ∨[ F ] (((x ==> z) ⊓[ F ] (y ==> z)) ⊓[ F ] y) ⊑⟨ ⦅𝟏⦆ ⟩
         ((x ==> z) ⊓[ F ] x) ∨[ F ] (((x ==> z) ⊓[ F ] (y ==> z)) ⊓[ F ] y) ⊑⟨ ⦅𝟐⦆ ⟩
         ((x ==> z) ⊓[ F ] x) ∨[ F ] ((y ==> z) ⊓[ F ] y) ⊑⟨ ∨-cright _ _ _ (≡⇒⊑ (pos F) (comm F (y ==> z) y)) ⟩
         ((x ==> z) ⊓[ F ] x) ∨[ F ] (y ⊓[ F ] (y ==> z)) ⊑⟨ ∨-cright _ _ _ (mp y z) ⟩
         ((x ==> z) ⊓[ F ] x) ∨[ F ] z                    ⊑⟨ ∨-cleft _ _ _ (≡⇒⊑ (pos F) (comm F _ _)) ⟩
         (x ⊓[ F ] (x ==> z)) ∨[ F ] z                    ⊑⟨ ∨-cleft _ _ _ (mp x z) ⟩
         z ∨[ F ] z                                       ⊑⟨ ≡⇒⊑ (pos F) (x∨x=x F z) ⟩
         z                                                ■
      where
      G𝟐 = ∨-cright z _ _ (mp y z)

      ⦅𝟏⦆ = ∨-cleft _ _ _ (cleft F _ (⊓[ F ]-lower₀ _ _))

      ⦅𝟐⦆ : _
      ⦅𝟐⦆ = ∨-cright _ _ _ (cleft F _ (⊓[ F ]-lower₁ _ _))
```
