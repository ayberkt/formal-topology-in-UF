---
title: Heyting Implication in a Frame
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Poset
open import Frame
open import Spectral

module HeytingImplication where

formsBasis : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ∣ F ∣F → (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
formsBasis {𝓥 = 𝓥} {𝓦} F B =
  ((x : ∣ F ∣F) →
     Σ[ U ∈ Fam 𝓦 (index B) ]
       [ isSup (pos F) ⁅ B $ u ∣ u ε U ⁆ x ])

hasBasis : (F : Frame 𝓤 𝓥 𝓦) → (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
hasBasis {𝓦 = 𝓦} F = Σ[ B ∈ Fam 𝓦 ∣ F ∣F ] formsBasis F B

module HeytingImplication (F : Frame 𝓤 𝓥 𝓦) where

  _isHeytingImplicationFor_ : ∣ F ∣F → ∣ F ∣F × ∣ F ∣F → hProp (𝓤 ∨ 𝓥)
  z isHeytingImplicationFor (x , y) =
    ∀[ w ∶ ∣ F ∣F ] (w ⊑[ pos F ] z) ⇔ ((x ⊓[ F ] w) ⊑[ pos F ] y)

  isHeytingImplication : (∣ F ∣F → ∣ F ∣F → ∣ F ∣F) → hProp (𝓤 ∨ 𝓥)
  isHeytingImplication _⇒_ =
    ∀[ x ∶ ∣ F ∣F ] ∀[ y ∶ ∣ F ∣F ]
      ((x ⇒ y) isHeytingImplicationFor (x , y))

module Definition (F : Frame 𝓤 𝓥 𝓥) (basis : hasBasis F) where

  open HeytingImplication F

  _≤_ : ∣ F ∣F → ∣ F ∣F → hProp 𝓥
  x ≤ y = x ⊑[ pos F ] y

  infix 3 _≤_

  _∧_ : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
  x ∧ y = x ⊓[ F ] y

  ℬ : 𝓥 ̇
  ℬ = π₀ (π₀ basis)

  β : ℬ → ∣ F ∣F
  β = π₁ (π₀ basis)

  _==>_ : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
  x ==> y =
    ⋁[ F ] ⁅ β b ∣ (b , _) ∶ Σ[ b ∈ ℬ ] [ (x ∧ β b) ≤ y ] ⁆

  mp : (x y : ∣ F ∣F) → [ x ⊓[ F ] (x ==> y) ⊑[ pos F ] y ]
  mp x y =
    x ⊓[ F ] (x ==> y)                    ⊑⟨ ≡⇒⊑ (pos F ) (dist F _ _) ⟩
    ⋁[ F ] ⁅ x ⊓[ F ] β b ∣ (b , _) ∶ _ ⁆ ⊑⟨ ⋁[ F ]-least _ _ γ        ⟩
    y                                     ■
    where
    open PosetReasoning (pos F)

    γ : _
    γ z ((_ , q) , eq) = subst (λ - → [ - ⊑[ pos F ] _ ]) eq q

  lemma : (x y : ∣ F ∣F) (c : ℬ)
        → [ (x ∧ β c ≤ y) ⇒ (β c ≤ x ==> y) ]
  lemma x y c p = ⋁[ F ]-upper _ _ ((c , p) , refl)

  ϕ : [ isHeytingImplication _==>_ ]
  ϕ x y z = forward , backward
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
        lub = π₁ (π₁ basis z)

      nts : _
      nts w (i , eq) = w          ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩
                       β (VV $ i) ⊑⟨ lemma x y (VV $ i) δ ⟩
                       x ==> y    ■
        where
        δ : [ x ⊓[ F ] β (VV $ i) ≤ y ]
        δ = x ∧ β (VV $ i)                ⊑⟨ cright F _ (⋁[ F ]-upper _ _ (i , refl)) ⟩
            x ∧ (⋁[ F ] ⁅ β v ∣ v ε VV ⁆) ⊑⟨ cright F _ (≡⇒⊑ (pos F) (sym ε)) ⟩
            x ∧ z                         ⊑⟨ p ⟩
            y                             ■
```
