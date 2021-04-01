---
title: Closed Nuclei
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis hiding (_∨_)
open import Frame

module ClosedNuclei (F : Frame 𝓤 𝓥 𝓦) where

open import Poset
open import Nucleus
```
-->

## Definition of closed nucleus

```agda
“_” : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
“ U ” V = U ∨[ F ] V
```


```agda
bin-dist-op : (x y z : ∣ F ∣F)
            → x ∨[ F ] (y ⊓[ F ] z) ≡ (x ∨[ F ] y) ⊓[ F ] (x ∨[ F ] z)
bin-dist-op x y z = sym nts
  where
  _∨_ : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
  _∨_ = λ x y → x ∨[ F ] y

  _∧_ : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
  _∧_ = λ x y → x ⊓[ F ] y

  ⦅𝟏⦆ = bin-dist F (x ∨ y) x z

  ⦅𝟐⦆ =
    ((x ∨ y) ∧ x) ∨ ((x ∨ y) ∧ z) ≡⟨ cong (_∨ (_ ∧ z)) (comm F (x ∨ y) x)    ⟩
    (x ∧ (x ∨ y)) ∨ ((x ∨ y) ∧ z) ≡⟨ cong (_∨ (_ ∧ z)) (absorption-op F x y) ⟩
    x ∨ ((x ∨ y) ∧ z)             ≡⟨ cong (x ∨_) (comm F (x ∨ y) z)          ⟩
    x ∨ (z ∧ (x ∨ y))             ∎

  ⦅𝟑⦆ = cong (x ∨_) (bin-dist F z x y)

  ⦅𝟒⦆ = x ∨ ((z ∧ x) ∨ (z ∧ y)) ≡⟨ sym (∨[ F ]-assoc x (z ∧ x) (z ∧ y))        ⟩
        (x ∨ (z ∧ x)) ∨ (z ∧ y) ≡⟨ cong (λ - → (x ∨ -) ∨ (z ∧ y)) (comm F z x) ⟩
        (x ∨ (x ∧ z)) ∨ (z ∧ y) ≡⟨ cong (λ - → - ∨ _) (absorption F x z)       ⟩
        (x ∨ (z ∧ y))           ≡⟨ cong (λ - → x ∨ -) (comm F z y)             ⟩
        (x ∨ (y ∧ z))           ∎

  nts : ((x ∨[ F ] y) ⊓[ F ] (x ∨[ F ] z)) ≡ x ∨[ F ] (y ⊓[ F ] z)
  nts = (x ∨ y) ∧ (x ∨ z)              ≡⟨ ⦅𝟏⦆ ⟩
        ((x ∨ y) ∧ x) ∨ ((x ∨ y) ∧ z)  ≡⟨ ⦅𝟐⦆ ⟩
        x ∨ (z ∧ (x ∨ y))              ≡⟨ ⦅𝟑⦆ ⟩
        x ∨ ((z ∧ x) ∨ (z ∧ y))        ≡⟨ ⦅𝟒⦆ ⟩
        x ∨ (y ∧ z)                    ∎
```

```agda
“”-preserves-meets : (U V W : ∣ F ∣F) → “ U ” (V ⊓[ F ] W) ≡ “ U ” V ⊓[ F ] “ U ” W
“”-preserves-meets U V W =
  “ U ” (V ⊓[ F ] W)               ≡⟨ refl ⟩
  U ∨[ F ] (V ⊓[ F ] W)            ≡⟨ bin-dist-op U V W ⟩
  (U ∨[ F ] V) ⊓[ F ] (U ∨[ F ] W) ≡⟨ refl ⟩
  “ U ” V ⊓[ F ] “ U ” W           ∎
```

```agda
“”-inflationary : (U V : ∣ F ∣F) → [ V ⊑[ pos F ] “ U ” V ]
“”-inflationary = ⊔[ F ]-upper₁
```

```agda
“”-idempotent : (U V : ∣ F ∣F) → [ “ U ” (“ U ” V) ⊑[ pos F ] “ U ” V ]
“”-idempotent U V =
  ⊔[ F ]-least U _ _ (⊔[ F ]-upper₀ U V) (⊑[ pos F ]-refl (“ U ” V))
```

```agda
ʻ_’ : ∣ F ∣F → Nucleus F
ʻ U ’ = “ U ” , “”-preserves-meets U , “”-inflationary U , “”-idempotent U
```
