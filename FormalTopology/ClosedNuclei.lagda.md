---
title: Closed Nuclei
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis hiding (_∨_)
open import Frame

module ClosedNuclei where

open import Cubical.Data.List using (_∷_; [])
open import Poset
open import Nucleus
open import HeytingImplication
open import Spectral
open import Regular
```
-->

## Definition of closed nucleus

```agda
module OpenNuclei (F : Frame 𝓤 𝓥 𝓦) where

  “_” : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
  “ U ” V = U ∨[ F ] V

  _∧_ : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
  U ∧ V = U ⊓[ F ] V

  infixr 4 _∧_
```

```agda
  bin-dist-op : (x y z : ∣ F ∣F)
              → x ∨[ F ] (y ⊓[ F ] z) ≡ (x ∨[ F ] y) ⊓[ F ] (x ∨[ F ] z)
  bin-dist-op x y z = sym nts
    where
    _∨_ : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
    _∨_ = λ x y → x ∨[ F ] y

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

```agda
module _ (F : Frame 𝓤 𝓥 𝓦) where

  open import PatchFrame hiding (𝟏)
  open OpenNuclei F

  ‘’-sc : (U : ∣ F ∣F) → isScottCont F ʻ U ’
  ‘’-sc U α α-dir = ⋁-unique F _ _ γ ε
    where
    open PosetReasoning (pos F)

    γ : (x : ∣ F ∣F) → x ε ⁅ “ U ” a ∣ a ε α ⁆ → [ x ⊑[ pos F ] “ U ” (⋁[ F ] α) ]
    γ x (i , eq) = subst (λ - → [ - ⊑[ pos F ] _ ]) eq (⋁[ F ]-least _ _ δ)
      where
      δ : _
      δ y (true  , eq′) = ⋁[ F ]-upper _ _ (true , eq′)
      δ y (false , eq′) =
        y                   ⊑⟨ ≡⇒⊑ (pos F) (sym eq′)           ⟩
        α $ i               ⊑⟨ ⋁[ F ]-upper _ _ (i , refl)     ⟩
        ⋁[ F ] α            ⊑⟨ ⋁[ F ]-upper _ _ (false , refl) ⟩
        U ∨[ F ] (⋁[ F ] α) ■

    ε : (w : ∣ F ∣F)
      → [ ∀[ o ε ⁅ “ U ” a ∣ a ε α ⁆ ] (o ⊑[ pos F ] w) ]
      → [ “ U ” (⋁[ F ] α) ⊑[ pos F ] w ]
    ε w ϕ = ∥∥-rec (isProp[] (_ ⊑[ pos F ] _)) ζ (π₀ α-dir)
      where
      ζ : index α → [ (“ U ” (⋁[ F ] α)) ⊑[ pos F ] w ]
      ζ i = ⋁[ F ]-least _ _ η
        where
        η : _
        η x (true , eq) = x ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ U ⊑⟨ ⋁[ F ]-upper _ _ (true , refl) ⟩ U ∨[ F ] (α $ i) ⊑⟨ ϕ _ (i , refl) ⟩ w ■
        η x (false , eq) = x ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ ⋁[ F ] α ⊑⟨ ⋁[ F ]-least _ _ rem ⟩ ⋁[ F ] ⁅ (U ∨[ F ] a) ∣ a ε α ⁆ ⊑⟨ ⋁[ F ]-least _ _ ϕ ⟩ w ■
          where
          rem : _
          rem y (j , eq) = y ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ α $ j ⊑⟨ ⋁[ F ]-upper _ _ (false , refl) ⟩ U ∨[ F ] (α $ j) ⊑⟨ ⋁[ F ]-upper _ _ (j , refl) ⟩ _ ■
```

## Complements

```agda
module Complements (F : Frame 𝓤 𝓥 𝓥) (spec : isSpectral F) (basis : hasBasis F) where

  open Definition F basis

  ¬“_” : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
  ¬“ U ” = U ==>_

  open DefnOfHeytingImplication F
  open HeytingImplicationProperties F

  open PosetReasoning (pos F)

  open import PatchFrame F hiding (𝟏)

  ¬“”-preserves-meets : (U V W : ∣ F ∣F)
                      → ¬“ U ” (V ⊓[ F ] W) ≡ ¬“ U ” V ⊓[ F ] ¬“ U ” W
  ¬“”-preserves-meets U V W =
    lemma₀ (==>-is-HI U (V ⊓[ F ] W)) (==>-is-HI U V) (==>-is-HI U W)

  ¬“”-inflationary : (U V : ∣ F ∣F) → [ V ⊑[ pos F ] ¬“ U ” V ]
  ¬“”-inflationary U V = π₁ (==>-is-HI U V V) (⊓[ F ]-lower₁ U V)

  ¬“”-idempotent : (U V : ∣ F ∣F) → [ ¬“ U ” (¬“ U ” V) ⊑[ pos F ] ¬“ U ” V ]
  ¬“”-idempotent U V = π₁ (==>-is-HI U V (¬“ U ” (¬“ U ” V))) nts
    where
    𝟏 : [ U ⊓[ F ] ¬“ U ” (¬“ U ” V) ⊑[ pos F ] (U ⊓[ F ] U) ⊓[ F ] ¬“ U ” (¬“ U ” V) ]
    𝟏 = cleft F _ (≡⇒⊑ (pos F) (sym (x∧x=x F U)))

    𝟐 : [ (U ⊓[ F ] U) ⊓[ F ] ¬“ U ” (¬“ U ” V) ⊑[ pos F ] U ⊓[ F ] (U ⊓[ F ] ¬“ U ” (¬“ U ” V)) ]
    𝟐 = ≡⇒⊑ (pos F) (⊓[ F ]-assoc _ _ _)

    𝟑 : [ U ⊓[ F ] (U ⊓[ F ] (U ==> ¬“ U ” V)) ⊑[ pos F ] (U ⊓[ F ] (¬“ U ” V)) ]
    𝟑 = cright F U (mp U (¬“ U ” V))

    nts : [ (glb-of F U (¬“ U ” (¬“ U ” V))) ⊑[ pos F ] V ]
    nts = U ⊓[ F ] ¬“ U ” (¬“ U ” V)               ⊑⟨ 𝟏      ⟩
          (U ⊓[ F ] U) ⊓[ F ] (¬“ U ” (¬“ U ” V))  ⊑⟨ 𝟐      ⟩
          U ⊓[ F ] (U ⊓[ F ] (¬“ U ” (¬“ U ” V)))  ⊑⟨ 𝟑      ⟩
          U ⊓[ F ] (U ==> V)                       ⊑⟨ mp U V ⟩
          V ■

  ¬‘_’ : ∣ F ∣F → Nucleus F
  ¬‘ U ’ = ¬“ U ”
         , ¬“”-preserves-meets U
         , ¬“”-inflationary U
         , ¬“”-idempotent U

  ¬‘_’-monotone : (U : ∣ F ∣F) → isMonotonic (pos F) (pos F) ¬“ U ”
  ¬‘_’-monotone U = mono F ¬‘ U ’

  open import WayBelow F hiding (⋁_)

  main-lemma : (U : ∣ F ∣F) → [ U ≪ U ] → (V W : ∣ F ∣F) → [ V ≪ V ]
             → [ V ⊑[ pos F ] (¬“ U ” W) ]
             → Σ[ V′ ∈ ∣ F ∣F ] [ V′ ≪ V′ ] × [ (V′ ⊑[ pos F ] W) ] × [ V ⊑[ pos F ] (U ==> V′) ]
  main-lemma U U-comp V W V-comp ϕ = V ⊓[ F ] U , ε , γ , δ
    where
    γ : [ V ⊓[ F ] U ⊑[ pos F ] W ]
    γ = V ⊓[ F ] U            ⊑⟨ cleft F U ϕ                      ⟩
        (U ==> W) ⊓[ F ] U    ⊑⟨ ≡⇒⊑ (pos F) (comm F (U ==> W) U) ⟩
        U ⊓[ F ] (U ==> W)    ⊑⟨ mp U W ⟩
        W                     ■

    δ : [ V ⊑[ pos F ] U ==> (V ⊓[ F ] U) ]
    δ = π₁ (==>-is-HI U (V ⊓[ F ] U) V) (≡⇒⊑ (pos F) (comm F U V))

    ε : [ (V ⊓[ F ] U) ≪ (V ⊓[ F ] U) ]
    ε = π₁ (π₁ spec) V U V-comp U-comp

  ¬“”-sc : (U : ∣ F ∣F) → [ U ≪ U ] → isScottCont (¬‘ U ’)
  ¬“”-sc U U-comp S S-dir =
    continuity-lemma F spec ¬“ U ” (¬‘_’-monotone U) (main-lemma U U-comp) S S-dir
```

```agda
  open OpenNuclei F

  openn : (U : ∣ F ∣F) → [ U ≪ U ] → ∣ Patch ∣F
  openn U U-comp = ¬‘ U ’ , ¬“”-sc U U-comp

  close : (U : ∣ F ∣F) → ∣ Patch ∣F
  close U = ʻ U ’ , ‘’-sc F U

  complement-thm : (U : ∣ F ∣F) (γ : [ U ≪ U ])
                 → complements Patch (openn U γ) (close U)
  complement-thm U γ = nts₀ , nts₁
    where
    open PosetReasoning (pos Patch) renaming (_⊑⟨_⟩_ to _⊑P⟨_⟩_; _■ to _■P)

    rem : (V : ∣ F ∣F) → [ (¬“ U ” V ⊓[ F ] “ U ” V) ⊑[ pos F ] π₀ (π₀ ⊥[ Patch ]) V ]
    rem V = subst (λ - → [ rel (pos F) (¬“ U ” V ⊓[ F ] “ U ” V) - ]) (sym (⊥-Patch-id V)) nts
      where
      fin′ : _
      fin′ W (true , eq) = W ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ (U ==> V) ⊓[ F ] U ⊑⟨ mp-op U V ⟩ V ■
      fin′ W (false , eq) = subst (λ - → [ - ⊑[ pos F ] V ]) eq (⊓[ F ]-lower₁ (U ==> V) V)

      fin : [ rel (pos F) (bin-join F (glb-of F (U ==> V) U) (glb-of F (U ==> V) V)) V ]
      fin = ⋁[ F ]-least ⁅ glb-of F (U ==> V) U , glb-of F (U ==> V) V ⁆ V fin′

      nts : [ ((¬“ U ” V) ⊓[ F ] (“ U ” V)) ⊑[ pos F ] V ]
      nts =
          (U ==> V) ⊓[ F ] (U ∨[ F ] V)                     ⊑⟨ ≡⇒⊑ (pos F) (bin-dist F (U ==> V) U V) ⟩
          ((U ==> V) ⊓[ F ] U) ∨[ F ] ((U ==> V) ⊓[ F ] V)  ⊑⟨ fin ⟩
          V                                                 ■


    nts₀ : (openn U γ) ⊓[ Patch ] (close U) ≡ ⊥[ Patch ]
    nts₀ = ⊑[ pos Patch ]-antisym _ _ rem (⊥[ Patch ]-bottom ((openn U γ) ⊓[ Patch ] (close U)))

    rem₁ : [ ⊤[ Patch ] ⊑[ pos Patch ] (openn U γ) ∨[ Patch ] (close U)  ]
    rem₁ V = ⊤[ F ]                                   ⊑⟨ δ ⟩
             U ==> (U ∨[ F ] V)                       ⊑⟨ ⋁[ F ]-upper _ _ (false ∷ true ∷ [] , refl) ⟩
             π₀ (π₀ (openn U γ ∨[ Patch ] close U)) V ■
      where
      δ : _
      δ = π₁ (==>-is-HI U (bin-join F U V) ⊤[ F ]) (U ⊓[ F ] ⊤[ F ] ⊑⟨ ⊓[ F ]-lower₀ U ⊤[ F ] ⟩ U ⊑⟨ ⋁[ F ]-upper _ _ (true , refl) ⟩ U ∨[ F ] V ■)

    nts₁ : (openn U γ) ∨[ Patch ] (close U) ≡ ⊤[ Patch ]
    nts₁ = ⊑[ pos Patch ]-antisym _ _ (⊤[ Patch ]-top ((openn U γ) ∨[ Patch ] (close U))) rem₁
```
