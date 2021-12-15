--
title: Closed Nuclei
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe --experimental-lossy-unification #-}

open import Basis renaming (_∨_ to _⊔_)
open import Frame

module ClosedNuclei where

open import Cubical.Data.List using (_∷_; []; List)
open import Poset
open import Nucleus
open import Prenucleus
open import HeytingImplication
open import Frame
open import Spectral
open import Regular
open import Stone
open import RightAdjoint hiding (hasBasis)
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
```

```agda
  “”-preserves-meets : (U V W : ∣ F ∣F) → “ U ” (V ⊓[ F ] W) ≡ “ U ” V ⊓[ F ] “ U ” W
  “”-preserves-meets U V W =
    “ U ” (V ⊓[ F ] W)               ≡⟨ refl ⟩
    U ∨[ F ] (V ⊓[ F ] W)            ≡⟨ bin-dist-op F U V W ⟩
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
isScottContinuous : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦′)
                  → (f : ∣ F ∣F → ∣ G ∣F)
                  → _ ̇
isScottContinuous F G f =
  (U : Fam _ ∣ F ∣F) →
    [ isDirected (pos F) U ] →
      [ isSup (pos G) ⁅ f x ∣ x ε U ⁆ (f (⋁[ F ] U)) ]

sc→mono : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦)
        → (f : ∣ F ∣F → ∣ G ∣F)
        → isScottContinuous F G f
        → isMonotonic (pos F) (pos G) f
sc→mono F G f sc x y p =
  f x              ⊑⟨ ⊔[ G ]-upper₀ (f x) (f y) ⟩
  f x ∨[ G ] f y   ⊑⟨ ≡⇒⊑ (pos G) (sym nts)     ⟩
  f y              ■
  where
  open PosetReasoning (pos G)

  S : Fam 𝓦′ ∣ F ∣F
  S = ⁅ x , y ⁆

  S-dir : [ isDirected (pos F) S ]
  π₀ S-dir             = ∣ true ∣
  π₁ S-dir true  true  = ∣ true  , ((⊑[ pos F ]-refl _) , ⊑[ pos F ]-refl _) ∣
  π₁ S-dir false true  = ∣ false , (⊑[ pos F ]-refl _ , p) ∣
  π₁ S-dir true  false = ∣ false , p , (⊑[ pos F ]-refl _) ∣
  π₁ S-dir false false = ∣ false , ((⊑[ pos F ]-refl _) , ⊑[ pos F ]-refl _) ∣

  nts : f y ≡ f x ∨[ G ] f y
  nts = f y                    ≡⟨ cong f (x⊑y⇒y=x∨y F p)                         ⟩
        f (⋁[ F ] ⁅ x , y ⁆)   ≡⟨ ⦅𝟐⦆                                            ⟩
        ⋁[ G ] (f ⟨$⟩ S)       ≡⟨ cong (λ - → ⋁[ G ] (index S , -)) (funExt ⦅𝟑⦆) ⟩
        (⋁[ G ] ⁅ f x , f y ⁆) ∎
    where
    ⦅𝟐⦆ : _
    ⦅𝟐⦆ = ⋁-unique G _ _ (π₀ (sc S S-dir)) (π₁ (sc S S-dir))

    ⦅𝟑⦆ : _
    ⦅𝟑⦆ true  = refl
    ⦅𝟑⦆ false = refl

module _ (F : Frame 𝓤 𝓥 𝓦) where

  open OpenNuclei F
  open import PatchFrame F

  ‘’-sc : (U : ∣ F ∣F) → isScottCont ʻ U ’
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
        η x (true , eq) =
          x                ⊑⟨ ≡⇒⊑ (pos F) (sym eq)           ⟩
          U                ⊑⟨ ⋁[ F ]-upper _ _ (true , refl) ⟩
          U ∨[ F ] (α $ i) ⊑⟨ ϕ _ (i , refl)                 ⟩
          w                ■
        η x (false , eq) =
          x                               ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩
          ⋁[ F ] α                        ⊑⟨ ⋁[ F ]-least _ _ rem ⟩
          ⋁[ F ] ⁅ (U ∨[ F ] a) ∣ a ε α ⁆ ⊑⟨ ⋁[ F ]-least _ _ ϕ   ⟩
          w                               ■
          where
          rem : _
          rem y (j , eq) =
            y                ⊑⟨ ≡⇒⊑ (pos F) (sym eq)            ⟩
            α $ j            ⊑⟨ ⋁[ F ]-upper _ _ (false , refl) ⟩
            U ∨[ F ] (α $ j) ⊑⟨ ⋁[ F ]-upper _ _ (j , refl)     ⟩
            _ ■

  εε : ∣ F ∣F → ∣ Patch ∣F
  εε U = ʻ U ’ , ‘’-sc U

  εε-resp-⊤ : εε ⊤[ F ] ≡ ⊤[ Patch ]
  εε-resp-⊤ = ⊑[_]-antisym (pos Patch) _ _ (⊤[ Patch ]-top (εε ⊤[ F ])) goal
    where
    open PosetReasoning (pos F)

    goal : [ ⊤[ Patch ] ⊑[ pos Patch ] εε ⊤[ F ] ]
    goal x = π₀ (π₀ ⊤[ Patch ]) x ⊑⟨ ⊤[ F ]-top _           ⟩
             ⊤[ F ]               ⊑⟨ ⊔[ F ]-upper₀ ⊤[ F ] x ⟩
             ⊤[ F ] ∨[ F ] x      ■

  εε-resp-∧ : (x y : ∣ F ∣F) → εε (x ⊓[ F ] y) ≡ εε x ⊓[ Patch ] εε y
  εε-resp-∧ x y = Σ≡Prop isScottCont-prop (Σ≡Prop (isNuclear-prop F) (funExt nts))
    where
    nts : (z : ∣ F ∣F) → εε (glb-of F x y) .π₀ .π₀ z ≡ glb-of Patch (εε x) (εε y) .π₀ .π₀ z
    nts z = εε (glb-of F x y) .π₀ .π₀ z          ≡⟨ refl                                              ⟩
            (x ⊓[ F ] y) ∨[ F ] z                ≡⟨ ∨-comm F (x ⊓[ F ] y) z                           ⟩
            z ∨[ F ] (x ⊓[ F ] y)                ≡⟨ bin-dist-op F z x y                               ⟩
            (z ∨[ F ] x) ⊓[ F ] (z ∨[ F ] y)     ≡⟨ cong (λ - → - ⊓[ F ] (z ∨[ F ] y)) (∨-comm F z x) ⟩
            (x ∨[ F ] z) ⊓[ F ] (z ∨[ F ] y)     ≡⟨ cong (λ - → (x ∨[ F ] z) ⊓[ F ] -) (∨-comm F z y) ⟩
            (x ∨[ F ] z) ⊓[ F ] (y ∨[ F ] z)     ≡⟨ refl                                              ⟩
            ((εε x) ⊓[ Patch ] (εε y)) .π₀ .π₀ z ∎

  εε-resp-⋁ : (U : Fam 𝓦 ∣ F ∣F) → εε (⋁[ F ] U) ≡ (⋁[ Patch ] ⁅ εε u ∣ u ε U ⁆)
  εε-resp-⋁ U = ⋁-unique Patch _ _ β γ
    where
    open PosetReasoning (pos F) using (_⊑⟨_⟩_; _■)

    β : [ ∀[ V ε ⁅ εε x ∣ x ε U ⁆ ] (V ⊑[ pos Patch ] εε (⋁[ F ] U)) ]
    β ((j , _) , _) (i , eq) = subst (λ - → [ - ⊑[ pos Patch ] (εε (⋁[ F ] U)) ]) eq rem₀
      where
      rem₀ : [ (π₁ (⁅ εε x ∣ x ε U ⁆) i) ⊑[ pos Patch ] (εε (⋁[ F ] U)) ]
      rem₀ W = (U $ i) ∨[ F ] W ⊑⟨ ⋁[ F ]-least _ _ γ ⟩ (⋁[ F ] U) ∨[ F ] W ■
        where
        γ : _
        γ x (true  , eq) = x ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ U $ i ⊑⟨ ⋁[ F ]-upper _ _ (i , refl) ⟩ ⋁[ F ] U ⊑⟨ ⊔[ F ]-upper₀ _ _ ⟩ (⋁[ F ] U) ∨[ F ] W ■
        γ x (false , eq) = x ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ W ⊑⟨ ⊔[ F ]-upper₁ _ _ ⟩ _ ■

    γ : (j : ∣ pos Patch ∣ₚ)
         → [ ∀[ V ε (fmap εε U) ] (V ⊑[ pos Patch ] j) ]
         → [ εε (⋁[ F ] U) ⊑[ pos Patch ] j ]
    γ 𝕛@(𝒿@(j , _) , _) ϕ T = ⋁[ F ]-least _ _ rem₁
      where
      rem₁ : _
      rem₁ S (true , eq) = subst (λ - → [ - ⊑[ pos F ] j T ]) eq (⋁[ F ]-least _ _ δ)
        where
        δ : _
        δ Z (i , eq) =
          subst (λ - → [ - ⊑[ pos F ] j T ]) eq
            (U $ i ⊑⟨ ⊔[ F ]-upper₀ _ _ ⟩ (U $ i) ∨[ F ] T ⊑⟨ ϕ (εε (U $ i)) (i , refl) T ⟩ j T ■)
      rem₁ S (false , eq) = subst (λ - → [ - ⊑[ pos F ] j T ]) eq (𝓃₁ F 𝒿 T)

  εε-resp-∨ : (x y : ∣ F ∣F) → εε (x ∨[ F ] y) ≡ (εε x) ∨[ Patch ] (εε y)
  εε-resp-∨ x y = εε (x ∨[ F ] y)                ≡⟨ εε-resp-⋁ ⁅ x , y ⁆                         ⟩
                  ⋁[ Patch ] (εε ⟨$⟩ ⁅ x , y ⁆)  ≡⟨ cong (λ - → ⋁[ Patch ] -) (⁅⁆-distr x y εε) ⟩
                  (εε x) ∨[ Patch ] (εε y)       ∎

  εε-mono : isMonotonic (pos F) (pos Patch) εε
  εε-mono x y x≤y z = ⋁[ F ]-least _ _ γ
    where
    open PosetReasoning (pos F) using (_⊑⟨_⟩_; _■)

    γ : _
    γ w (true  , eq) = w          ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩
                        x          ⊑⟨ x≤y ⟩
                        y          ⊑⟨ ⋁[ F ]-upper _ _ (true , refl) ⟩
                        y ∨[ F ] z ■
    γ w (false , eq) = w          ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩
                        z          ⊑⟨ ⋁[ F ]-upper _ _ (false , refl) ⟩
                        y ∨[ F ] z ■

  εεε : F ─f→ Patch
  εεε = (εε , εε-mono) , εε-resp-⊤ , (εε-resp-∧ , εε-resp-⋁)

  εε-sc : isScottContinuous F Patch εε
  εε-sc U _ = nts₀ , nts₁
    where
    open PosetReasoning (pos F) using (_⊑⟨_⟩_; _■)

    nts₀ : [ ∀[ V ε ⁅ εε x ∣ x ε U ⁆ ] (V ⊑[ pos Patch ] εε (⋁[ F ] U)) ]
    nts₀ ((j , _) , _) (i , eq) = subst (λ - → [ - ⊑[ pos Patch ] (εε (⋁[ F ] U)) ]) eq rem₀
      where
      rem₀ : [ (π₁ (⁅ εε x ∣ x ε U ⁆) i) ⊑[ pos Patch ] (εε (⋁[ F ] U)) ]
      rem₀ W = (U $ i) ∨[ F ] W ⊑⟨ ⋁[ F ]-least _ _ γ ⟩ (⋁[ F ] U) ∨[ F ] W ■
        where
        γ : _
        γ x (true  , eq) = x ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ U $ i ⊑⟨ ⋁[ F ]-upper _ _ (i , refl) ⟩ ⋁[ F ] U ⊑⟨ ⊔[ F ]-upper₀ _ _ ⟩ (⋁[ F ] U) ∨[ F ] W ■
        γ x (false , eq) = x ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ W ⊑⟨ ⊔[ F ]-upper₁ _ _ ⟩ _ ■

    nts₁ : (j : ∣ pos Patch ∣ₚ)
         → [ ∀[ V ε (fmap εε U) ] (V ⊑[ pos Patch ] j) ]
         → [ εε (⋁[ F ] U) ⊑[ pos Patch ] j ]
    nts₁ 𝕛@(𝒿@(j , _) , _) ϕ T = ⋁[ F ]-least _ _ rem₁
      where
      rem₁ : _
      rem₁ S (true , eq) = subst (λ - → [ - ⊑[ pos F ] j T ]) eq (⋁[ F ]-least _ _ γ)
        where
        γ : _
        γ Z (i , eq) =
          subst (λ - → [ - ⊑[ pos F ] j T ]) eq
            (U $ i ⊑⟨ ⊔[ F ]-upper₀ _ _ ⟩ (U $ i) ∨[ F ] T ⊑⟨ ϕ (εε (U $ i)) (i , refl) T ⟩ j T ■)
      rem₁ S (false , eq) = subst (λ - → [ - ⊑[ pos F ] j T ]) eq (𝓃₁ F 𝒿 T)
```

## Complements

```agda
module Complements (F : Frame 𝓤 𝓥 𝓥) (spec : isSpectral′ F) (basis : hasBasis F) where

  open Definition F basis
  open import WayBelow F
  open import PatchFrame F hiding (𝟏)

  ¬“_” : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
  ¬“ U ” = U ==>_

  open DefnOfHeytingImplication F
  open HeytingImplicationProperties F

  open PosetReasoning (pos F)

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

  main-lemma : (U : ∣ F ∣F) → [ U ≪ U ] → (V W : ∣ F ∣F) → [ V ≪ V ]
             → [ V ⊑[ pos F ] (¬“ U ” W) ]
             → Σ[ V′ ∈ ∣ F ∣F ] [ V′ ≪ V′ ] × [ (V′ ⊑[ pos F ] W) ] × [ V ⊑[ pos F ] (¬“ U ” V′) ]
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
    ε = spec→compacts-closed-under-∧ F spec V U V-comp U-comp

  ¬“”-sc : (U : ∣ F ∣F) → [ U ≪ U ] → isScottCont (¬‘ U ’)
  ¬“”-sc U U-comp S S-dir =
    continuity-lemma F spec ¬“ U ” (¬‘_’-monotone U) (main-lemma U U-comp) S S-dir

  μ : (x : ∣ F ∣F) → [ x ≪ x ] → ∣ Patch ∣F
  μ x p = ¬‘ x ’ , ¬“”-sc x p
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

    abstract
      rem : (V : ∣ F ∣F) → [ (¬“ U ” V ⊓[ F ] “ U ” V) ⊑[ pos F ] π₀ (π₀ ⊥[ Patch ]) V ]
      rem V = subst (λ - → [ rel (pos F) (¬“ U ” V ⊓[ F ] “ U ” V) - ]) (sym (⊥-Patch-id V)) nts
        where
        ℱ : Fam 𝓥 ∣ F ∣F
        ℱ = Bool 𝓥 , λ b → if b then (U ==> V) ⊓[ F ] U else ((U ==> V) ⊓[ F ] V)

        fin′ : (W : ∣ F ∣F) → W ε ℱ → [ W ⊑[ pos F ] V ]
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
        δ : [ ⊤[ F ] ⊑[ pos F ] (U ==> (U ∨[ F ] V)) ]
        δ = π₁ (==>-is-HI U (bin-join F U V) ⊤[ F ]) (U ⊓[ F ] ⊤[ F ] ⊑⟨ ⊓[ F ]-lower₀ U ⊤[ F ] ⟩ U ⊑⟨ ⋁[ F ]-upper _ _ (true , refl) ⟩ U ∨[ F ] V ■)

      nts₁ : (openn U γ) ∨[ Patch ] (close U) ≡ ⊤[ Patch ]
      nts₁ = ⊑[ pos Patch ]-antisym _ _ (⊤[ Patch ]-top ((openn U γ) ∨[ Patch ] (close U))) rem₁

  complement-thm′ : (x : ∣ F ∣F) → (κ : [ x ≪ x ]) → complements Patch (close x) (openn x κ)
  complement-thm′ x κ = G𝟏 , G𝟐
    where
    G𝟏 : close x ⊓[ Patch ] openn x κ ≡ ⊥[ Patch ]
    G𝟏 = close x ⊓[ Patch ] openn x κ   ≡⟨ comm Patch (close x) (openn x κ)  ⟩
         openn x κ ⊓[ Patch ] close x   ≡⟨ π₀ (complement-thm x κ)           ⟩
         ⊥[ Patch ]                     ∎

    G𝟐 : close x ∨[ Patch ] openn x κ ≡ ⊤[ Patch ]
    G𝟐 = close x ∨[ Patch ] openn x κ   ≡⟨ ∨-comm Patch (close x) (openn x κ)  ⟩
         openn x κ ∨[ Patch ] close x   ≡⟨ π₁ (complement-thm x κ)             ⟩
         ⊤[ Patch ]                     ∎
```

```agda
module PerfectMap (F : Frame 𝓤 𝓥 𝓥) (G : Frame 𝓤′ 𝓥 𝓥) (basis : hasBasis F) where

  open AdjointFunctorTheorem F G basis
  open import WayBelow

  -- Perfection!
  isPerfect : (f : F ─f→ G) → (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓤′) ̇
  isPerfect (f , _ , (_ , p)) = isScottContinuous G F  (_^* f (sym ∘ p))

  perfection-lemma : (f : F ─f→ G)
                   → isPerfect f
                   → {x y : ∣ F ∣F}
                   → [ _≪_ F x y ]
                   → [ _≪_ G (π₀ (π₀ f) x)  ((π₀ (π₀ f)) y) ]
  perfection-lemma (f , _ , (_ , p)) f-perf {x = x} {y} x≪y S S-dir ϕ =
    ∥∥-rec (∥∥-prop _) goal nts
    where
    S′-dir : [ isDirected (pos F) ⁅ (_^* f (sym ∘ p)) s ∣  s ε S ⁆ ]
    S′-dir = directed-image-lemma (pos G) (pos F) (_^*ᴹ f (sym ∘ p)) S S-dir

    𝟏 : [ rel (pos F) ((_^* f (sym ∘ p)) (⋁[ G ] S)) (⋁[ F ] ((_^* f (sym ∘ p)) ⟨$⟩ S)) ]
    𝟏 = ≡⇒⊑ (pos F) (⋁-unique F _ _ β γ)
      where
      β : _
      β = π₀ (f-perf S S-dir)

      γ : _
      γ = π₁ (f-perf S S-dir)

    rem : [ y ⊑[ pos F ] ⋁[ F ] ((_^* f (sym ∘ p)) ⟨$⟩ S) ]
    rem = y                             ⊑⟨ π₀ (^*-RA f (sym ∘ p) y (⋁[ G ] S)) ϕ ⟩
          (_^* f (sym ∘ p)) (⋁[ G ] S)  ⊑⟨ 𝟏                           ⟩
          ⋁[ F ] ((_^* f (sym ∘ p)) ⟨$⟩ S)         ■
      where
      open PosetReasoning (pos F)

    goal : Σ[ i ∈ index S ] [ x ⊑[ pos F ] (((_^* f (sym ∘ p)) ⟨$⟩ S) $ i) ]
         → ∥ Σ[ i ∈ index S ] [ (G ≤ π₀ f _) (S $ i) ] ∥
    goal (i , q) = ∣ i , rem′ ∣
      where
      rem′ : [ π₀ f x ⊑[ pos G ] (S $ i) ]
      rem′ = π₁ (^*-RA f (sym ∘ p) x (S $ i)) q

    nts : [ ∥ Σ[ i ∈ index S ] [ x ⊑[ pos F ] (_^* f (sym ∘ p)) (S $ i) ] ∥Ω ]
    nts = x≪y ((_^* f (sym ∘ p)) ⟨$⟩ S) S′-dir rem

```

```agda
module CompactnessLemma (F : Frame 𝓤 𝓥 𝓥) (G : Frame 𝓤′ 𝓥 𝓥) (basis : hasBasis F) where

  open PerfectMap F G basis
  open import WayBelow

  compactness-lemma : (f : F ─f→ G)
                    → isPerfect f
                    → [ isCompact F ]
                    → [ isCompact G ]
  compactness-lemma 𝒻@((f , _) , (p , _)) f-perf F-compact =
    subst (λ - → [ _≪_ G - - ]) p (perfection-lemma 𝒻 f-perf F-compact)
```

```agda
module SomeMoreResults (F : Frame (𝓤 ⁺) 𝓤 𝓤) (spec′ : isSpectral′ F) (basis : hasBasis F) where

  open OpenNuclei F

  open import WayBelow
  open import PatchFrame

  private
    ℬ : Fam 𝓤 ∣ F ∣F
    ℬ = π₀ basis

  _⊑s_ : ScottContNucleus F → ScottContNucleus F → hProp 𝓤
  ((j , _) , _) ⊑s ((k , _) , _) = ∀[ i ∶ index ℬ ] j (ℬ $ i) ⊑[ pos F ] k (ℬ $ i)

  ⊑patch↔⊑s : (𝒿 𝓀 : ScottContNucleus F) → [ 𝒿 ⊑[ pos (Patch F) ] 𝓀 ] ↔ [ 𝒿 ⊑s 𝓀 ]
  ⊑patch↔⊑s 𝒿@((j , _) , j-sc) 𝓀@((k , _) , k-sc) = β , γ
    where
    -- Trivial direction.
    β : [ 𝒿 ⊑[ pos (Patch F) ] 𝓀 ] → [ 𝒿 ⊑s 𝓀 ]
    β j≤k i = j≤k (ℬ $ i)

    open PosetReasoning (pos F)

    γ : [ 𝒿 ⊑s 𝓀 ] → [ 𝒿 ⊑[ pos (Patch F) ] 𝓀 ]
    γ j≤k x =
      j x                           ⊑⟨ ≡⇒⊑ (pos F) (cong j eq)        ⟩
      j (⋁[ F ] ⁅ ℬ $ i ∣ i ε ℐ ⁆)  ⊑⟨ ≡⇒⊑ (pos F) (j-sc _ dir)       ⟩
      ⋁[ F ] ⁅ j (ℬ $ i) ∣ i ε ℐ ⁆  ⊑⟨ ⋁[ F ]-least _ _ nts           ⟩
      ⋁[ F ] ⁅ k (ℬ $ i) ∣ i ε ℐ ⁆  ⊑⟨ ≡⇒⊑ (pos F) (sym (k-sc _ dir)) ⟩
      k (⋁[ F ] ⁅ ℬ $ i ∣ i ε ℐ ⁆)  ⊑⟨ ≡⇒⊑ (pos F) (cong k (sym eq))  ⟩
      k x ■
      where
      ℐ : Fam 𝓤 (index ℬ)
      ℐ = π₀ (π₁ basis x)

      p : _
      p = π₀ (π₁ (π₁ (π₁ basis x)))

      q : _
      q = π₁ (π₁ (π₁ (π₁ basis x)))

      dir : [ isDirected (pos F) ⁅ ℬ $ j ∣ j ε ℐ ⁆ ]
      dir = π₀ (π₁ (π₁ basis x))

      eq : x ≡ ⋁[ F ] ⁅ ℬ $ i ∣ i ε ℐ ⁆
      eq = ⋁-unique F _ _ p q

      nts : [ ∀[ y ε ⁅ j (ℬ $ i) ∣ i ε ℐ ⁆ ] (y ⊑[ pos F ] ⋁[ F ] ⁅ k (ℬ $ i) ∣ i ε ℐ ⁆) ]
      nts y (l , eq) = subst (λ - → [ - ⊑[ pos F ] (⋁[ F ] _) ]) eq rem
        where
        rem : [ (π₁ (fmap (λ i → j (ℬ $ i)) ℐ) l) ⊑[ pos F ] (⋁[ F ] (index ℐ , (λ x₁ → k (ℬ $ ℐ $ x₁)))) ]
        rem = j (ℬ $ (ℐ $ l)) ⊑⟨ j≤k (ℐ $ l) ⟩ k (ℬ $ (ℐ $ l)) ⊑⟨ ⋁[ F ]-upper _ _ (l , refl) ⟩ _ ■

  ⊑s-refl : [ isReflexive _⊑s_ ]
  ⊑s-refl x = π₀ (⊑patch↔⊑s x x) (⊑[ pos (Patch F) ]-refl x)

  ⊑s-trans : [ isTransitive _⊑s_ ]
  ⊑s-trans x y z x≤y y≤z =
    π₀ (⊑patch↔⊑s x z) (⊑[ pos (Patch F) ]-trans x y z (π₁ (⊑patch↔⊑s x y) x≤y) (π₁ (⊑patch↔⊑s y z) y≤z))

  ⊑s-antisym : [ isAntisym (carrier-is-set (pos (Patch F))) _⊑s_ ]
  ⊑s-antisym x y x≤y y≤x =
    ⊑[ pos (Patch F) ]-antisym x y (π₁ (⊑patch↔⊑s x y) x≤y) (π₁ (⊑patch↔⊑s y x) y≤x)
```

We define a new version of the patch frame using the `⊑s` relation

```agda
  Patch′-pos : Poset (𝓤 ⁺) 𝓤
  Patch′-pos = ∣ Patch F ∣F , _⊑s_
             , carrier-is-set (pos (Patch F))
             , ⊑s-refl , ⊑s-trans , ⊑s-antisym

  Patch′ : Frame (𝓤 ⁺) 𝓤 𝓤
  Patch′ = ∣ Patch F ∣F
         , ((strₚ Patch′-pos , ⊤[ Patch F ] , (glb-of (Patch F) , ⋁[ Patch F ]_)) , nts)
    where
    nts₀ : [ isTop Patch′-pos ⊤[ Patch F ] ]
    nts₀ x = π₀ (⊑patch↔⊑s x ⊤[ Patch F ]) (⊤[ Patch F ]-top x)

    nts₁ : [ isGLB Patch′-pos (glb-of (Patch F)) ]
    nts₁ = (λ 𝒿 𝓀 → π₀ (⊑patch↔⊑s (𝒿 ⊓[ Patch F ] 𝓀) 𝒿) (⊓[ Patch F ]-lower₀ 𝒿 𝓀) , π₀ (⊑patch↔⊑s (𝒿 ⊓[ Patch F ] 𝓀) 𝓀) (⊓[ Patch F ]-lower₁ 𝒿 𝓀))
         , λ 𝒾 𝒿 𝓀 p → π₀ (⊑patch↔⊑s 𝓀 (𝒾 ⊓[ Patch F ] 𝒿)) (⊓[ Patch F ]-greatest 𝒾 𝒿 𝓀 (π₁ (⊑patch↔⊑s 𝓀 𝒾) (π₀ p)) (π₁ (⊑patch↔⊑s 𝓀 𝒿) (π₁ p)))

    nts₂ : [ isLUB Patch′-pos (⋁[ Patch F ]_) ]
    nts₂ = nts₂-0 , nts₂-1
      where
      nts₂-0 : (U : Fam 𝓤 ∣ Patch F ∣F) (𝒿 : ∣ Patch F ∣F)→ 𝒿 ε U → [ 𝒿 ⊑s (⋁[ Patch F ] U) ]
      nts₂-0 U 𝒿 𝒿εU = π₀ (⊑patch↔⊑s 𝒿 (⋁[ Patch F ] U)) (⋁[ Patch F ]-upper U 𝒿 𝒿εU)

      nts₂-1 : (U : Fam 𝓤 ∣ Patch F ∣F) (𝓀 : ∣ Patch F ∣F)
             → ((𝒿 : ∣ Patch F ∣F) → 𝒿 ε U → [ 𝒿 ⊑s 𝓀 ])
             → [ (⋁[ Patch F ] U) ⊑s 𝓀 ]
      nts₂-1 U 𝓀 ϕ = π₀ (⊑patch↔⊑s (⋁[ Patch F ] U) 𝓀) (⋁[ Patch F ]-least U 𝓀 (λ 𝒾 p → π₁ (⊑patch↔⊑s 𝒾 𝓀) (ϕ 𝒾 p)))

    nts : _
    nts = nts₀ , nts₁ , nts₂ , dist (Patch F)

  ≪patch↔≪s : (𝒿 𝓀 : ScottContNucleus F) → [ _≪_ Patch′ 𝒿 𝓀 ] → [ _≪_ (Patch F) 𝒿 𝓀 ]
  ≪patch↔≪s 𝒿 𝓀 𝒿≪𝓀 S S-dir p =
    ∥∥-rec
      (isProp[] ∥ (Σ[ i ∈ index S ] [ 𝒿 ⊑[ pos (Patch F ) ] (S $ i) ]) ∥Ω)
      nts
      (𝒿≪𝓀 S S-dir′ q )
    where
    S-dir′ : [ isDirected (pos Patch′) S ]
    π₀ S-dir′     = π₀ S-dir
    π₁ S-dir′ i j = ∥∥-rec (∥∥-prop _) rem (π₁ S-dir i j)
      where
      rem : _
      rem (k , i≤k , j≤k) = ∣ k , π₀ (⊑patch↔⊑s (S $ i) (S $ k)) i≤k , π₀ (⊑patch↔⊑s (S $ j) (S $ k)) j≤k ∣

    q : [ 𝓀 ⊑[ pos Patch′ ] (⋁[ Patch′ ] S) ]
    q = π₀ (⊑patch↔⊑s 𝓀 (⋁[ Patch′ ] S)) p

    nts : Σ[ i ∈ index S ] [ 𝒿 ⊑[ pos Patch′ ] (S $ i) ]
        → [ ∥ Σ[ i ∈ index S ] [ 𝒿 ⊑[ pos (Patch F) ] (S $ i) ] ∥Ω ]
    nts (i , φ) = ∣ i , (π₁ (⊑patch↔⊑s 𝒿 (S $ i)) φ) ∣
```

We now prove that `Patch` and `Patch′` are equivalent

```agda
  equiv : Patch F ≅f Patch′
  equiv = ((id ∣ Patch F ∣F , μ) , ρ) , ((id ∣ Patch F ∣F , μ′) , ρ′) , sec , ret
    where
    μ : isMonotonic (pos (Patch F)) (pos Patch′) (id ∣ Patch F ∣F)
    μ x y p i = p (ℬ $ i)

    ρ : isFrameHomomorphism (Patch F) Patch′ (id ∣ Patch F ∣F , μ)
    ρ = refl , ((λ _ _ → refl) , (λ _ → refl))

    μ′ : isMonotonic (pos Patch′) (pos (Patch F)) (id ∣ Patch F ∣F)
    μ′ 𝒿 𝓀 ϕ z = π₁ (⊑patch↔⊑s 𝒿 𝓀) ϕ z

    ρ′ : isFrameHomomorphism Patch′ (Patch F) (id ∣ Patch F ∣F , μ′)
    ρ′ = refl , ((λ _ _ → refl) , λ _ → refl)

    sec : section (id ∣ Patch F ∣F) (id ∣ Patch F ∣F)
    sec _ = refl

    ret : retract (id ∣ Patch F ∣F) (id ∣ Patch F ∣F)
    ret _ = refl
```

```agda
  open AdjointFunctorTheorem F Patch′ basis

  δδ-mono : isMonotonic (pos F) (pos Patch′) (εε F)
  δδ-mono x y p = π₀ (⊑patch↔⊑s (εε F x) (εε F y)) (εε-mono F x y p)

  δδδ : F ─f→ Patch′
  δδδ = (εε F , μ)
      , εε-resp-⊤ F
      , (εε-resp-∧ F , εε-resp-⋁ F)
    where
    μ : isMonotonic (pos F) (pos Patch′) (εε F)
    μ x y p = π₀ (⊑patch↔⊑s (εε F x) (εε F y)) (εε-mono F x y p)

  δ* : ∣ Patch′ ∣F → ∣ F ∣F
  δ* = π₀ (_^*ᴹ (π₀ δδδ) (sym ∘ εε-resp-⋁ F))

  δ*-mono : isMonotonic (pos Patch′) (pos F) δ*
  δ*-mono = π₁ (_^*ᴹ (π₀ δδδ) (sym ∘ εε-resp-⋁ F))

  open GaloisConnection (pos F) (pos Patch′)

  ζ : ∣ Patch F ∣F → ∣ F ∣F
  ζ ((j , _) , _) = j ⊥[ F ]

  ζ-mono : isMonotonic (pos Patch′) (pos F) ζ
  ζ-mono 𝒿@((j , _) , _) 𝓀@((k , _) , _) p =
    j ⊥[ F ] ⊑⟨ π₁ (⊑patch↔⊑s 𝒿 𝓀) p ⊥[ F ] ⟩ k ⊥[ F ] ■
    where
    open PosetReasoning (pos F)

  ζζ : pos Patch′ ─m→ pos F
  ζζ = ζ , ζ-mono

  δ⊣ζ : [ π₀ δδδ ⊣ ζζ ]
  δ⊣ζ x 𝒿@((j , 𝓃₀ , 𝓃₁ , 𝓃₂) , _) = G𝟏 , G𝟐
    where
    open PosetReasoning (pos F)

    G𝟏 : [ (π₀ δδδ $ₘ x) ⊑[ pos Patch′ ] 𝒿 ⇒ x ⊑[ pos F ] (ζζ $ₘ 𝒿) ]
    G𝟏 p = x               ⊑⟨ ⋁[ F ]-upper _ _ (true , refl) ⟩
           x ∨[ F ] ⊥[ F ] ⊑⟨ π₁ (⊑patch↔⊑s (εε F x) 𝒿) p ⊥[ F ] ⟩
           j ⊥[ F ]        ■

    G𝟐 : [ x ⊑[ pos F ] (ζζ $ₘ 𝒿) ⇒ (π₀ δδδ $ₘ x) ⊑[ pos Patch′ ] 𝒿 ]
    G𝟐 p y = π₀ (⊑patch↔⊑s (εε F x) 𝒿) G𝟐a y
      where
      G𝟐a : [ εε F x ⊑[ pos (Patch F) ] 𝒿 ]
      G𝟐a z = ⋁[ F ]-least _ _ G𝟐b
        where
        † : [ j ⊥[ F ] ⊑[ pos F ] j z ]
        † = mono F (π₀ 𝒿) ⊥[ F ] z (⊥[ F ]-bottom z)

        G𝟐b : [ ∀[ w ε ⁅ x , z ⁆ ] (w ⊑[ pos F ] j z) ]
        G𝟐b w (true  , eq) = w ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ x ⊑⟨ p ⟩ j ⊥[ F ] ⊑⟨ † ⟩ j z ■
        G𝟐b w (false , eq) = w ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩ z ⊑⟨ 𝓃₁ z ⟩ j z ■

  𝟎-lemma : (𝒿 : ∣ Patch F ∣F) → δ* 𝒿 ≡ ζ 𝒿
  𝟎-lemma 𝒿@(jm , p) =
    funExt⁻
      (π₀ (PathΣ→ΣPathTransport _ _ (⊣-unique-right (π₀ δδδ) (δ* , δ*-mono) ζζ G𝟏 δ⊣ζ))) 𝒿
    where
    G𝟏 : [ π₀ δδδ ⊣ (δ* , δ*-mono) ]
    G𝟏 = ^*-RA (π₀ δδδ) (sym ∘ π₁ (π₁ (π₁ δδδ)))

  δδδ-lemma : (J : Fam 𝓤 ∣ Patch F ∣F) → [ isDirected (pos (Patch F)) J ]
            → δ* (⋁[ Patch′ ] J) ≡ ⋁[ F ] ⁅ δ* j ∣ j ε J ⁆
  δδδ-lemma J J-dir =
    δ* (⋁[ Patch′ ] J)                  ≡⟨ 𝟎-lemma (⋁[ Patch′ ] J)                      ⟩
    π₀ (π₀ (⋁[ Patch′ ] J)) ⊥[ F ]      ≡⟨ directed-computed-pointwise F J J-dir ⊥[ F ] ⟩
    ⋁[ F ] ⁅ π₀ (π₀ j) ⊥[ F ] ∣ j ε J ⁆ ≡⟨ ⦅𝟏⦆                                          ⟩
    ⋁[ F ] ⁅ δ* j ∣ j ε J ⁆             ∎
    where
    ⦅𝟏⦆ = cong (λ - → ⋁[ F ] (index J , -)) (sym (funExt (λ i → 𝟎-lemma (J $ i))))

  δδδ-perfect : PerfectMap.isPerfect F Patch′ basis δδδ
  δδδ-perfect J dir =
    subst (λ - → [ isSup (pos F) ⁅ δ* j ∣ j ε J ⁆ - ]) (sym (δδδ-lemma J G𝟏)) dir′
    where
    dir′ : [ isSup (pos F) (fmap δ* J) (⋁[ F ] fmap δ* J) ]
    dir′ = ⋁[ F ]-upper (fmap δ* J) , ⋁[ F ]-least (fmap δ* J)

    G𝟏 : [ isDirected (pos (Patch F)) J ]
    π₀ G𝟏 = π₀ dir
    π₁ G𝟏 i j = ∥∥-rec (∥∥-prop Ψ) G𝟏a (π₁ dir i j)
      where
      Ψ : Type (𝓤 ⁺)
      Ψ = Σ[ k ∈ index J ] [ (J $ i) ⊑[ pos (Patch F) ] (J $ k) ]
                         × [ (J $ j) ⊑[ pos (Patch F) ] (J $ k) ]

      Θ : Type 𝓤
      Θ = Σ[ k ∈ index J ] [ (J $ i) ⊑[ pos Patch′ ] (J $ k) ]
                         × [ (J $ j) ⊑[ pos Patch′ ] (J $ k) ]

      G𝟏a : Θ → ∥ Ψ ∥
      G𝟏a (k , p , q) =
        ∣ k , π₁ (⊑patch↔⊑s (J $ i) (J $ k)) p  , π₁ (⊑patch↔⊑s (J $ j) (J $ k)) q ∣
```

```agda
  -- sc-lemma : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦′)
  --          → (f : ∣ F ∣F → ∣ G ∣F)
  --          → isScottContinuous F G f
  --          → (x : ∣ F ∣F) (y : ∣ G ∣F)
  --          → [ _≪_ G y (f x) ] ↔ (Σ[ w ∈ ∣ F ∣F ] [ _≪_ G y (f w) ])
  -- sc-lemma F G f sc x y = forward , backward
  --   where
  --   forward : [ _≪_ G y (f x) ] → Σ[ w ∈ ∣ F ∣F ] [ _≪_ G y (f w) ]
  --   forward y≪fx = x , {!!}

  --   backward : Σ[ w ∈ ∣ F ∣F ] [ _≪_ G y (f w) ] → [ _≪_ G y (f x) ]
  --   backward (w , y≪fw) S S-dir ϕ = y≪fw S S-dir nts
  --     where
  --     foo : [ f x ⊑[ pos G ] (⋁[ G ] S) ]
  --     foo = ϕ

  --     nts : [ f w ⊑[ pos G ] (⋁[ G ] S) ]
  --     nts = {!!}

  patch′-is-compact : [ isCompact Patch′ ]
  patch′-is-compact = compactness-lemma δδδ δδδ-perfect (spec→compact F spec′)
    where
    open CompactnessLemma F Patch′ basis

  patch-is-compact : [ isCompact (Patch F) ]
  patch-is-compact 𝒥 𝒥-dir p = ∥∥-rec (∥∥-prop Θ) G𝟏 (patch′-is-compact 𝒥 dir′ G𝟐)
    where
    Θ : 𝓤 ⁺ ̇
    Θ = Σ[ i ∈ index 𝒥 ] [ ⊤[ Patch F ] ⊑[ pos (Patch F) ] (𝒥 $ i) ]

    dir′ : [ isDirected (pos Patch′) 𝒥 ]
    π₀ dir′ = π₀ 𝒥-dir
    π₁ dir′ i j = ∥∥-rec (∥∥-prop Ψ) G𝟑 (π₁ 𝒥-dir i j)
      where
      Ψ : 𝓤 ̇
      Ψ = Σ[ k ∈ index 𝒥 ] [ (𝒥 $ i) ⊑[ pos Patch′ ] (𝒥 $ k) ]
                         × [ (𝒥 $ j) ⊑[ pos Patch′ ] (𝒥 $ k) ]

      G𝟑 : _ → ∥ Ψ ∥
      G𝟑 (k , q , r) =
        ∣ k , π₀ (⊑patch↔⊑s (𝒥 $ i) (𝒥 $ k)) q , π₀ (⊑patch↔⊑s (𝒥 $ j) (𝒥 $ k)) r ∣

    G𝟏 : Σ[ i ∈ index 𝒥 ] [ ⊤[ Patch′ ] ⊑[ pos Patch′ ] (𝒥 $ i) ]
       → [ ∥ Σ[ i ∈ index 𝒥 ] [ ⊤[ Patch F ] ⊑[ pos (Patch F) ] (𝒥 $ i) ] ∥Ω ]
    G𝟏 (i , q) = ∣ i , π₁ (⊑patch↔⊑s ⊤[ Patch F ] (𝒥 $ i)) q ∣

    G𝟐 : [ ⊤[ Patch′ ] ⊑[ pos Patch′ ] ((WayBelow.⋁ Patch′) 𝒥) ]
    G𝟐 = π₀ (⊑patch↔⊑s ⊤[ Patch′ ] (⋁[ Patch′ ] 𝒥)) p

  open Complements F spec′ basis
  open DefnOfHeytingImplication F
  open Definition F basis

  ℬ-F : Fam 𝓤 ∣ F ∣F
  ℬ-F = π₀ basis

  ℬ-C : Fam (𝓤 ⁺) ∣ F ∣F
  ℬ-C = (Σ[ i ∈ index ℬ-F ] [ _≪_ F (ℬ-F $ i) (ℬ-F $ i) ]) , λ p → ℬ-F $ (π₀ p)

  -- nucleus-lemma : (j : ∣ Patch F ∣F)
  --               → [ isSup (pos (Patch F)) {!⁅ ‘ π₀ (π₀ j) b ’ ⊓[ F ] ¬‘ b ’ ∣ !} {!!} ]
  -- nucleus-lemma = {!!}

  -- nucleus-lemma : (j : ∣ Patch F ∣F)
  --               → j ≡ (⋁[ Patch F ] ⁅ εε F b ∨[ Patch F ] {!!} ∣ b ε ℬ-F ⁆)
  -- nucleus-lemma = {!!}
```

```agda
module NucleusLemma (F : Frame (𝓤 ⁺) 𝓤 𝓤) (spec′ : isSpectral′ F) where

  open import PatchFrame

  𝕨 : hasBasis F → (G : Frame (𝓤 ⁺) 𝓤 𝓤) → hasBasis G → (f : ∣ F ∣F → ∣ G ∣F) → ∣ F ∣F → Fam 𝓤 ∣ G ∣F
  𝕨 (ℬ , p) G (ℬ′ , p′) f x = I , λ { (i , j , p) → ℬ′ $ j }
    where
    I : 𝓤 ̇
    I = Σ[ i  ∈ index ℬ ] Σ[ j ∈ index ℬ′ ]
          ([ (ℬ $ i) ⊑[ pos F ] x ] × [ (ℬ′ $ j) ⊑[ pos G ] f (ℬ $ i) ])

  open import WayBelow F

  -- graph-thm : (bs : hasBasis F) → (G : Frame (𝓤 ⁺) 𝓤 𝓤) → isSpectral′ G → (bs′ : hasBasis G)
  --           → (f : ∣ F ∣F → ∣ G ∣F) → isScottContinuous F G f
  --           → (x : ∣ F ∣F) → [ x ≪ x ] → [ isSup (pos G) (𝕨 bs G bs′ f x) (f x) ]
  -- graph-thm bs@(ℬ , _) G spec bs′@(ℬ′ , _) f f-sc x x-comp = nts₀ , nts₁
  --   where
  --   open PosetReasoning (pos G)

  --   nts₀ : [ ∀[ x₁ ε (𝕨 bs  G bs′ f x) ] (x₁ ⊑[ pos G ] f x) ]
  --   nts₀ z ((i , j , (p , q)) , eq) = subst (λ - → [ rel (pos G) - (f x) ]) eq G𝟏
  --     where
  --     G𝟏 : [ (ℬ′ $ j) ⊑[ pos G ] f x ]
  --     G𝟏 = ℬ′ $ j ⊑⟨ q ⟩ f (ℬ $ i) ⊑⟨ sc→mono F G f f-sc _ _ p ⟩ f x ■

  --   nts₁ : (y : ∣ pos G ∣ₚ) → [ ∀[ x₁ ε (𝕨 bs G bs′ f x) ] (x₁ ⊑[ pos G ] y) ]
  --        → [ f x ⊑[ pos G ] y ]
  --   nts₁ y ϕ = f x                           ⊑⟨ {!!} ⟩
  --              f (⋁[ F ] ⁅ ℬ $ i ∣ i ε Wₓ ⁆) ⊑⟨ {!!} ⟩
  --              ⋁[ G ] ⁅ f (ℬ $ i) ∣ i ε Wₓ ⁆ ⊑⟨ ⦅𝟐⦆ ⟩
  --              y                             ■
  --     where
  --     Wₓ : Fam 𝓤 (index ℬ)
  --     Wₓ = π₀ (π₁ bs x)

  --     ⦅𝟐a⦆ : [ ∀[ z ε ⁅ f (ℬ $ i) ∣ i ε Wₓ ⁆ ] (z ⊑[ pos G ] y) ]
  --     ⦅𝟐a⦆ z (i , eq) =
  --       subst (λ - → [ - ⊑[ pos G ] y ]) eq (ϕ (f (ℬ $ (Wₓ $ i))) ((Wₓ $ i , {!!}) , {!!}))

  --     ⦅𝟐⦆ : _
  --     ⦅𝟐⦆ = ⋁[ G ]-least _ _ ⦅𝟐a⦆

  -- clopen-basis : [ isZeroDimensional (Patch F) ]
  -- clopen-basis = ∥∥-rec (isProp[] (isZeroDimensional (Patch F))) G𝟏 spec′
  --   where
  --   G𝟏 : (Σ[ ℬ ∈ Fam 𝓤 ∣ F ∣F ] _) → [ isZeroDimensional (Patch F) ]
  --   G𝟏 (ℬ , p , (q , f)) = {!!}
  --     where
  --     basis : hasBasis F
  --     basis = ℬ , q

  --     open SomeMoreResults F spec′ basis
  --     open OpenNuclei F
  --     open Complements F
  --     open Definition F basis hiding (ℬ)
  --     open PosetReasoning (pos F)

  --     ℬ-comp : [ ∀[ b ε ℬ ] (b ≪ b) ]
  --     ℬ-comp b (i , eq) = subst (λ - → [ - ≪ - ]) eq (p i)

  --     perfect-nucleus-lemma₀ : (j k : ∣ Patch F ∣F)
  --                            → ((x : ∣ F ∣F) → [ x ≪ x ] → [ π₀ (π₀ j) x ⊑[ pos F ] π₀ (π₀ k) x ])
  --                            → (x : ∣ F ∣F) → [ π₀ (π₀ j) x ⊑[ pos F ] π₀ (π₀ k) x ]
  --     perfect-nucleus-lemma₀ 𝒿@((j , j-n) , j-sc) 𝓀@((k , k-n) , k-sc) ρ x =
  --       j x                    ⊑⟨ ≡⇒⊑ (pos F) (cong j eq) ⟩
  --       j (⋁[ F ] W)           ⊑⟨ ≡⇒⊑ (pos F) (j-sc W W-dir) ⟩
  --       ⋁[ F ] ⁅ j w ∣ w ε W ⁆ ⊑⟨ nts ⟩
  --       ⋁[ F ] ⁅ k w ∣ w ε W ⁆ ⊑⟨ ≡⇒⊑ (pos F) (sym (k-sc W W-dir)) ⟩
  --       k (⋁[ F ] W)           ⊑⟨ ≡⇒⊑ (pos F) (cong k (sym eq)) ⟩
  --       k x                    ■
  --       where
  --       W : Fam 𝓤 (π₀ F)
  --       W = ⁅ ℬ $ i ∣ i ε (π₀ (q x)) ⁆

  --       W-dir : [ isDirected (pos F) W ]
  --       W-dir = π₀ (π₁ (q x))

  --       eq : x ≡ ⋁[ F ] W
  --       eq = ⋁-unique F _ _ (π₀ (π₁ (π₁ (q x)))) (π₁ (π₁ (π₁ (q x))))

  --       goal : _
  --       goal z (i , eq)  = z                       ⊑⟨ ≡⇒⊑ (pos F) (sym eq)         ⟩
  --                          j (W $ i)               ⊑⟨ ρ (W $ i) (p (π₀ (q x) $ i)) ⟩
  --                          k (W $ i)               ⊑⟨ ⋁[ F ]-upper _ _ (i , refl)  ⟩
  --                          ⋁[ F ] ⁅ k w ∣ w ε W ⁆  ■

  --       nts = ⋁[ F ]-least _ _ goal

  --     nucleus-lemma : (j : ∣ Patch F ∣F)
  --                   → j ≡ ⋁[ Patch F ] ⁅ εε F (j .π₀ .π₀ (ℬ $ i)) ⊓[ Patch F ] μ sp basis (ℬ $ i) (p i) ∣ i ∶ index ℬ ⁆
  --     nucleus-lemma 𝒿@((j , j-n) , j-sc) = G𝟐′
  --       where
  --       𝕜 : index ℬ → ∣ Patch F ∣F
  --       𝕜 i = εε F (j (ℬ $ i)) ⊓[ Patch F ] μ sp basis (ℬ $ i) (p i)

  --       𝕜₀ : index ℬ → ∣ F ∣F → ∣ F ∣F
  --       𝕜₀ i x = π₀ (π₀ (𝕜 i)) x

  --       foo : (i : index ℬ) → 𝕜₀ i (ℬ $ i) ≡ j (ℬ $ i)
  --       foo i =
  --         π₀ (π₀ (𝕜 i)) (ℬ $ i)                                   ≡⟨ refl                ⟩
  --         (j (ℬ $ i) ∨[ F ] (ℬ $ i)) ⊓[ F ] ((ℬ $ i) ==> (ℬ $ i)) ≡⟨ ⦅𝟏⦆                 ⟩
  --         (j (ℬ $ i) ∨[ F ] (ℬ $ i)) ⊓[ F ] ⊤[ F ]                ≡⟨ cong (λ - → - ⊓[ F ] ⊤[ F ]) ⦅𝟐⦆ ⟩
  --         j (ℬ $ i) ⊓[ F ] ⊤[ F ]                                 ≡⟨ x∧⊤=x F (j (ℬ $ i)) ⟩
  --         j (ℬ $ i)                                               ∎
  --         where
  --         ⦅𝟏⦆ : _
  --         ⦅𝟏⦆ = cong (λ - → (j (ℬ $ i) ∨[ F ] (ℬ $ i)) ⊓[ F ] -) (==>-id (ℬ $ i))

  --         ⦅𝟐⦆ : j (ℬ $ i) ∨[ F ] (ℬ $ i) ≡ j (ℬ $ i)
  --         ⦅𝟐⦆ = ⊑[ pos F ]-antisym _ _ ⦅𝟐a⦆ ⦅𝟐b⦆
  --           where
  --           ⦅𝟐a⦆ : [ j (ℬ $ i) ∨[ F ] (ℬ $ i) ⊑[ pos F ] j (ℬ $ i) ]
  --           ⦅𝟐a⦆ = ⋁[ F ]-least _ _ nts
  --             where
  --             nts : [ ∀[ x ε ⁅ j (ℬ $ i) , (ℬ $ i) ⁆ ] (x ⊑[ pos F ] j (ℬ $ i)) ]
  --             nts x (true  , eq) = subst (λ - → [ - ⊑[ pos F ] j (ℬ $ i) ]) eq (⊑[ pos F ]-refl _)
  --             nts x (false , eq) =
  --              x         ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩
  --              ℬ $ i     ⊑⟨ π₀ (π₁ j-n) (ℬ $ i) ⟩
  --              j (ℬ $ i) ■

  --           ⦅𝟐b⦆ : [ j (ℬ $ i) ⊑[ pos F ] j (ℬ $ i) ∨[ F ] (ℬ $ i) ]
  --           ⦅𝟐b⦆ = ⋁[ F ]-upper _ (j (ℬ $ i)) (true , refl)

  --       lemma-js : (i : index ℬ) → [ 𝕜 i ⊑[ pos (Patch F) ] 𝒿 ]
  --       lemma-js i x =
  --         𝕜₀ i x                                                     ⊑⟨ ⊑[ pos F ]-refl _ ⟩
  --         (j (ℬ $ i) ∨[ F ] x) ⊓[ F ] ((ℬ $ i) ==> x)                ⊑⟨ ⦅𝟏⦆               ⟩
  --         (j (ℬ $ i) ∨[ F ] x) ⊓[ F ] ((j (ℬ $ i) ∨[ F ] x) ==> j x) ⊑⟨ mp _ _            ⟩
  --         j x                                                        ■
  --         where
  --         ⦅𝟏b⦆ : [ ⊤[ F ] ⊑[ pos F ] (x ==> j x) ]
  --         ⦅𝟏b⦆ = π₁ (==>-is-HI x (j x) ⊤[ F ])
  --                (x ⊓[ F ] ⊤[ F ] ⊑⟨ ⊓[ F ]-lower₀ _ _ ⟩ x ⊑⟨ 𝓃₁ F (π₀ 𝒿) x ⟩ j x ■)

  --         ⦅𝟏a⦆ : [ ((ℬ $ i) ==> x) ⊑[ pos F ] ((j (ℬ $ i) ∨[ F ] x) ==> j x) ]
  --         ⦅𝟏a⦆ =
  --           (ℬ $ i) ==> x                          ⊑⟨ ==>-nucleus-lemma (ℬ $ i) x (j , j-n)           ⟩
  --           j (ℬ $ i) ==> j x                      ⊑⟨ ≡⇒⊑ (pos F) (sym (x∧⊤=x F (j (ℬ $ i) ==> j x))) ⟩
  --           (j (ℬ $ i) ==> j x) ⊓[ F ] ⊤[ F ]      ⊑⟨ cright F (j (ℬ $ i) ==> j x) ⦅𝟏b⦆               ⟩
  --           (j (ℬ $ i) ==> j x) ⊓[ F ] (x ==> j x) ⊑⟨ ==>-∨-lemma (j (ℬ $ i)) x (j x) ⟩
  --           (j (ℬ $ i) ∨[ F ] x) ==> j x           ■

  --         ⦅𝟏⦆ : _
  --         ⦅𝟏⦆ = cright F _ ⦅𝟏a⦆

  --       k : ∣ Patch F ∣F
  --       k = ⋁[ Patch F ] ⁅ 𝕜 i ∣ i ∶ index ℬ ⁆

  --       G𝟐′ : 𝒿 ≡ (⋁[ Patch F ] ⁅ 𝕜 i ∣ i ∶ index ℬ ⁆)
  --       G𝟐′ = ⋁-unique (Patch F) _ _ G𝟐′a G𝟐′b
  --         where
  --         G𝟐′a : [ ∀[ z ε ⁅ 𝕜 i ∣ i ∶ index ℬ ⁆ ] (z ⊑[ pos (Patch F) ] 𝒿) ]
  --         G𝟐′a z (i , eq) = subst (λ - → [ - ⊑[ pos (Patch F) ] 𝒿 ]) eq (lemma-js i)

  --         G𝟐′b : (𝓀 : ∣ (Patch F) ∣F)
  --              → [ ∀[ z ε ⁅ 𝕜 i ∣ i ∶ index ℬ ⁆ ] (z ⊑[ pos (Patch F) ] 𝓀) ]
  --              → [ 𝒿 ⊑[ pos (Patch F) ] 𝓀 ]
  --         G𝟐′b 𝓀@((k , k-n) , k-sc) θ x =
  --           perfect-nucleus-lemma₀ 𝒿 𝓀 ξ x
  --           where
  --           ξ : (y : ∣ F ∣F) → [ y ≪ y ] → [ j y ⊑[ pos F ] k y ]
  --           ξ y y-comp = ∥∥-rec (isProp[] (_ ⊑[ pos F ] _)) final (y-comp ((fmap (λ i → ℬ $ i)) 𝒥) 𝒥-dir cover)
  --             where
  --             𝒥 : Fam 𝓤 (index ℬ)
  --             𝒥 = π₀ (q y)

  --             υ : [ isSup (pos F) ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ y ]
  --             υ = π₁ (π₁ (q y))

  --             cover : [ y ⊑[ pos F ] ⋁[ F ] ⁅ ℬ $ i ∣ i ε 𝒥 ⁆ ]
  --             cover = ≡⇒⊑ (pos F) (⋁-unique F _ _ (π₀ υ) (π₁ υ))

  --             𝒥-dir : [ isDirected (pos F) ⁅ ℬ $ i ∣ i ε 𝒥 ⁆ ]
  --             𝒥-dir = π₀ (π₁ (q y))

  --             final : _ → [ j y ⊑[ pos F ] k y ]
  --             final (𝒾 , p) = subst (λ - → [ j - ⊑[ pos F ] k - ]) eq rem
  --               where
  --               iy : index ℬ
  --               iy = π₀ (q y) $ 𝒾

  --               eq : ℬ $ iy ≡ y
  --               eq = ⊑[ pos F ]-antisym _ _ eq₀ p
  --                 where
  --                 eq₀ : [ (ℬ $ iy) ⊑[ pos F ] y ]
  --                 eq₀ = ℬ $ iy                   ⊑⟨ ⋁[ F ]-upper _ _ (𝒾 , refl) ⟩
  --                       ⋁[ F ] ⁅ ℬ $ i ∣ i ε 𝒥 ⁆ ⊑⟨ ≡⇒⊑ (pos F) (sym (⋁-unique F _ _ (π₀ υ) (π₁ υ))) ⟩
  --                       y                        ■

  --               goal : [ 𝕜₀ iy (ℬ $ iy) ⊑[ pos F ] k (ℬ $ iy) ]
  --               goal = θ (𝕜 iy) (iy , refl) (ℬ $ iy)

  --               rem : [ j (ℬ $ iy) ⊑[ pos F ] k (ℬ $ iy) ]
  --               rem = j (ℬ $ iy)     ⊑⟨ ≡⇒⊑ (pos F) (sym (foo iy)) ⟩
  --                     𝕜₀ iy (ℬ $ iy) ⊑⟨ goal                       ⟩
  --                     k (ℬ $ iy)     ■
-- --}
```

Given some f : F → G where F is a compact frame, if f is Scott-continuous then G is compact as well.
