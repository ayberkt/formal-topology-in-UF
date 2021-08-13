<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Poset
open import Frame
open import Regular
open import WayBelow

module PatchFrameAdditional where
```
-->

```agda
⋜→≪ : (F : Frame 𝓤 𝓥 𝓦)
    → [ isCompact F ]
    → (x y : ∣ F ∣F) → x ⋜[ F ] y → [ _≪_ F x y ]
⋜→≪ F F-comp x y (z , comp₀ , comp₁) S S-dir p =
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
