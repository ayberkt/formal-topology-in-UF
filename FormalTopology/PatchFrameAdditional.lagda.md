<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Poset
open import Frame
open import WayBelow
open import ClosedNuclei
open import PatchFrame
open import Spectral
open import Stone
open import Regular
open import HeytingImplication
open import Cubical.Foundations.Function using (uncurry)

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

```agda
⇊′ : (F : Frame 𝓤 𝓥 𝓦) → ∣ F ∣F → hasBasis F → Fam (𝓤 ∨ 𝓦) ∣ F ∣F
⇊′ F x (ℬ , _) = ⁅ ℬ $ i ∣ (i , _) ∶ (Σ[ i ∈ index ℬ ] (ℬ $ i) ⋜[ F ] x ) ⁆
```

```agda
clopen→compact-in-compact-locale : (F : Frame 𝓤 𝓥 𝓦)
                                 → [ isCompact F ]
                                 → (x : ∣ F ∣F)
                                 → hasComplement F x
                                 → [ _≪_ F x x ]
clopen→compact-in-compact-locale F F-comp x x-clopen = ⋜→≪ F F-comp x x x-clopen
```

```agda
isSpectralMap : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦) (f : F ─f→ G) → _ ̇
isSpectralMap F G ((f , _) , _) =
  (x : ∣ F ∣F) → [ isCompactOpen F x ] → [ isCompactOpen G (f x) ]
```

```agda
compact→clopen-in-stone-locale : (F : Frame 𝓤 𝓥 𝓦)
                                 → [ isStone′ F ]
                                 → (x : ∣ F ∣F) → [ _≪_ F x x ] → hasComplement F x
compact→clopen-in-stone-locale {𝓦 = 𝓦} F F-stone x x≪x =
  ∥∥-rec (hasComplement-prop F x) nts (π₁ F-stone)
  where
  nts : Σ[ ℬ ∈ Fam _ ∣ F ∣F ] (isBasisFor F ℬ × isComplemented F ℬ)
      → hasComplement F x
  nts (ℬ , b , comp) = ∥∥-rec (hasComplement-prop F x) nts′ (x≪x _ W-dir φ₀ )
    where
    𝒥 : Fam 𝓦 (index ℬ)
    𝒥 = π₀ (b x)

    W-dir : [ isDirected (pos F) ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ ]
    W-dir = π₀ (π₁ (b x))

    φ : x ≡ ⋁[ F ] ⁅ ℬ $ j ∣ j ε 𝒥 ⁆
    φ = ⋁-unique F _ _ (π₀ (π₁ (π₁ (b x)))) (π₁ (π₁ (π₁ (b x))))

    φ₀ : [ x ⊑[ pos F ] ⋁[ F ] ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ ]
    φ₀ = ≡⇒⊑ (pos F) φ

    nts′ : (Σ[ i ∈ index 𝒥 ] [ x ⊑[ pos F ] (ℬ $ (𝒥 $ i)) ]) → hasComplement F x
    nts′ (i , p) = subst (λ - → hasComplement F -) (sym eq) (comp (ℬ $ 𝒥 $ i) (𝒥 $ i , refl))
      where
      eq : x ≡ ℬ $ (𝒥 $ i)
      eq = ⊑[ pos F ]-antisym _ _ p (π₀ (π₁ (π₁ (b x))) (ℬ $ 𝒥 $ i) (i , refl))
```

```agda
compact↔clopen-in-stone-locale : (F : Frame 𝓤 𝓥 𝓦)
                               → [ isStone′ F ]
                               → (x : ∣ F ∣F)
                               → [ isCompactOpen F x ] ↔ hasComplement F x
compact↔clopen-in-stone-locale F stone x = G𝟏 , G𝟐
  where
  G𝟏 : [ isCompactOpen F x ] → hasComplement F x
  G𝟏 = compact→clopen-in-stone-locale F stone x

  G𝟐 : hasComplement F x → [ isCompactOpen F x ]
  G𝟐 = clopen→compact-in-compact-locale F (π₀ stone) x
```

```agda
-- perfect-maps-determined-by-compact-opens : (F : Frame 𝓤 𝓥 𝓥) (G : Frame 𝓤′ 𝓥 𝓥)
--                                          → (F-ℬ : hasBasis F)
--                                          → (f g : F ─f→ G)
--                                          → PerfectMap.isPerfect F G F-ℬ f
--                                          → PerfectMap.isPerfect F G F-ℬ g
--                                          → ((x : ∣ F ∣F) → [ _≪_ F x x ] → f .π₀ .π₀ x ≡ g .π₀ .π₀ x)
--                                          → (x : ∣ F ∣F) → f .π₀ .π₀ x ≡ g .π₀ .π₀ x
-- perfect-maps-determined-by-compact-opens = {!!}
```

```agda
basic-eq : (F G : Frame 𝓤 𝓥 𝓦) (f g : F ─f→ G)
         → ((ℬ , _) : hasBasis F)
         → ((b : ∣ F ∣F) →  b ε ℬ → f .π₀ .π₀ b ≡ g .π₀ .π₀ b)
         → f ≡ g
basic-eq {𝓦 = 𝓦} F G ((f , _) , (_ , _ , f-resp-⋁)) ((g , _) , (_ , _ , g-resp-⋁)) (ℬ , basis) ψ =
  Σ≡Prop (isFrameHomomorphism-prop F G) (Σ≡Prop (isMonotonic-prop (pos F) (pos G)) (funExt nts))
    where
    nts : (x : ∣ F ∣F) → f x ≡ g x
    nts x = f x                            ≡⟨ cong f eq ⟩
            f (⋁[ F ] ⁅ ℬ $ i ∣ i ε 𝒥 ⁆)   ≡⟨ f-resp-⋁ ⁅ ℬ $ i ∣ i ε 𝒥 ⁆ ⟩
            ⋁[ G ] ⁅ f (ℬ $ i) ∣ i ε 𝒥 ⁆   ≡⟨ cong (λ - → ⋁[ G ] (index 𝒥 , -)) (funExt λ i → ψ (ℬ $ 𝒥 $ i) ((𝒥 $ i) , refl)) ⟩
            ⋁[ G ] ⁅ g (ℬ $ i) ∣ i ε 𝒥 ⁆   ≡⟨ sym (g-resp-⋁ ⁅ ℬ $ i ∣ i ε 𝒥 ⁆) ⟩
            g (⋁[ F ] ⁅ (ℬ $ i) ∣ i ε 𝒥 ⁆) ≡⟨ cong g (sym eq) ⟩
            g x                            ∎
      where
      𝒥 : Fam 𝓦 (index ℬ)
      𝒥 = π₀ (basis x)

      eq : x ≡ ⋁[ F ] ⁅ ℬ $ i ∣ i ε 𝒥 ⁆
      eq =  uncurry (⋁-unique F ⁅ ℬ $ i ∣ i ε 𝒥 ⁆ x) (π₁ (π₁ (basis x)))
```

```agda
-- ε-is-mono : (F G : Frame 𝓤 𝓥 𝓦) (f g : (Patch F) ─f→ G)
--           → isSpectralMap (Patch F) G f
--           → isSpectralMap (Patch F) G g
--           → ((x : ∣ F ∣F) → f .π₀ .π₀ (εε F x) ≡ g .π₀ .π₀ (εε F x))
--           → f ≡ g
-- ε-is-mono F G f g f-spec g-spec ψ =
--   Σ≡Prop (isFrameHomomorphism-prop (Patch F) G)
--   (Σ≡Prop (isMonotonic-prop (pos (Patch F)) (pos G)) (funExt nts))
--   where
--   ε-spectral : isSpectralMap F (Patch F) (εεε F)
--   ε-spectral = {!!}

--   main : (x : ∣ F ∣F) → [ isCompactOpen F x ] → f .π₀ .π₀ (εε F x) ≡ g .π₀ .π₀ (εε F x)
--   main x x-comp = {!!}

--   nts : (𝒿 : ∣ Patch F ∣F) → f .π₀ .π₀ 𝒿 ≡ g .π₀ .π₀ 𝒿
--   nts 𝒿@((j , j-n) , j-sc) = {!!}
```
