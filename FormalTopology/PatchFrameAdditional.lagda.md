<!--
```agda
{-# OPTIONS --cubical --experimental-lossy-unification #-}

open import Basis
open import Poset
open import Frame
open import WayBelow
open import ClosedNuclei
open import PatchFrame
open import Spectral
open import Stone
open import Base
open import Regular
open import HeytingImplication
open import PatchFrameNucleusLemma
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
comp→basic : (F : Frame 𝓤 𝓥 𝓦)
           → (ℬ : Fam 𝓦 ∣ F ∣F)
           → isDirBasisFor F ℬ
           → (x : ∣ F ∣F) → [ _≪_ F x x ] → ∥ x ε ℬ ∥
comp→basic {𝓦 = 𝓦} F ℬ basis x x≪x =
  ∥∥-rec (∥∥-prop (x ε ℬ)) nts (x≪x W W-dir p)
  where
  𝒥 : Fam 𝓦 (index ℬ)
  𝒥 = π₀ (basis x)

  W : Fam 𝓦 ∣ F ∣F
  W = ⁅ ℬ $ j ∣ j ε 𝒥 ⁆

  W-dir : [ isDirected (pos F) W ]
  W-dir = π₀ (π₁ (basis x))

  r : x ≡ ⋁[ F ] W
  r = uncurry (⋁-unique F _ _) (π₁ (π₁ (basis x)))

  p : [ x ⊑[ pos F ] ⋁[ F ] W ]
  p = ≡⇒⊑ (pos F) r

  nts : Σ[ i ∈ index W ] [ x ⊑[ pos F ] (W $ i) ] → ∥ x ε ℬ ∥
  nts (i , x≤wᵢ) = ∣ 𝒥 $ i , ⊑[ pos F ]-antisym _ _ rem x≤wᵢ ∣
    where
    open PosetReasoning (pos F)

    rem : [ (W $ i) ⊑[ pos F ] x ]
    rem = W $ i      ⊑⟨ ⋁[ F ]-upper _ _ (i , refl) ⟩
          ⋁[ F ] W   ⊑⟨ ≡⇒⊑ (pos F) (sym r)         ⟩
          x          ■
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
isSpectralMap : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦) (f : F ─f→ G) → hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺ ∨ 𝓤′ ∨ 𝓥′)
isSpectralMap F G ((f , _) , _) = ∀[ x ∶ ∣ F ∣F ] isCompactOpen F x ⇒ isCompactOpen G (f x)
```

```agda
-- compact→clopen-in-stone-locale : (F : Frame 𝓤 𝓥 𝓦)
--                                → [ isStone′ F ]
--                                → (x : ∣ F ∣F) → [ _≪_ F x x ] → hasComplement F x
-- compact→clopen-in-stone-locale {𝓦 = 𝓦} F F-stone x x≪x =
--   ∥∥-rec (hasComplement-prop F x) nts (π₁ F-stone)
--   where
--   nts : Σ[ ℬ ∈ Fam _ ∣ F ∣F ] (isBasisFor F ℬ × isComplemented F ℬ)
--       → hasComplement F x
--   nts (ℬ , b , comp) = ∥∥-rec (hasComplement-prop F x) nts′ (x≪x _ W-dir φ₀ )
--     where
--     𝒥 : Fam 𝓦 (index ℬ)
--     𝒥 = π₀ (b x)

--     W-dir : [ isDirected (pos F) ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ ]
--     W-dir = π₀ (π₁ (b x))

--     φ : x ≡ ⋁[ F ] ⁅ ℬ $ j ∣ j ε 𝒥 ⁆
--     φ = ⋁-unique F _ _ (π₀ (π₁ (π₁ (b x)))) (π₁ (π₁ (π₁ (b x))))

--     φ₀ : [ x ⊑[ pos F ] ⋁[ F ] ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ ]
--     φ₀ = ≡⇒⊑ (pos F) φ

--     nts′ : (Σ[ i ∈ index 𝒥 ] [ x ⊑[ pos F ] (ℬ $ (𝒥 $ i)) ]) → hasComplement F x
--     nts′ (i , p) = subst (λ - → hasComplement F -) (sym eq) (comp (ℬ $ 𝒥 $ i) (𝒥 $ i , refl))
--       where
--       eq : x ≡ ℬ $ (𝒥 $ i)
--       eq = ⊑[ pos F ]-antisym _ _ p (π₀ (π₁ (π₁ (b x))) (ℬ $ 𝒥 $ i) (i , refl))
```

```agda
-- compact↔clopen-in-stone-locale : (F : Frame 𝓤 𝓥 𝓦)
--                                → [ isStone′ F ]
--                                → (x : ∣ F ∣F)
--                                → [ isCompactOpen F x ] ↔ hasComplement F x
-- compact↔clopen-in-stone-locale F stone x = G𝟏 , G𝟐
--   where
--   G𝟏 : [ isCompactOpen F x ] → hasComplement F x
--   G𝟏 = compact→clopen-in-stone-locale F stone x

--   G𝟐 : hasComplement F x → [ isCompactOpen F x ]
--   G𝟐 = clopen→compact-in-compact-locale F (π₀ stone) x
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
module SpectralityOfε (F : Frame (𝓤 ⁺) 𝓤 𝓤) (σ : isSpectral′ F) where

  ε-spec : [ isSpectralMap F (Patch F) (εεε F) ]
  ε-spec = ∥∥-rec (isProp[] (isSpectralMap F (Patch F) (εεε F))) nts σ
    where
    nts : _ → [ isSpectralMap F (Patch F) (εεε F) ]
    nts (ℬ , p , base , q) x x≪x = ≪patch↔≪s (εε F x) (εε F x) (main-lemma x x≪x)
      where
      F-has-basis : hasBasis F
      F-has-basis = ℬ , base

      open SomeMoreResults F σ F-has-basis renaming (Patch′ to Patch′-F)
      open PerfectMap F Patch′-F F-has-basis

      main-lemma : [ isSpectralMap F Patch′-F δδδ ]
      main-lemma x x≪x = perfection-lemma δδδ δδδ-perfect x≪x
```

```agda
```

```agda
open import AdditionalFrameTheorems

ε-is-mono : (F G : Frame (𝓤 ⁺) 𝓤 𝓤)
          → (F-spec : isSpectral′ F)
          → (f g : (Patch F) ─f→ G)
          → [ isSpectralMap (Patch F) G f ]
          → [ isSpectralMap (Patch F) G g ]
          → ((x : ∣ F ∣F) → f .π₀ .π₀ (εε F x) ≡ g .π₀ .π₀ (εε F x))
          → f ≡ g
ε-is-mono {𝓤 = 𝓤} F G F-spec 𝒻@((f , _) , (_ , f-resp-∧ , f-resp-⋁)) ℊ@((g , _) , (_ , g-resp-∧ , g-resp-⋁)) f-spec g-spec ψ =
  Σ≡Prop (isFrameHomomorphism-prop (Patch F) G)
  (Σ≡Prop (isMonotonic-prop (pos (Patch F)) (pos G)) (funExt nts))
  where
  open SpectralityOfε F F-spec

  ε-spectral : [ isSpectralMap F (Patch F) (εεε F) ]
  ε-spectral = ε-spec

  nts : (𝒿 : ∣ Patch F ∣F) → f 𝒿 ≡ g 𝒿
  nts 𝒿@((j , j-n) , j-sc) =
    ∥∥-rec (carrier-is-set (pos G) _ _) goal (∥∥-× (π₁ (stone F F-spec)) F-spec)
    where
    goal : ((Σ[ ℬ ∈ Fam _ ∣ Patch F ∣F ] (isBasisFor (Patch F) ℬ × isComplemented (Patch F) ℬ)) × _)
         → f 𝒿 ≡ g 𝒿
    goal ((ℬP , basis , clop) , spec@(ℬ@(I , _) , _ , bs)) =
      f 𝒿                            ≡⟨ ⦅𝟏⦆ ⟩
      f (⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ I ] Σ[ k ∈ I ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ] ⁆)  ≡⟨ ⦅𝟐⦆ ⟩
      ⋁[ G ] ⁅ f (εε F (ℬ $ i) ⊓[ Patch F ] ν k) ∣ (i , k , _) ∶ Σ[ i ∈ I ] Σ[ k ∈ I ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ] ⁆        ≡⟨ ⦅𝟑⦆ ⟩
      ⋁[ G ] ⁅ f (εε F (ℬ $ i)) ⊓[ G ] f (ν k) ∣ (i , k , _) ∶ Σ[ i ∈ I ] Σ[ k ∈ I ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ] ⁆          ≡⟨ ⦅𝟒⦆ ⟩
      ⋁[ G ] ⁅ g (εε F (ℬ $ i)) ⊓[ G ] g (ν k) ∣ (i , k , _) ∶ Σ[ i ∈ I ] Σ[ k ∈ I ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ] ⁆          ≡⟨ ⦅𝟓⦆ ⟩
      ⋁[ G ] ⁅ g (εε F (ℬ $ i) ⊓[ Patch F ] ν k) ∣ (i , k , _) ∶ Σ[ i ∈ I ] Σ[ k ∈ I ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ] ⁆        ≡⟨ ⦅𝟔⦆ ⟩
      g (⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ I ] Σ[ k ∈ I ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ] ⁆)  ≡⟨ ⦅𝟕⦆ ⟩
      g 𝒿                            ∎
      where
      F-has-basis : hasBasis F
      F-has-basis = ℬ , π₀ bs

      open Main F F-spec spec hiding (ℬ; basis)
      open Complements F (spec′→spec F F-spec) F-has-basis using (complement-thm′; complement-thm)

      ℐ : Fam 𝓤 (index ℬP)
      ℐ = π₀ (basis 𝒿)

      W : Fam 𝓤 ∣ Patch F ∣F
      W = ⁅ ℬP $ i ∣ i ε ℐ ⁆

      ⦅𝟏⦆ = cong f (the-nucleus-lemma 𝒿)

      ⦅𝟐⦆ = f-resp-⋁ ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ I ] Σ[ k ∈ I ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ] ⁆

      ⦅𝟑⦆ = cong (λ - → ⋁[ G ] ((Σ[ i ∈ I ] Σ[ k ∈ I ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ]) , -)) (funExt λ { (i , k , _) → f-resp-∧ (εε F (ℬ $ i)) (ν k) })

      ‘’-mono→¬‘’-mono : (i : index ℬ) → f (ν i) ≡ g (ν i)
      ‘’-mono→¬‘’-mono i = complements-unique G (f (εε F (ℬ $ i))) (f (ν i)) (g (ν i)) comp₀ comp₂
        where
        nts₀ : complements (Patch F) (εε F (ℬ $ i)) (ν i)
        nts₀ = complement-thm′ (ℬ $ i) (κ i)

        comp₀ : complements G (f (εε F (ℬ $ i))) (f (ν i))
        comp₀ = complement-preservation (Patch F) G 𝒻 (εε F (ℬ $ i)) (ν i) nts₀

        comp₁ : complements G (g (εε F (ℬ $ i))) (g (ν i))
        comp₁ = complement-preservation (Patch F) G ℊ (εε F (ℬ $ i)) (ν i) nts₀

        γ : f (εε F (ℬ $ i)) ≡ g (εε F (ℬ $ i))
        γ = ψ (ℬ $ i)

        comp₂ : complements G (f (εε F (ℬ $ i))) (g (ν i))
        comp₂ = subst (λ - → complements G - (g (ν i))) (sym γ) comp₁


      ⦅𝟒⦆ = cong (λ - → ⋁[ G ] ((Σ[ i ∈ I ] Σ[ k ∈ I ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ]) , -)) (funExt rem)
        where
        rem : _
        rem (i , k , p) =
          (f (εε F (ℬ $ i))) ⊓[ G ] (f (ν k)) ≡⟨ cong (λ - → - ⊓[ G ] (f (ν k))) (ψ (ℬ $ i))  ⟩
          g (εε F (ℬ $ i)) ⊓[ G ] (f (ν k))   ≡⟨ cong (λ - → g (εε F (ℬ $ i)) ⊓[ G ] -) (‘’-mono→¬‘’-mono k) ⟩
          g (εε F (ℬ $ i)) ⊓[ G ] g (ν k)     ∎

      ⦅𝟓⦆ = cong (λ - → ⋁[ G ] ((Σ[ i ∈ I ] Σ[ k ∈ I ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ]) , -)) (funExt λ { (i , k , _) → sym (g-resp-∧ (εε F (ℬ $ i)) (ν k)) })

      ⦅𝟔⦆ = sym (g-resp-⋁ ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ I ] Σ[ k ∈ I ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ] ⁆)

      ⦅𝟕⦆ = cong g (sym (the-nucleus-lemma 𝒿))
```
