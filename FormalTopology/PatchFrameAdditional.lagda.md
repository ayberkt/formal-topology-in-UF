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
open import RightAdjoint hiding (hasBasis)
open import Base hiding (hasBasis)
open import Regular
open import HeytingImplication
open import PatchFrameNucleusLemma
open import Cubical.Data.List hiding ([_])
open import Cubical.Functions.Logic renaming (_⊓_ to _∧_)
open import Cubical.Foundations.Function using (uncurry)
open import Cubical.Foundations.Isomorphism using (isIso)

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
-- stone→spec : (F : Frame 𝓤 𝓥 𝓦)
--            → [ isStone′ F ] → isSpectral′ F
-- stone→spec F (comp , zero-dim) = ∥∥-rec (∥∥-prop _) nts zero-dim
--   where
--   nts : Σ-syntax (Fam _ ∣ F ∣F) (λ ℬ → isBasisFor F ℬ × isComplemented F ℬ)
--       → ∥ Σ-syntax (Fam _ ∣ F ∣F) (λ ℬ → ((i : index ℬ) → [ isCompactOpen F (ℬ $ i) ]) × isDirBasisFor F ℬ × closedUnderFinMeets F ℬ) ∥
--   nts (ℬ , basis , cl) = ∣ ℬ , ((λ i →  clopen→compact-in-compact-locale F comp (ℬ $ i) (cl (ℬ $ i) (i , refl))) , G𝟏 , G𝟐) ∣
--     where
--     G𝟏 : isDirBasisFor F ℬ
--     G𝟏 x = π₀ (basis x) , G𝟏a , π₁ (basis x)
--       where
--       G𝟏a : [ isDirected (pos F) ⁅ ℬ $ j ∣ j ε π₀ (basis x) ⁆ ]
--       G𝟏a = ∣ {!!} ∣ , {!!}

--     G𝟐 : closedUnderFinMeets F ℬ
--     G𝟐 = {!!} , {!!}
```

```agda
isSpectralMap : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦) (f : F ─f→ G) → hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺ ∨ 𝓤′ ∨ 𝓥′)
isSpectralMap F G ((f , _) , _) = ∀[ x ∶ ∣ F ∣F ] isCompactOpen F x ⇒ isCompactOpen G (f x)
```

```agda
directify-clopen : (F : Frame 𝓤 𝓥 𝓦)
                 → (ℬ : Fam 𝓦 ∣ F ∣F)
                 → isComplemented F ℬ
                 → isComplemented F (directify F ℬ)
directify-clopen F ℬ@(I , β) ψ b (is , eq) = subst (hasComplement F) eq (nts is)
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

clopen-basis-∧-complement : (F : Frame 𝓤 𝓥 𝓦)
                      → (ℬ : Fam 𝓦 ∣ F ∣F)
                      → isComplemented F ℬ
                      → (i j : index ℬ)
                      → hasComplement F ((ℬ $ i) ⊓[ F ] (ℬ $ j))
clopen-basis-∧-complement = {!!}

compact→clopen-in-stone-locale : (F : Frame 𝓤 𝓥 𝓦)
                               → [ isStone′ F ]
                               → (x : ∣ F ∣F) → [ _≪_ F x x ] → hasComplement F x
compact→clopen-in-stone-locale {𝓦 = 𝓦} F F-stone x x≪x =
  ∥∥-rec (hasComplement-prop F x) nts (π₁ F-stone)
  where
  nts : Σ[ ℬ ∈ Fam _ ∣ F ∣F ] (isBasisFor F ℬ × isComplemented F ℬ)
      → hasComplement F x
  nts (ℬ , b , comp) =
    ∥∥-rec (hasComplement-prop F x) (ℬ′-comp x) (comp→basic F ℬ′ ℬ′-basis x x≪x)
    where
    ℬ′ : Fam 𝓦 ∣ F ∣F
    ℬ′ = directify F ℬ

    ℬ′-basis : isDirBasisFor F ℬ′
    ℬ′-basis = directified-basis-gives-basis F ℬ b

    ℬ′-comp : isComplemented F ℬ′
    ℬ′-comp = directify-clopen F ℬ comp
```

```agda
compact↔clopen-in-stone-locale : (F : Frame 𝓤 𝓥 𝓦)
                               → [ isStone′ F ]
                               → (x : ∣ F ∣F) → [ _≪_ F x x ] ↔ hasComplement F x
compact↔clopen-in-stone-locale F F-stone@(F-comp , _) x =
    (compact→clopen-in-stone-locale F F-stone x)
  , (clopen→compact-in-compact-locale F F-comp x)
  where
  F-compact : [ isCompact F ]
  F-compact = F-comp
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
clopen→basic : (F : Frame (𝓤 ⁺) 𝓤 𝓤)
             → [ isStone′ F ]
             → ((ℬ , _) : Σ[ ℬ ∈ Fam 𝓤 ∣ F ∣F ] isDirBasisFor F ℬ)
             → (x : ∣ F ∣F) → hasComplement F x → ∥ x ε ℬ ∥
clopen→basic F F-stone (ℬ , p) x x-comp =
  comp→basic F ℬ p x (clopen→compact-in-compact-locale F (π₀ F-stone) x x-comp)
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
      open Complements F F-spec F-has-basis using (complement-thm′; complement-thm)
      open OpenNuclei

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

```agda
-- clopen-basis-fin-meets : (F : Frame (𝓤 ⁺) 𝓤 𝓤)
--                        → [ isStone′ F ]
--                        → (ℬ : Fam 𝓤 ∣ F ∣F)
--                        → isDirBasisFor F ℬ
--                        → isComplemented F ℬ
--                        → ∥ closedUnderFinMeets F ℬ ∥
-- clopen-basis-fin-meets F F-stone ℬ  b comp =
--   ∥∥-rec {!!} nts foo
--   where
--   foo : ∥ ⊤[ F ] ε ℬ ∥
--   foo = clopen→basic F F-stone (ℬ , b) ⊤[ F ] (⊥[ F ] , (G𝟏 , G𝟐))
--     where
--     G𝟏 = ⊤[ F ] ⊓[ F ] ⊥[ F ] ≡⟨ x∧⊥=⊥ F ⊤[ F ]       ⟩
--          ⊥[ F ]               ∎

--     G𝟐 = {!!}

--   baz : {!!}
--   baz = {!comp→basic!}

--   bar : (i j : index ℬ) → ∥ Σ[ k ∈ index ℬ ] ℬ $ k ≡ (ℬ $ i) ⊓[ F ] (ℬ $ j) ∥
--   bar i j = clopen→basic F F-stone (ℬ , b) ((ℬ $ i) ⊓[ F ] (ℬ $ j)) ϕ
--     where
--     ¬ℬ : index ℬ → ∣ F ∣F
--     ¬ℬ i = π₀ (comp (ℬ $ i) (i , refl))

--     ϕ : hasComplement F ((ℬ $ i) ⊓[ F ] (ℬ $ j))
--     ϕ = (¬ℬ i ∨[ F ] ¬ℬ j)
--       , ∧-complement F (ℬ $ i) (ℬ $ j) (¬ℬ i) (¬ℬ j) (π₁ (comp (ℬ $ i) (i , refl))) ((π₁ (comp (ℬ $ j) (j , refl))))

--   nts : ⊤[ F ] ε ℬ → ∥ closedUnderFinMeets F ℬ ∥
--   nts (k , eq) =
--     {!!} -- ∣ (k , subst (λ - → [ isTop (pos F) - ]) (sym eq) ⊤[ F ]-top) , G𝟏 ∣
--     where
--     G𝟏 : (i j : index ℬ)
--        → Σ-syntax (index ℬ) (λ k → [ isInf (pos F) (ℬ $ k) (ℬ $ i) (ℬ $ j) ])
    -- G𝟏 i j = {!!}
```

```agda
isInjective : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
            → isSet A → isSet B → (f : A → B) → hProp (𝓤 ∨ 𝓥)
isInjective {A = A} A-set B-set f =
  ∀[ x ∶ A ] ∀[ y ∶ A ] ((f x ≡ f y) , B-set (f x) (f y)) ⇒ ((x ≡ y) , A-set x y)

isSurjective : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → isSet A → isSet B → (f : A → B) → hProp (𝓤 ∨ 𝓥)
isSurjective {A = A} {B} A-set B-set f = ∀[ y ∶ B ] ∥ Σ[ x ∈ A ] f x ≡ y ∥Ω

isIsomorphism : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → isSet A → isSet B → (f : A → B) → hProp (𝓤 ∨ 𝓥)
isIsomorphism A-set B-set f = isInjective A-set B-set f ∧ isSurjective A-set B-set f

module Lemma3-3-V (F : Frame (𝓤 ⁺) 𝓤 𝓤) (stone : [ isStone′ F ]) where

  F-spec : isSpectral′ F
  F-spec = ∥∥-rec (∥∥-prop _) nts (π₁ stone)
    where
    nts : Σ[ ℬ ∈ (Fam 𝓤 ∣ F ∣F) ] (isBasisFor F ℬ × isComplemented F ℬ)
        → ∥ Σ[ ℬ ∈ (Fam 𝓤 ∣ F ∣F) ]
              ((i : index ℬ) → [ isCompactOpen F (ℬ $ i) ])
            × isDirBasisFor F ℬ
            × closedUnderFinMeets F ℬ ∥
    nts (ℬ , b , comp) = ∥∥-rec (∥∥-prop _) goal ⊤εℬ
      where
      F-compact : [ isCompact F ]
      F-compact = π₀ stone

      ϕ : isDirBasisFor F (directify F ℬ)
      ϕ = directified-basis-gives-basis F ℬ b

      κ : (is : List (index ℬ)) → [ isCompactOpen F (directify F ℬ $ is) ]
      κ is = clopen→compact-in-compact-locale F F-compact
               (directify F ℬ $ is)
               (directify-clopen F ℬ comp (directify F ℬ $ is) (is , refl))

      ⊤εℬ : ∥ ⊤[ F ] ε directify F ℬ ∥
      ⊤εℬ = comp→basic F (directify F ℬ) ϕ ⊤[ F ] F-compact

      goal : ⊤[ F ] ε directify F ℬ
           → ∥ Σ[ ℬ₁ ∈ (Fam 𝓤 ∣ F ∣F) ] (((i : index ℬ₁) → [ isCompactOpen F (ℬ₁ $ i) ]) × isDirBasisFor F ℬ₁ × closedUnderFinMeets F ℬ₁) ∥
      goal (i , eq) = ∣ directify F ℬ , ζ , directified-basis-gives-basis F ℬ b , γ ∣
        where
        ζ : (j : index (directify F ℬ)) → [ isCompactOpen F (directify F ℬ $ j) ]
        ζ js = clopen→compact-in-compact-locale F (π₀ stone) (directify F ℬ $ js) (directify-clopen F ℬ comp (directify F ℬ $ js) (js , refl))

        γ : closedUnderFinMeets F (directify F ℬ)
        γ = ∣ i , (subst (λ - → [ isTop (pos F) - ]) (sym eq) ⊤[ F ]-top) ∣ , rem
          where
          rem : (is js : List (index ℬ)) → ∥ Σ[ ks ∈ List (index ℬ) ] [ isInf (pos F) (directify F ℬ $ ks) (directify F ℬ $ is) (directify F ℬ $ js) ] ∥
          rem is js = ∥∥-rec (∥∥-prop _) nts₁ (clopen→basic F stone (directify F ℬ , directified-basis-gives-basis F ℬ b) ((directify F ℬ $ is) ⊓[ F ] (directify F ℬ $ js)) nts₀)
            where
            ¬is : ∣ F ∣F
            ¬is = π₀ (directify-clopen F ℬ comp (directify F ℬ $ is) (is , refl))

            ¬js : ∣ F ∣F
            ¬js = π₀ (directify-clopen F ℬ comp (directify F ℬ $ js) (js , refl))

            nts₀ : hasComplement F ((directify F ℬ $ is) ⊓[ F ] (directify F ℬ $ js))
            nts₀ = (¬is ∨[ F ] ¬js) , ∧-complement F (directify F ℬ $ is) (directify F ℬ $ js) ¬is ¬js
                                        (π₁ (directify-clopen F ℬ comp (directify F ℬ $ is) (is , refl)))
                                        (π₁ (directify-clopen F ℬ comp (directify F ℬ $ js) (js , refl)))

            nts₁ : ((directify F ℬ $ is) ⊓[ F ] (directify F ℬ $ js)) ε directify F ℬ
                 → ∥ Σ[ ks ∈ List (index ℬ) ] [ isInf (pos F) (directify F ℬ $ ks) (directify F ℬ $ is) (directify F ℬ $ js) ] ∥
            nts₁ (ks , eq) = ∣ ks , subst (λ - → [ isInf (pos F) - _ _ ]) (sym eq) ((⊓[ F ]-lower₀ _ _ , ⊓[ F ]-lower₁ _ _) , λ z (p , q) → ⊓[ F ]-greatest _ _ _ p q) ∣


  stone-basis : (𝒿 : ∣ Patch F ∣F)
              → ∥ Σ[ S ∈ Fam 𝓤 ∣ F ∣F ] 𝒿 ≡ ⋁[ Patch F ] ⁅ εε F s ∣ s ε S ⁆ ∥
  stone-basis 𝒿@((j , _) , _) = ∥∥-rec (∥∥-prop _) main-goal (π₁ stone)
    where
    main-goal : Σ[ ℬ ∈ Fam 𝓤 ∣ F ∣F ] isBasisFor F ℬ × isComplemented F ℬ
              → ∥ Σ[ S ∈ Fam 𝓤 ∣ F ∣F ] 𝒿 ≡ ⋁[ Patch F ] ⁅ εε F s ∣ s ε S ⁆ ∥
    main-goal (ℬ , basis , comp) = ∣ S , G𝟑 ∣
      where
      ℬ↑ : Fam 𝓤 ∣ F ∣F
      ℬ↑ = directify F ℬ

      not : index ℬ↑ → ∣ F ∣F
      not is = π₀ (directify-clopen F ℬ comp (ℬ↑ $ is) (is , refl))

      S : Fam 𝓤 ∣ F ∣F
      S = (Σ[ is ∈ index ℬ↑ ] Σ[ js ∈ index ℬ↑ ] [ (ℬ↑ $ is) ⊑[ pos F ] j (ℬ↑ $ js) ])
        , λ { (is , js , _) → (ℬ↑ $ is) ⊓[ F ] not js }

      dir-basis : isDirBasisFor F ℬ↑
      dir-basis = directified-basis-gives-basis F ℬ basis

      κκ : (i : index ℬ↑) → [ isCompactOpen F (ℬ↑ $ i) ]
      κκ i = clopen→compact-in-compact-locale F (π₀ stone) (ℬ↑ $ i) (directify-clopen F ℬ comp (ℬ↑ $ i) (i , refl))

      ∧-closure : closedUnderFinMeets F ℬ↑
      ∧-closure = G𝟏 , G𝟐
        where
        G𝟏 : ∥ Σ[ i ∈ index ℬ↑ ] [ isTop (pos F) (ℬ↑ $ i) ] ∥
        G𝟏 = ∥∥-rec
               (∥∥-prop _)
               (λ (i , eq) → ∣ i , (subst (λ - → [ isTop (pos F) - ]) (sym eq) ⊤[ F ]-top) ∣)
               (comp→basic F ℬ↑ dir-basis ⊤[ F ] (π₀ stone) )

        G𝟐 : (i j : index ℬ↑) → ∥ Σ[ k ∈ index ℬ↑ ] [ isInf (pos F) (ℬ↑ $ k) (ℬ↑ $ i) (ℬ↑ $ j) ] ∥
        G𝟐 i j = ∥∥-rec (∥∥-prop _)
                   goal
                   (clopen→basic F stone (ℬ↑ , dir-basis) ((ℬ↑ $ i) ⊓[ F ] (ℬ↑ $ j)) (clopen-basis-∧-complement F (directify F ℬ) (directify-clopen F ℬ comp) i j))
          where
          goal : ((ℬ↑ $ i) ⊓[ F ] (ℬ↑ $ j)) ε ℬ↑ → ∥ Σ[ k ∈ index ℬ↑ ] [ isInf (pos F) (ℬ↑ $ k) (ℬ↑ $ i) (ℬ↑ $ j) ] ∥
          goal (k , eq) = ∣ k , (subst (λ - → [ isInf (pos F) - (ℬ↑ $ i) (ℬ↑ $ j) ]) (sym eq) ((G𝟐a , G𝟐b) , G𝟐c)) ∣
            where
            G𝟐a = ⊓[ F ]-lower₀ (ℬ↑ $ i) (ℬ↑ $ j)
            G𝟐b = ⊓[ F ]-lower₁ (ℬ↑ $ i) (ℬ↑ $ j)
            G𝟐c = uncurry ∘ ⊓[ F ]-greatest (ℬ↑ $ i) (ℬ↑ $ j)

      spec : isSpectral′ F
      spec = ∣ ℬ↑ , κκ , dir-basis , ∧-closure ∣

      open Main F spec (ℬ↑ , κκ , dir-basis , ∧-closure) hiding (ℬ)
      open Complements F spec (ℬ↑ , dir-basis)

      ¬-ε-lemma : (x x′ : ∣ F ∣F)
                → complements F x x′
                → (comp : [ _≪_ F x x ])
                → μ x comp ≡ εε F x′
      ¬-ε-lemma x x′ (p , q) x≪x =
        complements-unique (Patch F) (εε F x) (μ x x≪x) (εε F x′) (complements-sym (Patch F) (complement-thm x x≪x)) foo
        where
        foo : complements (Patch F) (εε F x) (εε F x′)
        foo = complement-preservation F (Patch F) (εεε F) x x′ (p , q)

      G𝟒 : _ ≡ _
      G𝟒 = cong (λ - → ⋁[ Patch F ] -) (ΣPathTransport→PathΣ _ _ (refl , {!!}))
        where
        G𝟒a : ((is , ks , p) : Σ[ i ∈ index ℬ↑ ] Σ[ k ∈ index ℬ↑ ] [ (ℬ↑ $ i) ⊑[ pos F ] (j (ℬ↑ $ k)) ])
            → ((εε F (ℬ↑ $ is)) ⊓[ Patch F ] ν ks) ≡ εε F ((ℬ↑ $ is) ⊓[ F ] not ks)
        G𝟒a (is , ks , p) =
          εε F (ℬ↑ $ is) ⊓[ Patch F ] ν ks          ≡⟨ † ⟩
          εε F (ℬ↑ $ is) ⊓[ Patch F ] εε F (not ks) ≡⟨ sym (εε-resp-∧ F (ℬ↑ $ is) (not ks)) ⟩
          εε F ((ℬ↑ $ is) ⊓[ F ] not ks)            ∎
          where
          foo : complements F (ℬ↑ $ ks) (not ks)
          foo = π₁ (directify-clopen F ℬ comp (ℬ↑ $ ks) (ks , refl))

          † : _
          † = cong (λ - → (εε F (ℬ↑ $ is)) ⊓[ Patch F ] -) (¬-ε-lemma (ℬ↑ $ ks) (not ks) foo (κκ ks))

      G𝟑 : 𝒿 ≡ ⋁[ Patch F ] ⁅ εε F s ∣ s ε S ⁆
      G𝟑 = 𝒿                                  ≡⟨ the-nucleus-lemma 𝒿 ⟩
           ⋁[ Patch F ] ⁅ εε F (ℬ↑ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ↑ ] Σ[ k ∈ index ℬ↑ ] [ (ℬ↑ $ i) ⊑[ pos F ] (j (ℬ↑ $ k)) ] ⁆   ≡⟨ G𝟒 ⟩
           ⋁[ Patch F ] ⁅ εε F s ∣ s ε S ⁆    ∎

    -- nts : _
    -- nts si@(ℬ , comp , _) = ∥∥-rec (∥∥-prop _) nts′ (π₁ stone)
    --   where
    --   open Main F F-spec si hiding (ℬ)

    --   nts′ : Σ-syntax (Fam 𝓤 ∣ F ∣F) (λ ℬ₁ → isBasisFor F ℬ₁ × isComplemented F ℬ₁)
    --        → ∥ Σ-syntax (Fam 𝓤 ∣ F ∣F) (λ S → 𝒿 ≡ ⋁[ Patch F ] fmap (εε F) S) ∥
    --   nts′ (ℬ′ , _ , κ) = ∣ S , G𝟏 ∣
    --     where
    --     open PosetReasoning (pos (Patch F))

    --     not : index ℬ′ → ∣ F ∣F
    --     not i = π₀ (κ (ℬ′ $ i) (i , refl))

    --     S : Fam 𝓤 ∣ F ∣F
    --     S = (Σ[ k ∈ index ℬ′ ] Σ[ l ∈ index ℬ′ ] [ (ℬ′ $ k) ⊑[ pos F ] j (ℬ′ $ l) ])
    --       , λ { (k , l , _) → (ℬ′ $ k) ⊓[ F ] not l }

    --     G𝟐 : _
    --     G𝟐 = ⋁[ Patch F ]-least _ (⋁[ Patch F ] ⁅ εε F s ∣ s ε S ⁆) G𝟐a
    --       where
    --       G𝟐a : [ ∀[ k ε ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ] ⁆ ]
    --                 (k ⊑[ pos (Patch F) ] ⋁[ Patch F ] ⁅ εε F s ∣ s ε S ⁆) ]
    --       G𝟐a z ((k , l , p) , eq) =
    --         subst (λ - → [ rel (pos (Patch F)) - (⋁[ Patch F ] (fmap (λ s → εε F s)) S) ]) eq G𝟐b
    --         where
    --         G𝟐b : [ (εε F (ℬ $ k) ⊓[ Patch F ] ν l) ⊑[ pos (Patch F) ] ⋁[ Patch F ] ⁅ εε F s ∣ s ε S ⁆ ]
    --         G𝟐b = εε F (ℬ $ k) ⊓[ Patch F ] ν l          ⊑⟨ {!!} ⟩
    --               εε F (ℬ $ k) ⊓[ Patch F ] εε F {!!}    ⊑⟨ {!!} ⟩
    --               {!!}                                   ■

    --     G𝟑 : _
    --     G𝟑 = {!!}

    --     † : ⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ] ⁆
    --       ≡ ⋁[ Patch F ] ⁅ εε F s ∣ s ε S ⁆
    --     † = ⊑[ pos (Patch F) ]-antisym _ _ G𝟐 G𝟑

    --     G𝟏 : 𝒿 ≡ ⋁[ Patch F ] ⁅ εε F s ∣ s ε S ⁆
    --     G𝟏 = 𝒿                                  ≡⟨ the-nucleus-lemma 𝒿 ⟩
    --         ⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ] [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ] ⁆  ≡⟨ {!!} ⟩
    --         ⋁[ Patch F ] ⁅ εε F s ∣ s ε S ⁆    ∎

      -- goal : _
      -- goal (ℬ , b , comp) = ∣ S , G𝟏 ∣
      --   where
      --   basis : hasBasis F
      --   basis = directify F ℬ , directified-basis-gives-basis F ℬ b


      --   κ : {!!}
      --   κ = {!!}


      --   G𝟏 : 𝒿 ≡ ⋁[ Patch F ] ⁅ εε F s ∣ s ε S ⁆
      --   G𝟏 = 𝒿                                                    ≡⟨ {!!} ⟩
      --        ⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] μ (ℬ $ k) {!!}  ∣ (i , k , _) ∶ Σ[ i ∈ _ ] Σ[ k ∈ _ ] [ (ℬ $ i) ⊑[ pos F ] (j (ℬ $ k)) ] ⁆                               ≡⟨ {!!} ⟩
      --        ⋁[ Patch F ] ⁅ εε F s ∣ s ε S ⁆ ∎

--   -- F-has-basis : {!!}
--   -- F-has-basis = {!!}

--   -- open SomeMoreResults F

--   F-set : isSet ∣ F ∣F
--   F-set = carrier-is-set (pos F)

--   P-set : isSet ∣ Patch F ∣F
--   P-set = carrier-is-set (pos (Patch F))

--   εε-is-iso-on-stone-locales : [ isIsomorphism F-set P-set (εε F) ]
--   εε-is-iso-on-stone-locales =
--     ∥∥-rec (isProp[] (isIsomorphism F-set P-set (εε F))) nts (π₁ stone)
--     where
--     nts : Σ[ ℬ ∈ Fam 𝓤 ∣ F ∣F ] (isBasisFor F ℬ × isComplemented F ℬ)
--         → [ isIsomorphism F-set P-set (εε F) ]
--     nts (ℬ , b , comp) = G𝟏 , G𝟐
--       where
--       postulate F-spec : isSpectral′ F

--       basis : hasBasis F
--       basis = directify F ℬ , directified-basis-gives-basis F ℬ b

--       open SomeMoreResults F F-spec basis renaming (Patch′ to Patch′-F)
--       open AdjointFunctorTheorem F Patch′-F

--       ε* : ∣ Patch F ∣F → ∣ F ∣F
--       ε* = RA-of-homo basis δδδ

--       G𝟏 : [ isInjective F-set P-set (εε F) ]
--       G𝟏 = {!ε-is-mono F Patch′-F F-spec !}

--       G𝟐 : [ isSurjective F-set P-set (εε F) ]
--       G𝟐 𝒿 = {!!}
```
