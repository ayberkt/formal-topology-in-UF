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
open import RightAdjoint hiding (hasBasis)
open import Regular
open import Cubical.Data.List hiding ([_])
open import HeytingImplication hiding (formsBasis)
open import Cubical.Foundations.Function using (uncurry)
```
-->

```agda
module PatchFrameNucleusLemma (F : Frame (𝓤 ⁺) 𝓤 𝓤) (spec′ : isSpectral′ F) where

  𝕨 : hasBasis F → (G : Frame (𝓤 ⁺) 𝓤 𝓤) → hasBasis G → (f : ∣ F ∣F → ∣ G ∣F) → ∣ F ∣F → Fam 𝓤 ∣ G ∣F
  𝕨 (ℬ , p) G (ℬ′ , p′) f x = I , λ { (i , j , p) → ℬ′ $ j }
    where
    I : 𝓤 ̇
    I = Σ[ i  ∈ index ℬ ] Σ[ j ∈ index ℬ′ ]
          [ (ℬ $ i) ⊑[ pos F ] x ] × [ (ℬ′ $ j) ⊑[ pos G ] f (ℬ $ i) ]

  -- graph-thm : (bs : hasBasis F) (G : Frame (𝓤 ⁺) 𝓤 𝓤) → isSpectral′ G → (bs′ : hasBasis G)
  --           → (f : ∣ F ∣F → ∣ G ∣F) → isScottContinuous F G f
  --           → (x : ∣ F ∣F) → [ _≪_ F x x ] → [ isSup (pos G) (𝕨 bs G bs′ f x) (f x) ]
  -- graph-thm bs G spec′ bs′ f f-sc = {!!}

  module Main (𝔹 : Σ[ ℬ ∈ Fam 𝓤 ∣ F ∣F ]
                     ((i : index ℬ) → [ isCompactOpen F (ℬ $ i) ])
                     × formsBasis F ℬ
                     × closedUnderFinMeets F ℬ) where

    ℬ = π₀ 𝔹
    open Complements F

    σ : isSpectral F
    σ = spec′→spec F ∣ 𝔹 ∣

    κ : (i : index ℬ) → [ isCompactOpen F (ℬ $ i) ]
    κ = π₀ (π₁ 𝔹)

    basis : hasBasis F
    basis = ℬ , π₀ (π₁ (π₁ 𝔹))

    ν : index ℬ → ∣ Patch F ∣F
    ν i = μ σ basis (ℬ $ i) (κ i) -- μ sp basis (ℬ $ i) (κ i)

    comp→basic : (x : ∣ F ∣F) → [ isCompactOpen F x ] → ∥ x ε ℬ ∥
    comp→basic x x≪x =
      ∥∥-rec (∥∥-prop (x ε ℬ)) nts (x≪x ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ (π₀ (π₁ (π₁ basis x))) (≡⇒⊑ (pos F) eq))
      where
      𝒥 : Fam 𝓤 (index ℬ)
      𝒥 = π₀ (π₁ basis x)

      eq : x ≡ ⋁[ F ] ⁅ ℬ $ j ∣ j ε 𝒥 ⁆
      eq = uncurry (⋁-unique F _ _) (π₁ (π₁ (π₁ basis x)))

      nts : Σ[ j ∈ index 𝒥 ] [ x ⊑[ pos F ] (ℬ $ (𝒥 $ j)) ]
          → ∥ x ε ℬ ∥
      nts (j , p) = ∣ (𝒥 $ j) , ⊑[ pos F ]-antisym _ _ nts₀ nts₁ ∣
        where
        nts₀ = subst (λ - → [ (ℬ $ (𝒥 $ j)) ⊑[ pos F ] - ]) (sym eq) (⋁[ F ]-upper _ _ (j , refl))

        nts₁ = p

    perfect-nucleus-lemma₀ : (j k : ∣ Patch F ∣F)
                            → ((x : ∣ F ∣F) → [ _≪_ F x x ] → [ π₀ (π₀ j) x ⊑[ pos F ] π₀ (π₀ k) x ])
                            → (x : ∣ F ∣F) → [ π₀ (π₀ j) x ⊑[ pos F ] π₀ (π₀ k) x ]
    perfect-nucleus-lemma₀ 𝒿@((j , j-n) , j-sc) 𝓀@((k , k-n) , k-sc) ρ x =
      j x                    ⊑⟨ ≡⇒⊑ (pos F) (cong j eq) ⟩
      j (⋁[ F ] W)           ⊑⟨ ≡⇒⊑ (pos F) (j-sc W W-dir) ⟩
      ⋁[ F ] ⁅ j w ∣ w ε W ⁆ ⊑⟨ nts ⟩
      ⋁[ F ] ⁅ k w ∣ w ε W ⁆ ⊑⟨ ≡⇒⊑ (pos F) (sym (k-sc W W-dir)) ⟩
      k (⋁[ F ] W)           ⊑⟨ ≡⇒⊑ (pos F) (cong k (sym eq)) ⟩
      k x                    ■
      where
      open PosetReasoning (pos F)

      W : Fam 𝓤 (π₀ F)
      W = ⁅ ℬ $ i ∣ i ε (π₀ (π₁ basis x)) ⁆

      W-dir : [ isDirected (pos F) W ]
      W-dir = π₀ (π₁ (π₁ basis x))

      eq : x ≡ ⋁[ F ] W
      eq = ⋁-unique F _ _ (π₀ (π₁ (π₁ (π₁ basis x)))) (π₁ (π₁ (π₁ (π₁ basis x))))

      goal : _
      goal z (i , eq)  = z                       ⊑⟨ ≡⇒⊑ (pos F) (sym eq)         ⟩
                          j (W $ i)               ⊑⟨ ρ (W $ i) (κ (π₀ (π₁ basis x) $ i)  ) ⟩
                          k (W $ i)               ⊑⟨ ⋁[ F ]-upper _ _ (i , refl)  ⟩
                          ⋁[ F ] ⁅ k w ∣ w ε W ⁆  ■

      nts = ⋁[ F ]-least _ _ goal

    last-step : (((j , _) , _) : ∣ Patch F ∣F)
              → (⋁[ Patch F ] ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆)
                ≡ (⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k
                                  ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ]
                                                  [ (ℬ $ i) ⊑[ pos F ] (j (ℬ $ k)) ] ⁆)
    last-step ((j , j-n) , j-sc)= ⊑[ pos (Patch F) ]-antisym _ _ G𝟏 G𝟐
      where
      open PosetReasoning (pos F)

      rhs-fam =
        ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ] [ (ℬ $ i) ⊑[ pos F ] (j (ℬ $ k)) ] ⁆

      G𝟏 : [ (⋁[ Patch F ] ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆)
           ⊑[ pos (Patch F) ]
           (⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k
                         ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ]
                                           [ (ℬ $ i) ⊑[ pos F ] (j (ℬ $ k)) ] ⁆)
           ]
      G𝟏 = ⋁[ Patch F ]-least _ ((⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ] [ (ℬ $ i) ⊑[ pos F ] (j (ℬ $ k)) ] ⁆)) G𝟏a
        where
        G𝟏a : (k : ∣ Patch F ∣F)
            → k ε ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆
            → [ k ⊑[ pos (Patch F) ] (⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ] [ (ℬ $ i) ⊑[ pos F ] (j (ℬ $ k)) ] ⁆) ]
        G𝟏a k (l , eq) = subst (λ - → [ - ⊑[ pos (Patch F) ] (⋁[ Patch F ] rhs-fam) ]) eq G𝟏b
          where
          G𝟏b : [ εε F (j (ℬ $ l)) ⊓[ Patch F ] ν l ⊑[ pos (Patch F) ] ⋁[ Patch F ] rhs-fam ]
          G𝟏b x = perfect-nucleus-lemma₀ (εε F (j (ℬ $ l)) ⊓[ Patch F ] ν l) (⋁[ Patch F ] rhs-fam) rem x
            where
            𝒦 : Fam 𝓤 (index ℬ)
            𝒦 = π₀ (π₁ basis (j (ℬ $ l)))

            eq₀ : j (ℬ $ l) ≡ ⋁[ F ] ⁅ ℬ $ k ∣ k ε 𝒦 ⁆
            eq₀ = uncurry (⋁-unique F _ _) (π₁ (π₁ (π₁ basis (j (ℬ $ l)))))

            rem : (w : ∣ F ∣F)
                → [ _≪_ F w w ]
                → [ (π₀ (π₀ ((εε F (j (ℬ $ l))) ⊓[ Patch F ] (ν l))) w) ⊑[ pos F ] (π₀ (π₀ (⋁[ Patch F ] rhs-fam)) w) ]
            rem w w≪w = εε F (j (ℬ $ l)) .π₀ .π₀ w ⊓[ F ] ν l .π₀ .π₀ w                        ⊑⟨ ≡⇒⊑ (pos F) (cong (λ - → glb-of F (εε F - .π₀ .π₀ w) (ν l .π₀ .π₀ w)) eq₀) ⟩
                        εε F (⋁[ F ] ⁅ ℬ $ k ∣ k ε 𝒦 ⁆) .π₀ .π₀ w ⊓[ F ] ν l .π₀ .π₀ w         ⊑⟨ ⦅𝟏⦆ ⟩
                        (⋁[ Patch F ] ⁅ εε F (ℬ $ k) ∣ k ε 𝒦 ⁆) .π₀ .π₀ w ⊓[ F ] ν l .π₀ .π₀ w ⊑⟨ ⦅𝟐⦆ ⟩
                        (⋁[ F ] ⁅ εε F (ℬ $ k) .π₀ .π₀ w ∣ k ε 𝒦 ⁆) ⊓[ F ] ν l .π₀ .π₀ w       ⊑⟨ ≡⇒⊑ (pos F) (comm F (⋁[ F ] ⁅ εε F (ℬ $ k) .π₀ .π₀ w ∣ k ε 𝒦 ⁆) (ν l .π₀ .π₀ w)) ⟩
                        ν l .π₀ .π₀ w ⊓[ F ] (⋁[ F ] ⁅ εε F (ℬ $ k) .π₀ .π₀ w ∣ k ε 𝒦 ⁆)       ⊑⟨ ≡⇒⊑ (pos F) (dist F (ν l .π₀ .π₀ w) ⁅ εε F (ℬ $ k) .π₀ .π₀ w ∣ k ε 𝒦 ⁆) ⟩
                        (⋁[ F ] ⁅ ν l .π₀ .π₀ w ⊓[ F ] (εε F (ℬ $ k) .π₀ .π₀ w) ∣ k ε 𝒦 ⁆)     ⊑⟨ ≡⇒⊑ (pos F) (cong (λ - → ⋁[ F ] (index 𝒦 , -)) (funExt λ k → comm F (ν l .π₀ .π₀ w) (εε F _ .π₀ .π₀ w))) ⟩
                        (⋁[ F ] ⁅ (εε F (ℬ $ k) .π₀ .π₀ w) ⊓[ F ] ν l .π₀ .π₀ w ∣ k ε 𝒦 ⁆)     ⊑⟨ final ⟩
                        (⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ] [ (ℬ $ i) ⊑[ pos F ] (j (ℬ $ k)) ] ⁆) .π₀ .π₀ w  ⊑⟨ ⊑[ pos F ]-refl _ ⟩
                        (⋁[ Patch F ] rhs-fam) .π₀ .π₀ w                                       ■
              where
              dir : [ isDirected (pos (Patch F)) ⁅ εε F (ℬ $ k) ∣ k ε 𝒦 ⁆ ]
              dir = directed-image-lemma (pos F) (pos (Patch F)) (εε F , εε-mono F) _ (π₀ (π₁ (π₁ basis (j (ℬ $ l)))))

              ⦅𝟏⦆ = ≡⇒⊑ (pos F) (cong (λ - → - ⊓[ F ] ν l .π₀ .π₀ w) (ScottContNucleus-eq⁻ F _ _ (εε-resp-⋁ F ⁅ ℬ $ k ∣ k ε 𝒦 ⁆) w))
              ⦅𝟐⦆ = ≡⇒⊑ (pos F) (cong (λ - → - ⊓[ F ] ν l .π₀ .π₀ w) (directed-computed-pointwise F ⁅ εε F (ℬ $ k) ∣ k ε 𝒦 ⁆ dir w))

              final : _
              final = ⋁[ F ]-least _ _ nts
                where
                nts : (z : ∣ F ∣F)
                    → z ε ⁅ (εε F (ℬ $ k) .π₀ .π₀ w) ⊓[ F ] ν l .π₀ .π₀ w ∣ k ε 𝒦 ⁆
                    → [ z ⊑[ pos F ] (⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ] [ (ℬ $ i) ⊑[ pos F ] (j (ℬ $ k)) ] ⁆) .π₀ .π₀ w ]
                nts z (v , υ) =
                  z    ⊑⟨ ≡⇒⊑ (pos F) (sym υ) ⟩
                  εε F (ℬ $ (𝒦 $ v)) .π₀ .π₀ w ⊓[ F ] ν l .π₀ .π₀ w ⊑⟨ ⋁[ F ]-upper _ _ goal ⟩
                  (⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ] [ (ℬ $ i) ⊑[ pos F ] (j (ℬ $ k)) ] ⁆) .π₀ .π₀ w ■
                  where
                  goal′ : [ (ℬ $ (𝒦 $ v)) ⊑[ pos F ] j (ℬ $ l) ]
                  goal′ = ℬ $ (𝒦 $ v)              ⊑⟨ ⋁[ F ]-upper _ _ (v , refl) ⟩
                          ⋁[ F ] ⁅ ℬ $ k ∣ k ε 𝒦 ⁆ ⊑⟨ ≡⇒⊑ (pos F) (sym eq₀)       ⟩
                          j (ℬ $ l)                ■

                  goal = (𝒦 $ v , (l  , goal′)) ∷ [] , refl

      G𝟐 : [ (⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k
                         ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ]
                                           [ (ℬ $ i) ⊑[ pos F ] (j (ℬ $ k)) ] ⁆)
             ⊑[ pos (Patch F) ]
             (⋁[ Patch F ] ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆) ]
      G𝟐 = ⋁[ Patch F ]-least _ (⋁[ Patch F ] ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆) G𝟐a
        where
        G𝟐a : [ ∀[ w ε ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ] [ (ℬ $ i) ⊑[ pos F ] (j (ℬ $ k)) ] ⁆ ]
                  (w ⊑[ pos (Patch F) ] (⋁[ Patch F ] ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆)) ]
        G𝟐a w ((k , l , p) , eq) x =
          subst (λ - → [ - .π₀ .π₀ x ⊑[ pos F ] (⋁[ Patch F ] ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆) .π₀ .π₀ x ]) eq G𝟐b
          where
          G𝟐b : [ εε F (ℬ $ k) .π₀ .π₀ x ⊓[ F ] ν l .π₀ .π₀ x ⊑[ pos F ] (⋁[ Patch F ] ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆) .π₀ .π₀ x ]
          G𝟐b = perfect-nucleus-lemma₀ (εε F (ℬ $ k) ⊓[ Patch F ] ν l) (⋁[ Patch F ] ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆) G𝟐c x
            where
            G𝟐c : (c : ∣ F ∣F)
                → [ _≪_ F c c ]
                → [ εε F (ℬ $ k) .π₀ .π₀ c ⊓[ F ] ν l .π₀ .π₀ c ⊑[ pos F ] (⋁[ Patch F ] ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆) .π₀ .π₀ c ]
            G𝟐c c c≪c = εε F (ℬ $ k) .π₀ .π₀ c ⊓[ F ] ν l .π₀ .π₀ c                                  ⊑⟨ cleft F (ν l .π₀ .π₀ c) ⦅𝟏⦆ ⟩
                        εε F (j (ℬ $ l)) .π₀ .π₀ c ⊓[ F ] ν l .π₀ .π₀ c                              ⊑⟨ final                       ⟩
                        (⋁[ Patch F ] ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆) .π₀ .π₀ c ■
              where
              ⦅𝟏⦆ : [ εε F (ℬ $ k) .π₀ .π₀ c ⊑[ pos F ] εε F (j (ℬ $ l)) .π₀ .π₀ c ]
              ⦅𝟏⦆ = εε-mono F (ℬ $ k) (j (ℬ $ l)) p c


              final : [ εε F (j (ℬ $ l)) .π₀ .π₀ c ⊓[ F ] ν l .π₀ .π₀ c ⊑[ pos F ] ((⋁[ Patch F ] ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆) .π₀ .π₀ c) ]
              final = ⋁[ F ]-upper _ _ (l ∷ [] , refl)

    johnstones-lemma : (𝒿 : ∣ Patch F ∣F)
                     → 𝒿 ≡ ⋁[ Patch F ] ⁅ εε F (𝒿 .π₀ .π₀ (ℬ $ i)) ⊓[ Patch F ] μ σ basis (ℬ $ i) (κ i) ∣ i ∶ index ℬ ⁆
    johnstones-lemma 𝒿@((j , j-n@(𝓃₀ , 𝓃₁ , 𝓃₂)) , j-sc) = G𝟐′
      where
      open PosetReasoning (pos F)
      open Definition F basis hiding (ℬ)

      𝕜 : index ℬ → ∣ Patch F ∣F
      𝕜 i = εε F (j (ℬ $ i)) ⊓[ Patch F ] μ σ basis (ℬ $ i) (κ i)

      𝕜₀ : index ℬ → ∣ F ∣F → ∣ F ∣F
      𝕜₀ i x = π₀ (π₀ (𝕜 i)) x

      foo : (i : index ℬ) → 𝕜₀ i (ℬ $ i) ≡ j (ℬ $ i)
      foo i =
        π₀ (π₀ (𝕜 i)) (ℬ $ i)                                   ≡⟨ refl                             ⟩
        (j (ℬ $ i) ∨[ F ] (ℬ $ i)) ⊓[ F ] ((ℬ $ i) ==> (ℬ $ i)) ≡⟨ ⦅𝟏⦆                              ⟩
        (j (ℬ $ i) ∨[ F ] (ℬ $ i)) ⊓[ F ] ⊤[ F ]                ≡⟨ cong (λ - → - ⊓[ F ] ⊤[ F ]) ⦅𝟐⦆ ⟩
        j (ℬ $ i) ⊓[ F ] ⊤[ F ]                                 ≡⟨ x∧⊤=x F (j (ℬ $ i))              ⟩
        j (ℬ $ i)                                               ∎
        where
        ⦅𝟏⦆ : _
        ⦅𝟏⦆ = cong (λ - → (j (ℬ $ i) ∨[ F ] (ℬ $ i)) ⊓[ F ] -) (==>-id (ℬ $ i))

        ⦅𝟐⦆ : j (ℬ $ i) ∨[ F ] (ℬ $ i) ≡ j (ℬ $ i)
        ⦅𝟐⦆ = ⊑[ pos F ]-antisym _ _ ⦅𝟐a⦆ ⦅𝟐b⦆
          where
          ⦅𝟐a⦆ : [ j (ℬ $ i) ∨[ F ] (ℬ $ i) ⊑[ pos F ] j (ℬ $ i) ]
          ⦅𝟐a⦆ = ⋁[ F ]-least _ _ nts
            where
            nts : [ ∀[ x ε ⁅ j (ℬ $ i) , (ℬ $ i) ⁆ ] (x ⊑[ pos F ] j (ℬ $ i)) ]
            nts x (true  , eq) = subst (λ - → [ - ⊑[ pos F ] j (ℬ $ i) ]) eq (⊑[ pos F ]-refl _)
            nts x (false , eq) =
              x         ⊑⟨ ≡⇒⊑ (pos F) (sym eq) ⟩
              ℬ $ i     ⊑⟨ 𝓃₁ (ℬ $ i) ⟩
              j (ℬ $ i) ■

          ⦅𝟐b⦆ : [ j (ℬ $ i) ⊑[ pos F ] j (ℬ $ i) ∨[ F ] (ℬ $ i) ]
          ⦅𝟐b⦆ = ⋁[ F ]-upper _ (j (ℬ $ i)) (true , refl)

      lemma-js : (i : index ℬ) → [ 𝕜 i ⊑[ pos (Patch F) ] 𝒿 ]
      lemma-js i x =
        𝕜₀ i x                                                     ⊑⟨ ⊑[ pos F ]-refl _ ⟩
        (j (ℬ $ i) ∨[ F ] x) ⊓[ F ] ((ℬ $ i) ==> x)                ⊑⟨ ⦅𝟏⦆               ⟩
        (j (ℬ $ i) ∨[ F ] x) ⊓[ F ] ((j (ℬ $ i) ∨[ F ] x) ==> j x) ⊑⟨ mp _ _            ⟩
        j x                                                        ■
        where
        ⦅𝟏b⦆ : [ ⊤[ F ] ⊑[ pos F ] (x ==> j x) ]
        ⦅𝟏b⦆ = π₁ (==>-is-HI x (j x) ⊤[ F ])
                (x ⊓[ F ] ⊤[ F ] ⊑⟨ ⊓[ F ]-lower₀ _ _ ⟩ x ⊑⟨ 𝓃₁ x ⟩ j x ■)

        ⦅𝟏a⦆ : [ ((ℬ $ i) ==> x) ⊑[ pos F ] ((j (ℬ $ i) ∨[ F ] x) ==> j x) ]
        ⦅𝟏a⦆ =
          (ℬ $ i) ==> x                          ⊑⟨ ==>-nucleus-lemma (ℬ $ i) x (j , j-n)           ⟩
          j (ℬ $ i) ==> j x                      ⊑⟨ ≡⇒⊑ (pos F) (sym (x∧⊤=x F (j (ℬ $ i) ==> j x))) ⟩
          (j (ℬ $ i) ==> j x) ⊓[ F ] ⊤[ F ]      ⊑⟨ cright F (j (ℬ $ i) ==> j x) ⦅𝟏b⦆               ⟩
          (j (ℬ $ i) ==> j x) ⊓[ F ] (x ==> j x) ⊑⟨ ==>-∨-lemma (j (ℬ $ i)) x (j x) ⟩
          (j (ℬ $ i) ∨[ F ] x) ==> j x           ■

        ⦅𝟏⦆ : _
        ⦅𝟏⦆ = cright F _ ⦅𝟏a⦆

      k : ∣ Patch F ∣F
      k = ⋁[ Patch F ] ⁅ 𝕜 i ∣ i ∶ index ℬ ⁆

      G𝟐′ : 𝒿 ≡ (⋁[ Patch F ] ⁅ 𝕜 i ∣ i ∶ index ℬ ⁆)
      G𝟐′ = ⋁-unique (Patch F) _ _ G𝟐′a G𝟐′b
        where
        G𝟐′a : [ ∀[ z ε ⁅ 𝕜 i ∣ i ∶ index ℬ ⁆ ] (z ⊑[ pos (Patch F) ] 𝒿) ]
        G𝟐′a z (i , eq) = subst (λ - → [ - ⊑[ pos (Patch F) ] 𝒿 ]) eq (lemma-js i)

        G𝟐′b : (𝓀 : ∣ (Patch F) ∣F)
              → [ ∀[ z ε ⁅ 𝕜 i ∣ i ∶ index ℬ ⁆ ] (z ⊑[ pos (Patch F) ] 𝓀) ]
              → [ 𝒿 ⊑[ pos (Patch F) ] 𝓀 ]
        G𝟐′b 𝓀@((k , k-n) , k-sc) θ x = perfect-nucleus-lemma₀ 𝒿 𝓀 ξ x
          where
          ξ : (y : ∣ F ∣F) → [ _≪_ F y y ] → [ j y ⊑[ pos F ] k y ]
          ξ y y-comp = ∥∥-rec (isProp[] (_ ⊑[ pos F ] _)) final (y-comp ((fmap (λ i → ℬ $ i)) 𝒥) 𝒥-dir cover)
            where
            𝒥 : Fam 𝓤 (index ℬ)
            𝒥 = π₀ (π₁ basis y)

            υ : [ isSup (pos F) ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ y ]
            υ = π₁ (π₁ (π₁ basis y))

            cover : [ y ⊑[ pos F ] ⋁[ F ] ⁅ ℬ $ i ∣ i ε 𝒥 ⁆ ]
            cover = ≡⇒⊑ (pos F) (⋁-unique F _ _ (π₀ υ) (π₁ υ))

            𝒥-dir : [ isDirected (pos F) ⁅ ℬ $ i ∣ i ε 𝒥 ⁆ ]
            𝒥-dir = π₀ (π₁ (π₁ basis y))

            final : _ → [ j y ⊑[ pos F ] k y ]
            final (𝒾 , p) = subst (λ - → [ j - ⊑[ pos F ] k - ]) eq rem
              where
              iy : index ℬ
              iy = π₀ (π₁ basis y) $ 𝒾

              eq : ℬ $ iy ≡ y
              eq = ⊑[ pos F ]-antisym _ _ eq₀ p
                where
                eq₀ : [ (ℬ $ iy) ⊑[ pos F ] y ]
                eq₀ = ℬ $ iy                   ⊑⟨ ⋁[ F ]-upper _ _ (𝒾 , refl) ⟩
                      ⋁[ F ] ⁅ ℬ $ i ∣ i ε 𝒥 ⁆ ⊑⟨ ≡⇒⊑ (pos F) (sym (⋁-unique F _ _ (π₀ υ) (π₁ υ))) ⟩
                      y                        ■

              goal : [ 𝕜₀ iy (ℬ $ iy) ⊑[ pos F ] k (ℬ $ iy) ]
              goal = θ (𝕜 iy) (iy , refl) (ℬ $ iy)

              rem : [ j (ℬ $ iy) ⊑[ pos F ] k (ℬ $ iy) ]
              rem = j (ℬ $ iy)     ⊑⟨ ≡⇒⊑ (pos F) (sym (foo iy)) ⟩
                    𝕜₀ iy (ℬ $ iy) ⊑⟨ goal                       ⟩
                    k (ℬ $ iy)     ■
```

```agda
    the-nucleus-lemma : (𝒿 : ∣ Patch F ∣F)
                      → 𝒿 ≡ ⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ] [ (ℬ $ i) ⊑[ pos F ] (𝒿 .π₀ .π₀ (ℬ $ k)) ] ⁆
    the-nucleus-lemma 𝒿@((j , _) , _) =
      𝒿                                                                   ≡⟨ johnstones-lemma 𝒿 ⟩
      ⋁[ Patch F ] ⁅ εε F (j (ℬ $ i)) ⊓[ Patch F ] ν i ∣ i ∶ index ℬ ⁆    ≡⟨ last-step 𝒿 ⟩
      ⋁[ Patch F ] ⁅ εε F (ℬ $ i) ⊓[ Patch F ] ν k
                     ∣ (i , k , _) ∶ Σ[ i ∈ index ℬ ] Σ[ k ∈ index ℬ ]
                                       [ (ℬ $ i) ⊑[ pos F ] j (ℬ $ k) ] ⁆ ∎
```
-->
