```agda
{-# OPTIONS --cubical --experimental-lossy-unification #-}

module Naturality where

open import Poset
open import Frame
open import Basis
open import PatchFrame
open import Spectral
open import ClosedNuclei
open import HeytingImplication
open import Basis
open import AdditionalFrameTheorems
open import WayBelow hiding (_≤_)
open import Cubical.Foundations.Function using (uncurry)
```

```agda
𝒪 : Frame 𝓤 𝓥 𝓦 → Frame 𝓤 𝓥 𝓦
𝒪 A = A

module NaturalityProof (A B     : Frame (𝓤 ⁺) 𝓤 𝓤)
                       (A-spec  : isSpectralₛ A)
                       (B-spec  : isSpectralₛ B) where

  ℬA : Fam 𝓤 ∣ A ∣F
  ℬA = π₀ A-spec

  A-basis : hasBasis A
  A-basis = ℬA , π₀ (π₁ (π₁ A-spec))

  ℬB : Fam 𝓤 ∣ B ∣F
  ℬB = π₀ B-spec

  B-basis : hasBasis B
  B-basis = ℬB , π₀ (π₁ (π₁ B-spec))

  compacts-are-basic : (U : ∣ B ∣F) → [ _≪_ B U U ] → ∥ U ε ℬB ∥
  compacts-are-basic U κ =
    ∥∥-rec (∥∥-prop (U ε ℬB)) γ (κ ⁅ ℬB $ i ∣ i ε ℐ ⁆  d W◂ℐ)
      where
      open PosetReasoning (pos B)

      ℐ : Fam 𝓤 (index ℬB)
      ℐ = π₀ (π₁ B-basis U)

      d : [ isDirected (pos B) ⁅ ℬB $ i ∣ i ε ℐ ⁆ ]
      d = π₀ (π₁ (π₁ B-basis U))

      W◂ℐ : [ U ⊑[ pos B ] ⋁[ B ] ⁅ ℬB $ i ∣ i ε ℐ ⁆ ]
      W◂ℐ = ≡⇒⊑ (pos B) (uncurry (⋁-unique B _ _) (π₁ (π₁ (π₁ B-basis U))))

      γ : Σ[ i ∈ index ℐ ] [ U ⊑[ pos B ] (ℬB $ ℐ $ i) ] → ∥ U ε ℬB ∥
      γ (i , p) = ∣ (ℐ $ i) , (⊑[ pos B ]-antisym _ _ δ p) ∣
        where
        δ : [ (ℬB $ (ℐ $ i)) ⊑[ pos B ] U ]
        δ = ℬB $ ℐ $ i ⊑⟨ ⋁[ B ]-upper _ _ (i , refl) ⟩
            ⋁[ B ] ⁅ ℬB $ i ∣ i ε ℐ ⁆ ⊑⟨ ≡⇒⊑ (pos B) (sym (uncurry (⋁-unique B _ _) (π₁ (π₁ (π₁ B-basis U))))) ⟩
            U ■

  ⊥εℬB : ∥ ⊥[ B ] ε ℬB ∥
  ⊥εℬB = compacts-are-basic ⊥[ B ] (⊥-compact B)

  open OpenNuclei A

  ∣εA⋆∣ : ∣ 𝒪 A ∣F → ∣ 𝒪 (Patch A) ∣F
  ∣εA⋆∣ = εε A

  ∣εB⋆∣ : ∣ 𝒪 B ∣F → ∣ 𝒪 (Patch B) ∣F
  ∣εB⋆∣ = εε B

  open Complements

  ∣ηA⋆∣ : (U : ∣ 𝒪 A ∣F) → [ _≪_ A U U ] → ∣ 𝒪 (Patch A) ∣F
  ∣ηA⋆∣ U p = μ A ∣ A-spec ∣ A-basis U p

  η⊥=⊤ : ∣ηA⋆∣ ⊥[ A ] (⊥-compact A) ≡ ⊤[ Patch A ]
  η⊥=⊤ = ⊑[ pos (Patch A) ]-antisym _ _ β γ
    where
    open Definition A A-basis using (mp; _==>_; ex-falso-quodlibet)
    open PosetReasoning (pos A)

    β : [ ∣ηA⋆∣ ⊥[ A ] (⊥-compact A) ⊑[ pos (Patch A) ] ⊤[ Patch A ] ]
    β = ⊤[ Patch A ]-top (∣ηA⋆∣ ⊥[ A ] (⊥-compact A))

    γ : [ ⊤[ Patch A ] ⊑[ pos (Patch A) ] ∣ηA⋆∣ ⊥[ A ] (⊥-compact A) ]
    γ x = ⊤[ A ] ⊑⟨ ≡⇒⊑ (pos A) (sym (ex-falso-quodlibet x)) ⟩ ⊥[ A ] ==> x ■

  η-comp-ε : (U : ∣ 𝒪 A ∣F) (p : [ _≪_ A U U ])
           → ∣εA⋆∣ U ⊓[ Patch A ] ∣ηA⋆∣ U p ≡ ⊥[ Patch A ]
  η-comp-ε U p =
    ScottContNucleus-eq A (∣εA⋆∣ U ⊓[ Patch A ] ∣ηA⋆∣ U p) ⊥[ Patch A ] (funExt †)
    where
    † : _
    † = ScottContNucleus-eq⁻ A _ _ (π₀ (complement-thm′ A ∣ A-spec ∣ A-basis U p))

  κ : (i : index ℬB) → [ _≪_ B (ℬB $ i) (ℬB $ i) ]
  κ = π₀ (π₁ B-spec)

  𝒦 : ∣ Patch B ∣F → Type 𝓤
  𝒦 ((j , _) , _) =
    Σ[ k ∈ index ℬB ] Σ[ l ∈ index ℬB ] [ (ℬB $ k) ⊑[ pos B ] j (ℬB $ l) ]

  -- Approximation of bar notation.
  bar : (f⋆ : 𝒪 B ─f→ 𝒪 A) → [ isSpectralMap B A f⋆ ] → ∣ 𝒪 (Patch B) ∣F → ∣ 𝒪 (Patch A) ∣F
  bar f⋆@((f , _) , _) f-spec 𝒿 = ⋁[ Patch A ] ℱ
    where
    ℱ : Fam 𝓤 ∣ Patch A ∣F
    ℱ = ⁅ ∣εA⋆∣ (f (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f (ℬB $ l)) (f-spec (ℬB $ l) (κ l))
          ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆

  naturality : (f⋆ : 𝒪 B ─f→ 𝒪 A) (f-spec : [ isSpectralMap B A f⋆ ])
             → (W : ∣ 𝒪 B ∣F) → ∣εA⋆∣ (f⋆ .π₀ .π₀ W) ≡ bar f⋆ f-spec (∣εB⋆∣ W)
  naturality 𝒻⋆@((f⋆ , f-mono) , (_ , _ , f⋁)) f-spec W = nts
    where
    open PosetNotation  (pos (Patch A)) using (_≤_)
    open PosetReasoning (pos (Patch A)) using (_⊑⟨_⟩_; _■)
    open PosetReasoning (pos A)         renaming (_⊑⟨_⟩_ to _≤⟨_⟩_; _■ to _■ₐ)

    𝒿 : ∣ Patch B ∣F
    𝒿 = ∣εB⋆∣ W

    ℱ : Fam 𝓤 ∣ Patch A ∣F
    ℱ = ⁅ ∣εA⋆∣ (f⋆ (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l))
          ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆

    ℐ : Fam 𝓤 (index ℬB)
    ℐ = π₀ (π₁ B-basis W)

    W◀ℐ : W ≡ ⋁[ B ] ⁅ (ℬB $ i) ∣ i ε ℐ ⁆
    W◀ℐ = uncurry (⋁-unique B ⁅ (ℬB $ i) ∣ i ε ℐ ⁆ W) (π₁ (π₁ (π₁ B-basis W)))

    up : [ (⋁[ Patch A ] ℱ) ≤ ∣εA⋆∣ (f⋆ W) ]
    up x = (⋁[ Patch A ] ℱ) .π₀ .π₀ x
           ≤⟨ ⊑[ pos (Patch A) ]-refl (⋁[ Patch A ] ℱ) x ⟩
         (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) .π₀ .π₀ x
           ≤⟨ ⦅𝟏⦆ x ⟩
         (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (W ∨[ B ] (ℬB $ l))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) .π₀ .π₀ x
           ≤⟨ ⦅𝟐⦆ x ⟩
         (⋁[ Patch A ] ⁅ ∣εA⋆∣ ((f⋆ W) ∨[ A ] (f⋆ (ℬB $ l))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) .π₀ .π₀ x
           ≤⟨ ⦅𝟑⦆ x ⟩
         (⋁[ Patch A ] ⁅ ((∣εA⋆∣ ((f⋆ W))) ∨[ Patch A ] (∣εA⋆∣ (f⋆ (ℬB $ l)))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) .π₀ .π₀ x
           ≤⟨ ⦅𝟑′⦆ x ⟩
         (⋁[ Patch A ] ⁅ ((∣εA⋆∣ ((f⋆ W))) ⊓[ Patch A ] (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l))))
                        ∨[ Patch A ]
                        ((∣εA⋆∣ (f⋆ (ℬB $ l))) ⊓[ Patch A ] (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)))) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) .π₀ .π₀ x
           ≤⟨ ⦅𝟒⦆ x ⟩
         (⋁[ Patch A ] ⁅ ((∣εA⋆∣ ((f⋆ W))) ⊓[ Patch A ] (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l))))
                        ∨[ Patch A ]
                        ⊥[ Patch A ] ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) .π₀ .π₀ x                                                                   ≤⟨ ⦅𝟓⦆ x ⟩
         (⋁[ Patch A ] ⁅ ((∣εA⋆∣ ((f⋆ W))) ⊓[ Patch A ] (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)))) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) .π₀ .π₀ x ≤⟨ ⦅𝟔⦆ x ⟩
         (∣εA⋆∣ ((f⋆ W)) ⊓[ Patch A ] (⋁[ Patch A ] ⁅ (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l))) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆)) .π₀ .π₀ x   ≤⟨ ⊓[ Patch A ]-lower₀ (∣εA⋆∣ ((f⋆ W))) ((⋁[ Patch A ] ⁅ (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l))) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆)) x ⟩
         ∣εA⋆∣ ((f⋆ W)) .π₀ .π₀ x           ■ₐ
         where
           ⦅𝟏⦆ : [ (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) ⊑[ pos (Patch A) ] (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (W ∨[ B ] (ℬB $ l))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) ]
           ⦅𝟏⦆  = ⋁[ Patch A ]-least
                    (⁅ ∣εA⋆∣ (f⋆ (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆)
                    ((⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (W ∨[ B ] (ℬB $ l))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆)) p
                    where
                    p : _
                    p _ ((k , l , r) , eq) = subst
                                     (λ - →
                                        [ rel (pos (Patch A)) - ((⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (W ∨[ B ] (ℬB $ l))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆)) ])
                                     eq q
                      where
                      nts : [ ∣εA⋆∣ (f⋆ (ℬB $ k)) ⊑[ pos (Patch A) ] ∣εA⋆∣ (f⋆ (W ∨[ B ] (ℬB $ l))) ]
                      nts = εε-mono A (f⋆ (ℬB $ k)) (f⋆ (W ∨[ B ] (ℬB $ l))) (f-mono _ _ r)

                      q : [ (∣εA⋆∣ (f⋆ (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)))
                            ⊑[ pos (Patch A) ]
                            (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (W ∨[ B ] (ℬB $ l))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆)
                          ]
                      q x = ((∣εA⋆∣ (f⋆ (ℬB $ k))) ⊓[ Patch A ] (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)))) .π₀ .π₀ x
                            ≤⟨ cleft (Patch A) (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l))) {x = ∣εA⋆∣ (f⋆ (ℬB $ k))} {∣εA⋆∣ (f⋆ (W ∨[ B ] (ℬB $ l)))} nts x ⟩
                          ((∣εA⋆∣ (f⋆ (W ∨[ B ] (ℬB $ l)))) ⊓[ Patch A ] (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)))) .π₀ .π₀ x
                            ≤⟨ ⋁[ Patch A ]-upper
                                 (⁅ ∣εA⋆∣ (f⋆ (W ∨[ B ] (ℬB $ l))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆)
                                 (∣εA⋆∣ (f⋆ (W ∨[ B ] (ℬB $ l))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l))) ((k , l , r) , refl) x ⟩
                          (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (W ∨[ B ] (ℬB $ l))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) .π₀ .π₀ x ■ₐ

           ⦅𝟐⦆  = ≡⇒⊑ (pos (Patch A)) (cong (λ - → ⋁[ Patch A ] (𝒦 𝒿 , -)) (funExt p))
                    where
                    p : _
                    p (k , l , r) = cong (λ - → (∣εA⋆∣ -) ⊓[ Patch A ] (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)))) nts
                      where
                      nts = f⋆ (W ∨[ B ] (ℬB $ l))      ≡⟨ f⋁ (⁅ W , (ℬB $ l) ⁆) ⟩
                            _                           ≡⟨ cong (λ - → ⋁[ A ] -) (⁅⁆-distr W (ℬB $ l) f⋆) ⟩
                            (f⋆ W) ∨[ A ] (f⋆ (ℬB $ l)) ∎
           ⦅𝟑⦆  = ≡⇒⊑ (pos (Patch A)) (cong (λ - → ⋁[ Patch A ] (𝒦 𝒿 , -)) (funExt p))
                    where
                    p : _
                    p (k , l , r) = cong (λ - → - ⊓[ Patch A ] (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)))) (εε-resp-∨ A (f⋆ W) (f⋆ (ℬB $ l)))
           ⦅𝟑′⦆ = ≡⇒⊑ (pos (Patch A)) (cong (λ - → ⋁[ Patch A ] (𝒦 𝒿 , -)) (funExt p))
                    where
                    p : _
                    p (k , l , r) = bin-dist′ (Patch A) (∣εA⋆∣ ((f⋆ W))) (∣εA⋆∣ (f⋆ (ℬB $ l))) (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)))
           ⦅𝟒⦆  = ≡⇒⊑ (pos (Patch A)) (cong (λ - → ⋁[ Patch A ] (𝒦 𝒿 , -)) (funExt p))
                    where
                    p : _
                    p (k , l , r) = cong (λ - → ((∣εA⋆∣ ((f⋆ W))) ⊓[ Patch A ] (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)))) ∨[ Patch A ] -) (η-comp-ε (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)))
           ⦅𝟓⦆  = ≡⇒⊑ (pos (Patch A)) (cong (λ - → ⋁[ Patch A ] (𝒦 𝒿 , -)) (funExt p))
                    where
                    p : _
                    p (k , l , r) = ((∣εA⋆∣ ((f⋆ W))) ⊓[ Patch A ] (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)))) ∨[ Patch A ] ⊥[ Patch A ] ≡⟨ ⊥∨x=x (Patch A) _ ⟩
                                    (∣εA⋆∣ (f⋆ W)) ⊓[ Patch A ] (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l))) ∎
           ⦅𝟔⦆  = ≡⇒⊑ (pos (Patch A)) (sym (dist (Patch A) (∣εA⋆∣ (f⋆ W)) (⁅ (∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l))) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆)))

    cool-lemma : ∥ ⊥[ B ] ε ℬB ∥
               → [ (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ i)) ∣ i ε ℐ ⁆) ⊑[ pos (Patch A) ] (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) ]
    cool-lemma = ∥∥-rec
                   (isProp[] ((⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ i)) ∣ i ε ℐ ⁆) ⊑[ pos (Patch A) ] (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆))) γ
                 where
                   γ : Σ[ k ∈ index ℬB ] (ℬB $ k) ≡ ⊥[ B ]
                     → [ (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ i)) ∣ i ε ℐ ⁆)
                         ⊑[ pos (Patch A) ]
                         (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆)
                       ]
                   γ (i⊥ , eq) x =
                     (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ i)) ∣ i ε ℐ ⁆) .π₀ .π₀ x                                                                      ≤⟨ ⦅𝟏⦆ x ⟩
                     (⋁[ Patch A ] ⁅ (∣εA⋆∣ (f⋆ (ℬB $ i))) ⊓[ Patch A ] ⊤[ Patch A ] ∣ i ε ℐ ⁆) .π₀ .π₀ x                                          ≤⟨ ⦅𝟐⦆ x ⟩
                     (⋁[ Patch A ] ⁅ (∣εA⋆∣ (f⋆ (ℬB $ i))) ⊓[ Patch A ] ∣ηA⋆∣ ⊥[ A ] (⊥-compact A) ∣ i ε ℐ ⁆) .π₀ .π₀ x                            ≤⟨ ⦅𝟑⦆ x ⟩
                     (⋁[ Patch A ] ⁅ (∣εA⋆∣ (f⋆ (ℬB $ i))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ ⊥[ B ]) (f-spec ⊥[ B ] (⊥-compact B)) ∣ i ε ℐ ⁆) .π₀ .π₀ x       ≤⟨ ⦅𝟒⦆ x ⟩
                     (⋁[ Patch A ] ⁅ (∣εA⋆∣ (f⋆ (ℬB $ i))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ i⊥)) (f-spec (ℬB $ i⊥) (κ i⊥)) ∣ i ε ℐ ⁆) .π₀ .π₀ x        ≤⟨ ⦅𝟓⦆ x ⟩
                     (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) .π₀ .π₀ x ■ₐ
                     where
                       open Definition A A-basis using (_==>_)

                       ⦅𝟏⦆ = ≡⇒⊑ (pos (Patch A)) (cong (λ - → (⋁[ Patch A ] (index ℐ , -))) (funExt λ i → sym (x∧⊤=x (Patch A) (∣εA⋆∣ (f⋆ (ℬB $ ℐ $ i))))))

                       ⦅𝟐⦆ = ≡⇒⊑ (pos (Patch A)) (cong (λ - → (⋁[ Patch A ] (index ℐ , -))) (funExt nts))
                               where
                               nts : _
                               nts i = cong (λ - → glb-of (Patch A) (∣εA⋆∣ (f⋆ (ℬB $ ℐ $ i))) -) (sym η⊥=⊤)

                       ⦅kk⦆ = ≡⇒⊑ (pos (Patch A)) (cong (λ - → (⋁[ Patch A ] (index ℐ , -))) (funExt λ i → cong (λ - → (∣εA⋆∣ (f⋆ (ℬB $ ℐ $ i))) ⊓[ Patch A ] -) δ))
                             where
                               † = ScottContNucleus-eq A (∣ηA⋆∣ ⊥[ A ] (⊥-compact A))
                                     (∣ηA⋆∣ (f⋆ ⊥[ B ]) (f-spec ⊥[ B ] (⊥-compact B)))
                                     (funExt λ x → (⊥[ A ] ==> x) ≡⟨ cong (_==> x) (sym (resp-⊥ B A 𝒻⋆)) ⟩ (f⋆ ⊥[ B ] ==> x) ∎)
                               ‡ = ScottContNucleus-eq A
                                     (∣ηA⋆∣ (f⋆ ⊥[ B ]) (f-spec ⊥[ B ] (⊥-compact B)))
                                     (∣ηA⋆∣ (f⋆ (ℬB $ i⊥)) (f-spec (ℬB $ i⊥) (κ i⊥)))
                                       (funExt λ x → (f⋆ ⊥[ B ] ==> x) ≡⟨ cong (λ - → (f⋆ -) ==> x) (sym eq) ⟩
                                                     (f⋆ (ℬB $ i⊥) ==> x) ∎)

                               δ : ⊤[ Patch A ] ≡ ∣ηA⋆∣ (f⋆ (ℬB $ i⊥)) (f-spec (ℬB $ i⊥) (κ i⊥))
                               δ = ⊤[ Patch A ]                                    ≡⟨ sym η⊥=⊤ ⟩
                                   ∣ηA⋆∣ ⊥[ A ] (⊥-compact A)                      ≡⟨ †   ⟩
                                   ∣ηA⋆∣ (f⋆ ⊥[ B ]) (f-spec ⊥[ B ] (⊥-compact B)) ≡⟨ ‡ ⟩
                                   ∣ηA⋆∣ (f⋆ (ℬB $ i⊥)) (f-spec (ℬB $ i⊥) (κ i⊥))  ∎

                       ⦅𝟑⦆ = ≡⇒⊑ (pos (Patch A)) (cong (λ - → (⋁[ Patch A ] (index ℐ , -))) (funExt λ i → cong (λ - → (∣εA⋆∣ (f⋆ (ℬB $ ℐ $ i))) ⊓[ Patch A ] -) δ))
                               where
                               δ = ScottContNucleus-eq A
                                     (∣ηA⋆∣ ⊥[ A ] (⊥-compact A))
                                     (∣ηA⋆∣ (f⋆ ⊥[ B ]) (f-spec ⊥[ B ] (⊥-compact B)))
                                     (funExt λ x → (⊥[ A ] ==> x) ≡⟨ cong (_==> x) (sym (resp-⊥ B A 𝒻⋆)) ⟩ (f⋆ ⊥[ B ] ==> x) ∎)

                       ⦅𝟒⦆ = ≡⇒⊑ (pos (Patch A)) (cong (λ - → (⋁[ Patch A ] (index ℐ , -))) (funExt λ i → cong (λ - → (∣εA⋆∣ (f⋆ (ℬB $ ℐ $ i))) ⊓[ Patch A ] -) δ))
                             where
                               δ = ScottContNucleus-eq A
                                     (∣ηA⋆∣ (f⋆ ⊥[ B ]) (f-spec ⊥[ B ] (⊥-compact B)))
                                     (∣ηA⋆∣ (f⋆ (ℬB $ i⊥)) (f-spec (ℬB $ i⊥) (κ i⊥)))
                                       (funExt λ x → (f⋆ ⊥[ B ] ==> x) ≡⟨ cong (λ - → (f⋆ -) ==> x) (sym eq) ⟩
                                                     (f⋆ (ℬB $ i⊥) ==> x) ∎)

                       ⦅𝟓⦆ = ⋁[ Patch A ]-least
                               ((fmap
                                 (λ i →
                                    glb-of (Patch A) (∣εA⋆∣ (f⋆ (ℬB $ i)))
                                    (∣ηA⋆∣ (f⋆ (ℬB $ i⊥)) (f-spec (ℬB $ i⊥) (κ i⊥)))))
                                ℐ)
                               (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆)
                               δ
                               where
                               δ : _
                               δ y (i , eq-i) =
                                 subst
                                   (λ - → [ - ⊑[ pos (Patch A) ] (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) ])
                                   eq-i
                                   ζ
                                   where
                                   open PosetReasoning (pos B) using () renaming (_⊑⟨_⟩_ to _≤⟨_⟩B_; _■ to _■B)

                                   ξ = ℬB $ ℐ $ i                  ≤⟨ ⋁[ B ]-upper ⁅ ℬB $ i ∣ i ε ℐ ⁆ (ℬB $ ℐ $ i) (i , refl) ⟩B
                                       (⋁[ B ] ⁅ ℬB $ i ∣ i ε ℐ ⁆) ≤⟨ ≡⇒⊑ (pos B) (sym W◀ℐ) ⟩B
                                       W                           ≤⟨ ⊔[ B ]-upper₀ W (ℬB $ i⊥) ⟩B
                                       𝒿 .π₀ .π₀ (ℬB $ i⊥)         ■B

                                   ζ = ⋁[ Patch A ]-upper _
                                     ((∣εA⋆∣ (f⋆ (ℬB $ ℐ $ i))) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ i⊥)) (f-spec (ℬB $ i⊥) (κ i⊥)))
                                     ((ℐ $ i , i⊥ , ξ) , refl)

    -- open import ClosedNuclei

    down′ : [ ∣εA⋆∣ (f⋆ W) ⊑[ pos (Patch A) ] (⋁[ Patch A ] ℱ) ]
    down′ x = ∣εA⋆∣ (f⋆ W) .π₀ .π₀ x                                      ≤⟨ ⦅𝟏⦆ x  ⟩
              (∣εA⋆∣ (f⋆ (⋁[ B ] ⁅ (ℬB $ i) ∣ i ε ℐ ⁆))) .π₀ .π₀ x        ≤⟨ ⦅𝟐⦆ x  ⟩
              ∣εA⋆∣ (⋁[ A ] ⁅ f⋆ (ℬB $ i) ∣ i ε ℐ ⁆) .π₀ .π₀ x            ≤⟨ ⦅𝟑⦆ x ⟩
              (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ i)) ∣ i ε ℐ ⁆) .π₀ .π₀ x    ≤⟨ cool-lemma ⊥εℬB x ⟩
              (⋁[ Patch A ] ⁅ ∣εA⋆∣ (f⋆ (ℬB $ k)) ⊓[ Patch A ] ∣ηA⋆∣ (f⋆ (ℬB $ l)) (f-spec (ℬB $ l) (κ l)) ∣ (k , l , _) ∶ 𝒦 𝒿 ⁆) .π₀ .π₀ x  ■ₐ
              where
                ⦅𝟏⦆ = ≡⇒⊑ (pos (Patch A)) (cong (λ - → ∣εA⋆∣ (f⋆ -)) W◀ℐ)
                ⦅𝟐⦆ = ≡⇒⊑ (pos (Patch A)) (cong ∣εA⋆∣ (f⋁ ⁅ (ℬB $ i) ∣ i ε ℐ ⁆))
                ⦅𝟑⦆ = ≡⇒⊑ (pos (Patch A)) (εε-resp-⋁ A ⁅ f⋆ (ℬB $ i) ∣ i ε ℐ ⁆)

    down : (x : ∣ A ∣F) → [ ∣εA⋆∣ (f⋆ W) .π₀ .π₀ x ⊑[ pos A ] (⋁[ Patch A ] ℱ) .π₀ .π₀ x ]
    down x = ∣εA⋆∣ (f⋆ W) .π₀ .π₀ x      ≤⟨ down′ x ⟩
             (⋁[ Patch A ] ℱ) .π₀ .π₀ x  ■ₐ

    nts : ∣εA⋆∣ (f⋆ W) ≡ ⋁[ Patch A ] ℱ
    nts = ⊑[ pos (Patch A) ]-antisym _ _ down up

-- --}
-- --}
-- --}
```
