---
title: Properties of Frames
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Poset
open import Frame
open import Regular
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

module AdditionalFrameTheorems where
```
-->

Bunch of theorems about frames that should really go in the `Frame` module. That module
has gotten too big which is slowing down the typechecking which is why they are in this
module.

```agda
resp-∨ : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦) (f : F ─f→ G)
       → (x y : ∣ F ∣F)
       → π₀ (π₀ f) (x ∨[ F ] y) ≡ π₀ (π₀ f) x ∨[ G ] π₀ (π₀ f) y
resp-∨ F G ((f , f-mono) , _ , _ , r) x y =
  f (x ∨[ F ] y)           ≡⟨ r ⁅ x , y ⁆ ⟩
  ⋁[ G ] (f ⟨$⟩ ⁅ x , y ⁆) ≡⟨ nts ⟩
  f x ∨[ G ] f y           ∎
  where
  open PosetReasoning (pos G)

  nts : _
  nts = ⋁-unique G _ _ G𝟏 G𝟐
    where
    G𝟏 : _
    G𝟏 z (true  , eq) = z                        ⊑⟨ ≡⇒⊑ (pos G) (sym eq)            ⟩
                        f x                      ⊑⟨ ⋁[ G ]-upper _ _ (true , refl)  ⟩
                        ⋁[ G ] (f ⟨$⟩ ⁅ x , y ⁆) ■
    G𝟏 z (false , eq) = z                        ⊑⟨ ≡⇒⊑ (pos G) (sym eq)            ⟩
                        f y                      ⊑⟨ ⋁[ G ]-upper _ _ (false , refl) ⟩
                        ⋁[ G ] (f ⟨$⟩ ⁅ x , y ⁆) ■

    G𝟐 : _
    G𝟐 z ϕ = ⋁[ G ]-least _ _ G𝟐a
      where
      G𝟐a : [ ∀[ w ε (f ⟨$⟩ ⁅ x ,  y ⁆) ] (w ⊑[ pos G ] z) ]
      G𝟐a w (true  , eq) = w ⊑⟨ ≡⇒⊑ (pos G) (sym eq) ⟩ f x ⊑⟨ ϕ (f x) (true  , refl) ⟩ z ■
      G𝟐a w (false , eq) = w ⊑⟨ ≡⇒⊑ (pos G) (sym eq) ⟩ f y ⊑⟨ ϕ (f y) (false , refl) ⟩ z ■

complement-preservation : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦) (f : F ─f→ G)
                        → (x x′ : ∣ F ∣F)
                        → complements F x x′
                        → complements G (π₀ (π₀ f) x) (π₀ (π₀ f) x′)
complement-preservation F G 𝒻@((f , f-mono) , p , q , r) x x′ (x∧x′=⊥ , x∨x′=⊤) =
  G𝟏 , G𝟐
  where
  open PosetReasoning (pos G)

  abstract
    G𝟏 : f x ⊓[ G ] f x′ ≡ ⊥[ G ]
    G𝟏 = ⊑[ pos G ]-antisym _ _ G𝟏a (⊥[ G ]-bottom (f x ⊓[ G ] f x′))
      where
      G𝟏a : [ (f x ⊓[ G ] f x′)         ⊑[ pos  G ] ⊥[ G ] ]
      G𝟏a = (f x) ⊓[ G ] (f x′)         ⊑⟨ ≡⇒⊑ (pos G) (sym (q x x′)) ⟩
            f (x ⊓[ F ] x′)             ⊑⟨ f-mono _ _ (≡⇒⊑ (pos F) x∧x′=⊥) ⟩
            f ⊥[ F ]                    ⊑⟨ ⊑[ pos G ]-refl _ ⟩
            f (⋁[ F ] (𝟘 _ , λ ()))     ⊑⟨ ≡⇒⊑ (pos G) (r (𝟘 _ , λ ())) ⟩
            ⋁[ G ] (f ⟨$⟩ (𝟘 _ , λ ())) ⊑⟨ ≡⇒⊑ (pos G) (cong (λ - → ⋁[ G ] (𝟘 _ , -)) (funExt λ ())) ⟩
            ⋁[ G ] (𝟘 _ , λ ())         ⊑⟨ ⊑[ pos G ]-refl _ ⟩
            ⊥[ G ]                      ■

    G𝟐 : f x ∨[ G ] f x′ ≡ ⊤[ G ]
    G𝟐 = ⊑[ pos G ]-antisym _ _ (⊤[ G ]-top _) G𝟐a
      where
      G𝟐a : [ ⊤[ G ] ⊑[ pos G ] (f x ∨[ G ] f x′) ]
      G𝟐a = ⊤[ G ]          ⊑⟨ ≡⇒⊑ (pos G) (sym p)                                    ⟩
            f ⊤[ F ]        ⊑⟨ f-mono ⊤[ F ] (x ∨[ F ] x′) (≡⇒⊑ (pos F) (sym x∨x′=⊤)) ⟩
            f (x ∨[ F ] x′) ⊑⟨ ≡⇒⊑ (pos G) (resp-∨ F G 𝒻 x x′)                        ⟩
            f x ∨[ G ] f x′ ■

iso-inj-surj : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦)
             → (𝒻@((f , _) , _) : F ─f→ G)
             → isEmbedding  {A = ∣ F ∣F} {B = ∣ G ∣F} f
             → isSurjection {A = ∣ F ∣F} {B = ∣ G ∣F} f
             → isFrameIso {F = F} {G} 𝒻
iso-inj-surj F G 𝒻@((f , f-mono) , f-resp-⊤ , f-resp-∧ , f-resp-⋁) f-emb f-surj =
  ((g , g-mono) , resp-⊤ , resp-∧ , resp-⋁) , sec , ret
  where
  ι : Iso ∣ F ∣F ∣ G ∣F
  ι = equivToIso (f , isEmbedding×isSurjection→isEquiv (f-emb , f-surj))

  g : ∣ G ∣F → ∣ F ∣F
  g = Iso.inv ι

  sec : section f g
  sec = Iso.rightInv ι

  ret : retract f g
  ret = Iso.leftInv ι

  resp-⊤ : g ⊤[ G ] ≡ ⊤[ F ]
  resp-⊤ = g ⊤[ G ]     ≡⟨ cong g (sym f-resp-⊤) ⟩
           g (f ⊤[ F ]) ≡⟨ ret ⊤[ F ]            ⟩
           ⊤[ F ]       ∎

  f-inj : (x y : ∣ F ∣F) → f x ≡ f y → x ≡ y
  f-inj x y = Iso.inv (equivToIso ((λ p i → f (p i)) , f-emb x y))

  resp-∧ : (x y : ∣ G ∣F)
         → g (x ⊓[ G ] y) ≡ g x ⊓[ F ] g y
  resp-∧ x y = f-inj (g (x ⊓[ G ] y)) (g x ⊓[ F ] g y) †
    where
    † : f (g (x ⊓[ G ] y)) ≡ f (g x ⊓[ F ] g y)
    † = f (g (x ⊓[ G ] y))     ≡⟨ sec (x ⊓[ G ] y)                      ⟩
        x ⊓[ G ] y             ≡⟨ cong (λ - → - ⊓[ G ] y) (sym (sec x)) ⟩
        f (g x) ⊓[ G ] y       ≡⟨ cong (λ - → _ ⊓[ G ] -) (sym (sec y)) ⟩
        f (g x) ⊓[ G ] f (g y) ≡⟨ sym (f-resp-∧ (g x) (g y))            ⟩
        f (g x ⊓[ F ] g y)     ∎

  g-mono : isMonotonic (pos G) (pos F) g
  g-mono y₀ y₁ y₀≤y₁ = x=x∧y⇒x⊑y F †
    where
    † : g y₀ ≡ g y₀ ⊓[ F ] g y₁
    † = g y₀                ≡⟨ cong g (x⊑y⇒x=x∧y G y₀≤y₁)  ⟩
        g (y₀ ⊓[ G ] y₁)    ≡⟨ resp-∧ y₀ y₁                ⟩
        g y₀ ⊓[ F ] g y₁    ∎

  resp-⋁ : (S : Fam _ ∣ G ∣F) → g (⋁[ G ] S) ≡ ⋁[ F ] ⁅ g s ∣ s ε S ⁆
  resp-⋁ S = f-inj (g (⋁[ G ] S)) (⋁[ F ] ⁅ g s ∣ s ε S ⁆) †
    where
    † : f (g (⋁[ G ] S)) ≡ f (⋁[ F ] ⁅ g s ∣ s ε S ⁆)
    † = f (g (⋁[ G ] S))            ≡⟨ ⦅𝟏⦆ ⟩
        ⋁[ G ] S                    ≡⟨ ⦅𝟐⦆ ⟩
        ⋁[ G ] ⁅ f (g s) ∣ s ε S ⁆  ≡⟨ ⦅𝟑⦆ ⟩
        f (⋁[ F ] ⁅ g s ∣ s ε S ⁆)  ∎
        where
        ⦅𝟏⦆ = sec (⋁[ G ] S)
        ⦅𝟐⦆ = cong (λ - → ⋁[ G ] (index S , -)) (funExt λ i → sym (sec (S $ i)))
        ⦅𝟑⦆ = sym (f-resp-⋁ ⁅ g s ∣ s ε S ⁆)
```
