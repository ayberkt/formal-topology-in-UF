---
title: Base for a Frame
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

module Base where

open import Basis
open import Frame
open import Poset
open import Cofinality
open import Cubical.Data.List hiding ([_])
open import Cubical.Foundations.Function using (uncurry)
```
-->

```agda
isBasisFor : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ∣ F ∣F → (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇ 
isBasisFor {𝓦 = 𝓦} F ℬ =
  (x : ∣ F ∣F) →
    Σ[ J ∈ Fam 𝓦 (index ℬ) ] [ isSup (pos F) ⁅ ℬ $ j ∣ j ε  J ⁆ x ]

isDirBasisFor : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ∣ F ∣F → (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
isDirBasisFor {𝓥 = 𝓥} {𝓦} F B =
  (x : ∣ F ∣F) →
    Σ[ U ∈ Fam 𝓦 (index B) ]
      [ isDirected (pos F) ⁅ B $ u ∣ u ε U ⁆ ⊓ isSup (pos F) ⁅ B $ u ∣ u ε U ⁆ x ]
```

```agda
hasBasis : (F : Frame 𝓤 𝓥 𝓦) → hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺)
hasBasis {𝓦 = 𝓦} F = ∥ Σ[ ℬ ∈ Fam 𝓦 ∣ F ∣F ] isBasisFor F ℬ ∥Ω
```

```agda
hasDirBasis : (F : Frame 𝓤 𝓥 𝓦) → hProp (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺)
hasDirBasis {𝓦 = 𝓦} F = ∥ Σ[ ℬ ∈ Fam 𝓦 ∣ F ∣F ] isDirBasisFor F ℬ ∥Ω
```

```agda
directify : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ∣ F ∣F) → Fam 𝓦 ∣ F ∣F
directify F (I , f) = (List I , g)
  where
  open PosetReasoning (pos F)

  g : List I → ∣ F ∣F
  g = foldr (λ i - → f i ∨[ F ] -) ⊥[ F ]

directify-directed : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ∣ F ∣F)
                   → [ isDirected (pos F) (directify F S) ]
directify-directed F S@(I , f) = directed
  where
  open PosetReasoning (pos F)

  g = (directify F S) $_

  g-functorial : (is js : List I) → g (is ++ js) ≡ g is ∨[ F ] g js
  g-functorial []       js = g ([] ++ js)                  ≡⟨ refl                 ⟩
                             g js                          ≡⟨ sym (x∨⊥=x F (g js)) ⟩
                             ⊥[ F ] ∨[ F ] g js            ≡⟨ refl                 ⟩
                             g []   ∨[ F ] g js            ∎
  g-functorial (i ∷ is) js = g (i ∷ (is ++ js))            ≡⟨ refl ⟩
                             f i ∨[ F ] g (is ++ js)       ≡⟨ ⦅𝟏⦆  ⟩
                             f i ∨[ F ] (g is ∨[ F ] g js) ≡⟨ ⦅𝟐⦆  ⟩
                             (f i ∨[ F ] g is) ∨[ F ] g js ≡⟨ refl ⟩
                             g (i ∷ is) ∨[ F ] g js        ∎
    where
    ⦅𝟏⦆ = cong (λ - → f i ∨[ F ] -) (g-functorial is js)
    ⦅𝟐⦆ = sym (∨[ F ]-assoc (f i) (g is) (g js))

  upwards : [ ∀[ is ∶ List I ] ∀[ js ∶ List I ]
              ∥ Σ[ ks ∈ List I ] [ g is ⊑[ pos F ] g ks ] × [ g js ⊑[ pos F ] g ks ] ∥Ω ]
  upwards is js = ∣ is ++ js , G𝟏 , G𝟐 ∣
    where
    G𝟏 : [ g is ⊑[ pos F ] g (is ++ js) ]
    G𝟏 = g is             ⊑⟨ ⊔[ F ]-upper₀ (g is) (g js)            ⟩
         g is ∨[ F ] g js ⊑⟨ ≡⇒⊑ (pos F) (sym (g-functorial is js)) ⟩
         g (is ++ js)     ■

    G𝟐 : [ g js ⊑[ pos F ] g (is ++ js) ]
    G𝟐 = g js              ⊑⟨ ⊔[ F ]-upper₁ (g is) (g js)            ⟩
         g is ∨[ F ] g  js ⊑⟨ ≡⇒⊑ (pos F) (sym (g-functorial is js)) ⟩
         g (is ++ js)      ■

  directed : [ isDirected (pos F) (List I , g) ]
  directed = ∣ [] ∣ , upwards

directification-resp-join : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ∣ F ∣F)
                          → ⋁[ F ] S ≡ ⋁[ F ] (directify F S)
directification-resp-join F S = ⊑[ pos F ]-antisym _ _ G𝟏 G𝟐
  where
  open PosetReasoning (pos F)

  G𝟏 : [ ⋁[ F ] S ⊑[ pos F ] ⋁[ F ] (directify F S) ]
  G𝟏 = ⋁[ F ]-least _ _ nts
    where
    nts : [ ∀[ s ε S ] (s ⊑[ pos F ] ⋁[ F ] (directify F S)) ]
    nts s (i , eq) = ⋁[ F ]-upper (directify F S) s (i ∷ [] , goal)
      where
      goal : (S $ i) ∨[ F ] ⊥[ F ] ≡ s
      goal = (S $ i) ∨[ F ] ⊥[ F ] ≡⟨ ∨-comm F (S $ i) ⊥[ F ] ⟩
             ⊥[ F ] ∨[ F ] (S $ i) ≡⟨ x∨⊥=x F (S $ i)         ⟩
             S $ i                 ≡⟨ eq                      ⟩
             s                     ∎

  G𝟐-lemma : (is : List (index S)) → [ (directify F S $ is) ⊑[ pos F ] ⋁[ F ] S ]
  G𝟐-lemma []       = ⊥[ F ] ⊑⟨ ⊥[ F ]-bottom (⋁[ F ] S) ⟩ ⋁[ F ] S ■
  G𝟐-lemma (i ∷ is) = ⊔[ F ]-least _ _ _ nts₀ nts₁
    where
    nts₀ : [ (S $ i) ⊑[ pos F ] (⋁[ F ] S) ]
    nts₀ = ⋁[ F ]-upper _ _ (i , refl)

    nts₁ : [ (directify F S $ is) ⊑[ pos F ] (⋁[ F ] S) ]
    nts₁ = G𝟐-lemma is

  G𝟐 : [ ⋁[ F ] (directify F S) ⊑[ pos F ] ⋁[ F ] S   ]
  G𝟐 = ⋁[ F ]-least (directify F S) (⋁[ F ] S) nts
    where
    nts : [ ∀[ s ε (directify F S) ] (s ⊑[ pos F ] ⋁[ F ] S) ]
    nts s (is , eq) = subst (λ - → [ rel (pos F) - (⋁[ F ] S) ]) eq (G𝟐-lemma is)
```

```agda
directified-basis-gives-basis : (F : Frame 𝓤 𝓥 𝓦)
                              → (ℬ : Fam 𝓦 ∣ F ∣F)
                              → isBasisFor F ℬ
                              → isDirBasisFor F (directify F ℬ)
directified-basis-gives-basis {𝓦 = 𝓦} F ℬ basis = goal
  where
  𝒥 : ∣ F ∣F → Fam 𝓦 (index ℬ)
  𝒥 = π₀ ∘ basis

  approx : ∣ F ∣F → Fam 𝓦 ∣ F ∣F
  approx x = ⁅ ℬ $ j ∣ j ε 𝒥 x ⁆

  goal : isDirBasisFor F (directify F ℬ)
  goal x = (List (index (approx x)) , g) , dir , sup
    where
    g : List (index (approx x)) → index (directify F ℬ)
    g = map (𝒥 x $_)

    what-we-need : ⁅ directify F ℬ $ is ∣ is ε (List (index (approx x)) , g) ⁆ ≡ directify F (approx x)
    what-we-need = ΣPathTransport→PathΣ _ _ (refl , (transport refl ((directify F ℬ $_) ∘ g) ≡⟨ transportRefl ((directify F ℬ $_) ∘ g) ⟩ (directify F ℬ $_) ∘ g ≡⟨ funExt final-goal ⟩ π₁ (directify F (approx x)) ∎))
      where
      final-goal : (is : List (index (approx x))) → directify F ℬ $ g is ≡ (directify F (approx x)) $ is
      final-goal []       = refl
      final-goal (i ∷ is) = directify F ℬ $ g (i ∷ is)                            ≡⟨ refl ⟩
                            (ℬ $ 𝒥 x $ i) ∨[ F ] (directify F ℬ $ (g is))         ≡⟨ cong (λ - → (ℬ $ 𝒥 x $ i) ∨[ F ] -) (final-goal is) ⟩
                            (ℬ $ (𝒥 x $ i)) ∨[ F ] (directify F (approx x) $ is)  ≡⟨ refl ⟩
                            directify F (approx x) $ (i ∷ is)                     ∎

    dir : [ isDirected (pos F) ⁅ directify F ℬ $ is ∣ is ε (List (index (approx x)) , g) ⁆ ]
    dir = subst (λ - → [ isDirected (pos F) - ]) (sym what-we-need) (directify-directed F (approx x))

    sup : [ isSup (pos F) ⁅ directify F ℬ $ is ∣ is ε (List (index (approx x)) , g) ⁆ x ]
    sup = subst (λ - → [ isSup (pos F) - x ]) (sym what-we-need) (subst (λ - → [ isSup (pos F) (directify F (approx x)) - ]) (sym foo) (sup-goal₁ , sup-goal₂))
      where
      sup-goal₁ = ⋁[ F ]-upper (directify F (approx x))

      sup-goal₂ = ⋁[ F ]-least (directify F (approx x))

      foo : x ≡ ⋁[ F ] directify F (approx x)
      foo = x                             ≡⟨ uncurry (⋁-unique F (approx x) x) (π₁ (basis x)) ⟩
            ⋁[ F ] (approx x)             ≡⟨ directification-resp-join F (approx x) ⟩
            ⋁[ F ] directify F (approx x) ∎
```

```agda
basis→dir-basis : (F : Frame 𝓤 𝓥 𝓦) → [ hasBasis F ] → [ hasDirBasis F ]
basis→dir-basis {𝓦 = 𝓦} F = ∥∥-rec (isProp[] (hasDirBasis F)) nts
  where
  nts : Σ[ ℬ ∈ Fam 𝓦 ∣ F ∣F ] (isBasisFor F ℬ) → [ hasDirBasis F ]
  nts (ℬ , basis) = ∣ directify F ℬ , goal ∣
    where
    𝒥 : ∣ F ∣F → Fam 𝓦 (index ℬ)
    𝒥 = π₀ ∘ basis

    approx : ∣ F ∣F → Fam 𝓦 ∣ F ∣F
    approx x = ⁅ ℬ $ j ∣ j ε 𝒥 x ⁆

    goal : isDirBasisFor F (directify F ℬ)
    goal x = (List (index (approx x)) , g) , dir , sup
      where
      g : List (index (approx x)) → index (directify F ℬ)
      g = map (𝒥 x $_)

      what-we-need : ⁅ directify F ℬ $ is ∣ is ε (List (index (approx x)) , g) ⁆ ≡ directify F (approx x)
      what-we-need = ΣPathTransport→PathΣ _ _ (refl , (transport refl ((directify F ℬ $_) ∘ g) ≡⟨ transportRefl ((directify F ℬ $_) ∘ g) ⟩ (directify F ℬ $_) ∘ g ≡⟨ funExt final-goal ⟩ π₁ (directify F (approx x)) ∎))
        where
        final-goal : (is : List (index (approx x))) → directify F ℬ $ g is ≡ (directify F (approx x)) $ is
        final-goal []       = refl
        final-goal (i ∷ is) = directify F ℬ $ g (i ∷ is)                            ≡⟨ refl ⟩
                              (ℬ $ 𝒥 x $ i) ∨[ F ] (directify F ℬ $ (g is))         ≡⟨ cong (λ - → (ℬ $ 𝒥 x $ i) ∨[ F ] -) (final-goal is) ⟩
                              (ℬ $ (𝒥 x $ i)) ∨[ F ] (directify F (approx x) $ is)  ≡⟨ refl ⟩
                              directify F (approx x) $ (i ∷ is)                     ∎

      dir : [ isDirected (pos F) ⁅ directify F ℬ $ is ∣ is ε (List (index (approx x)) , g) ⁆ ]
      dir = subst (λ - → [ isDirected (pos F) - ]) (sym what-we-need) (directify-directed F (approx x))

      sup : [ isSup (pos F) ⁅ directify F ℬ $ is ∣ is ε (List (index (approx x)) , g) ⁆ x ]
      sup = subst (λ - → [ isSup (pos F) - x ]) (sym what-we-need) (subst (λ - → [ isSup (pos F) (directify F (approx x)) - ]) (sym foo) (sup-goal₁ , sup-goal₂))
        where
        sup-goal₁ = ⋁[ F ]-upper (directify F (approx x))

        sup-goal₂ = ⋁[ F ]-least (directify F (approx x))

        foo : x ≡ ⋁[ F ] directify F (approx x)
        foo = x                             ≡⟨ uncurry (⋁-unique F (approx x) x) (π₁ (basis x)) ⟩
              ⋁[ F ] (approx x)             ≡⟨ directification-resp-join F (approx x) ⟩
              ⋁[ F ] directify F (approx x) ∎
```

```agda
```
