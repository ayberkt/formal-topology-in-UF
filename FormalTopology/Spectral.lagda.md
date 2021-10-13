---
title: Spectral Locales
author: Ayberk Tosun
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Cubical.Functions.Logic renaming (_⊓_ to _∧_)
open import Cubical.Foundations.Function
open import Frame

module Spectral (F : Frame 𝓤 𝓥 𝓦) where

open import Poset
open import WayBelow
open import PatchFrame
open import RightAdjoint
open import Base hiding (hasBasis)
```
-->

## Definition of spectrality

**Definition.** A spectral locale is a locale for which the compact opens form
a base closed under finite meets.

**Definition (better).** Every open is the join of the set of compact opens
below it and the meet of two compacts opens is compact. Also, the top element is
compact.

```agda
closedUnderFinMeets : Fam 𝓦 ∣ F ∣F → (𝓤 ∨ 𝓥 ∨ 𝓦) ̇
closedUnderFinMeets U =
    ∥ Σ[ i ∈ index U ] [ isTop (pos F) (U $ i) ] ∥
  × (((i j : index U) → ∥ Σ[ k ∈ index U ] [ isInf (pos F) (U $ k) (U $ i) (U $ j) ] ∥))

closedUnderFinMeets′ : Fam 𝓦 ∣ F ∣F → hProp (𝓤 ∨ 𝓥 ∨ 𝓦)
closedUnderFinMeets′ S =
    ∥ Σ[ i ∈ index S ] [ isTop (pos F) (S $ i) ] ∥Ω
  ∧ (∀[ i ∶ index S ] ∀[ j ∶ index S ] ∥ Σ[ k ∈ index S ] [ isInf (pos F) (S $ k) (S $ i) (S $ j) ] ∥Ω)

isSpectral′ : (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
isSpectral′ =
  ∥ Σ[ ℬ ∈ Fam 𝓦 ∣ F ∣F ]
      ((i : index ℬ) → [ isCompactOpen F (ℬ $ i) ])
    × isDirBasisFor F ℬ × closedUnderFinMeets ℬ ∥

∥∥-functorial : {A : Type 𝓤} {B : Type 𝓥} → ∥ (A → B) ∥ → ∥ A ∥ → ∥ B ∥
∥∥-functorial {B = B} f x = ∥∥-rec (∥∥-prop B) (λ g → ∥∥-rec (∥∥-prop B) (λ y → ∣ g y ∣) x) f

spec′→basis : isSpectral′ → ∥ hasBasis F ∥
spec′→basis sp = ∥∥-rec (∥∥-prop (hasBasis F)) nts sp
  where
  nts : Σ-syntax (Fam 𝓦 ∣ F ∣F)
          (λ ℬ →
             ((i : index ℬ) → [ isCompactOpen F (ℬ $ i) ]) ×
             isDirBasisFor F ℬ × closedUnderFinMeets ℬ) →
          ∥ hasBasis F ∥
  nts (ℬ , _ , fb , _)= ∣ ℬ , fb ∣

spec→compact : isSpectral′ → [ isCompact F ]
spec→compact spec = ∥∥-rec (isProp[] (isCompact F)) nts spec
  where
  nts : Σ[ ℬ ∈ (Fam 𝓦 ∣ F ∣F) ] (((i : index ℬ) → [ isCompactOpen F (ℬ $ i) ]) × isDirBasisFor F ℬ × closedUnderFinMeets ℬ)
      → [ isCompact F ]
  nts (ℬ , κ , dir , fm) = ∥∥-rec (isProp[] (isCompact F)) nts′ (π₀ fm)
    where
    nts′ : _
    nts′ (i , top) = subst (λ - → [ _≪_ F -  - ]) (top-unique F (ℬ $ i) top) (κ i)

spec→compacts-closed-under-∧ : isSpectral′
                             → (x y : ∣ F ∣F)
                             → [ isCompactOpen F x ]
                             → [ isCompactOpen F y ]
                             → [ isCompactOpen F (x ⊓[ F ] y) ]
spec→compacts-closed-under-∧ spec x y x-comp y-comp =
  ∥∥-rec (isProp[] (isCompactOpen F (x ⊓[ F ] y))) γ spec
  where
  γ : _ → [ isCompactOpen F (x ⊓[ F ] y) ]
  γ (ℬ , κ , p , q) =
    ∥∥-rec (isProp[] (isCompactOpen F (x ⊓[ F ] y))) δ (∥∥-× ϕ ψ)
    where
    ℐ : Fam 𝓦 (index ℬ)
    ℐ = π₀ (p x)

    𝒥 : Fam 𝓦 (index ℬ)
    𝒥 = π₀ (p y)

    x-eq : x ≡ ⋁[ F ] ⁅ ℬ $ i ∣ i ε ℐ ⁆
    x-eq = uncurry (⋁-unique F ⁅ ℬ $ i ∣ i ε ℐ ⁆ x) (π₁ (π₁ (p x)))

    y-eq : y ≡ ⋁[ F ] ⁅ ℬ $ j ∣ j ε 𝒥 ⁆
    y-eq = uncurry (⋁-unique F ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ y) (π₁ (π₁ (p y)))

    cover-x : [ x ⊑[ pos F ] ⋁[ F ] ⁅ ℬ $ i ∣ i ε ℐ ⁆ ]
    cover-x = ≡⇒⊑ (pos F) x-eq

    cover-y : [ y ⊑[ pos F ] ⋁[ F ] ⁅ ℬ $ i ∣ i ε 𝒥 ⁆ ]
    cover-y = ≡⇒⊑ (pos F) y-eq

    ϕ : ∥ Σ[ i ∈ index ℐ ] [ x ⊑[ pos F ] (ℬ $ ℐ $ i) ] ∥
    ϕ = x-comp ⁅ ℬ $ i ∣ i ε ℐ ⁆ (π₀ (π₁ (p x))) cover-x

    ψ : ∥ Σ[ i ∈ index 𝒥 ] [ y ⊑[ pos F ] (ℬ $ 𝒥 $ i) ] ∥
    ψ = y-comp ⁅ ℬ $ i ∣ i ε 𝒥 ⁆ (π₀ (π₁ (p y))) cover-y

    δ : _
    δ ((i , x≤bᵢ) , (j , y≤bⱼ)) =
      ∥∥-rec (isProp[] (isCompactOpen F (x ⊓[ F ] y))) ν (π₁ q (ℐ $ i) (𝒥 $ j))
      where
      x=bᵢ : x ≡ ℬ $ (ℐ $ i)
      x=bᵢ = ⊑[ pos F ]-antisym _ _ x≤bᵢ (subst (λ - → [ (ℬ $ ℐ $ i) ⊑[ pos F ] - ]) (sym x-eq) (⋁[ F ]-upper _ _ (i , refl)))

      y=bⱼ : y ≡ ℬ $ (𝒥 $ j)
      y=bⱼ = ⊑[ pos F ]-antisym _ _ y≤bⱼ (subst (λ - → [ (ℬ $ 𝒥 $ j) ⊑[ pos F ] - ]) (sym y-eq) (⋁[ F ]-upper _ _ (j , refl)))

      ∧-eq : x ⊓[ F ] y ≡ ((ℬ $ ℐ $ i) ⊓[ F ] (ℬ $ 𝒥 $ j))
      ∧-eq = x ⊓[ F ] y                     ≡⟨ cong (λ - → - ⊓[ F ] y) x=bᵢ           ⟩
             (ℬ $ ℐ $ i) ⊓[ F ] y           ≡⟨ cong (λ - → (ℬ $ ℐ $ i) ⊓[ F ] -) y=bⱼ ⟩
             (ℬ $ ℐ $ i) ⊓[ F ] (ℬ $ 𝒥 $ j) ∎

      ν : _
      ν (k , inf) =
        subst (λ - → [ isCompactOpen F - ]) inf′ (κ k)
        where
        inf′ : ℬ $ k ≡ x ⊓[ F ] y
        inf′ = ℬ $ k                           ≡⟨ ⦅𝟏⦆ ⟩
               (ℬ $ ℐ $ i) ⊓[ F ] (ℬ $ 𝒥 $ j)  ≡⟨ sym ∧-eq ⟩
               x ⊓[ F ] y                      ∎
               where
               ⦅𝟏⦆ = ⊓-unique F _ _ _ (π₀ (π₀ inf)) (π₁ (π₀ inf)) λ w p q → π₁ inf w (p , q)

-- spec′→spec : isSpectral′ → isSpectral
-- spec′→spec spec′ = G𝟏 , G𝟐 , G𝟑
--   where
--   G𝟏 : (x : ∣ F ∣F)
--      → ∥ Σ[ U ∈ Fam 𝓦 ∣ F ∣F ] [ isSup (pos F) U x ] × [ ∀[ x ε U ] (isCompactOpen F x) ] ∥
--   G𝟏 x = ∥∥-rec (∥∥-prop _) G𝟏a ?
--     where
--     G𝟏a : Σ-syntax (Fam 𝓦 ∣ F ∣F)
--             (λ ℬ →
--                ((i : index ℬ) → [ isCompactOpen F (ℬ $ i) ]) ×
--                ((x₁ : ∣ F ∣F) →
--                 Σ-syntax (Fam 𝓦 (index ℬ))
--                 (λ I →
--                    [ isDirected (pos F) (fmap (_$_ ℬ) I) ] ×
--                    [ isSup (pos F) (fmap (_$_ ℬ) I) x₁ ]))
--                ×
--                Σ-syntax (index ℬ) (λ i → [ isTop (pos F) (ℬ $ i) ]) ×
--                ((i j : index ℬ) →
--                 Σ-syntax (index ℬ)
--                 (λ k → [ isInf (pos F) (ℬ $ k) (ℬ $ i) (ℬ $ j) ]))) →
--             ∥
--             Σ-syntax (Fam 𝓦 ∣ F ∣F)
--             (λ U → [ isSup (pos F) U x ] × [ fam-forall U (isCompactOpen F) ])
--             ∥
--     G𝟏a (ℬ , ϕ , J , _) =
--       ∣ ⁅ ℬ $ j ∣ j ε π₀ (J x) ⁆
--       , (π₁ (π₁ (J x)) , λ b (i , p) → subst ([_] ∘ isCompactOpen F) p (ϕ (π₀ (J x) $ i))) ∣

--   G𝟐 : [ isCompactOpen F ⊤[ F ] ]
--   G𝟐 = ∥∥-rec (isProp[] (isCompactOpen F ⊤[ F ])) G𝟐a spec′
--     where
--     G𝟐a : _ → [ isCompactOpen F ⊤[ F ] ]
--     G𝟐a (ℬ , (ϕ , _ , (i , p) , r)) = subst ([_] ∘ isCompactOpen F) G𝟐b (ϕ i)
--       where
--       G𝟐b : ℬ $ i ≡ ⊤[ F ]
--       G𝟐b = top-unique F (ℬ $ i) p

--   G𝟑 : (x y : ∣ F ∣F)
--      → [ isCompactOpen F x ] → [ isCompactOpen F y ] → [ isCompactOpen F (x ⊓[ F ] y) ]
--   G𝟑 x y x-comp y-comp =
--     ∥∥-rec (isProp[] (isCompactOpen F (x ⊓[ F ] y))) G𝟑a spec′
--     where
--     G𝟑a : _ → [ isCompactOpen F (x ⊓[ F ] y) ]
--     G𝟑a (ℬ , κ , (ϕ , ψ)) =
--       ∥∥-rec
--         (isProp[] (isCompactOpen F (x ⊓[ F ] y)))
--         G𝟑b
--         (∥∥-× (x-comp _ dir₀ cover₀) (y-comp _ dir₁ cover₁))
--       where
--       ℐ : Fam 𝓦 (index ℬ)
--       ℐ = π₀ (ϕ x)

--       𝒥 : Fam 𝓦 (index ℬ)
--       𝒥 = π₀ (ϕ y)

--       υ₀ : [ isSup (pos F) ⁅ ℬ $ i ∣ i ε ℐ ⁆ x ]
--       υ₀ = π₁ (π₁ (ϕ x))

--       υ₁ : [ isSup (pos F) ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ y ]
--       υ₁ = π₁ (π₁ (ϕ y))

--       dir₀ : [ isDirected (pos F) ⁅ ℬ $ i ∣ i ε ℐ ⁆ ]
--       dir₀ = π₀ (π₁ (ϕ x))

--       dir₁ : [ isDirected (pos F) ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ ]
--       dir₁ = π₀ (π₁ (ϕ y))

--       cover₀ : [ x ⊑[ pos F ] ⋁[ F ] ⁅ ℬ $ i ∣ i ε ℐ ⁆ ]
--       cover₀ = ≡⇒⊑ (pos F) (⋁-unique F _ _ (π₀ υ₀) (π₁ υ₀))

--       cover₁ : [ y ⊑[ pos F ] ⋁[ F ] ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ ]
--       cover₁ = ≡⇒⊑ (pos F) (⋁-unique F _ _ (π₀ υ₁) (π₁ υ₁))

--       G𝟑b : _ → [ isCompactOpen F (x ⊓[ F ] y) ]
--       G𝟑b ((𝒾 , p) , (𝒿 , q)) = subst ([_] ∘ isCompactOpen F) G𝟑c (κ k)
--         where
--         open PosetReasoning (pos F)

--         i : index ℬ
--         i = π₀ (ϕ x) $ 𝒾

--         j : index ℬ
--         j = π₀ (ϕ y) $ 𝒿

--         k : index ℬ
--         k = ? -- π₀ (π₁ ψ ((π₀ (ϕ x)) $ 𝒾) ((π₀ (ϕ y)) $ 𝒿))

--         foo : x ≡ ℬ $ i
--         foo = ⊑[ pos F ]-antisym x (ℬ $ i) p nts
--           where
--           nts : [ (ℬ $ i) ⊑[ pos F ] x ]
--           nts = ℬ $ i                            ⊑⟨ ⋁[ F ]-upper _ _ (𝒾  , refl) ⟩
--                 ⋁[ F ] ⁅ ℬ $ j ∣ j ε π₀ (ϕ x) ⁆  ⊑⟨ ≡⇒⊑ (pos F) (sym (⋁-unique F _ _ (π₀ υ₀) (π₁ υ₀))) ⟩
--                 x                                ■

--         bar : y ≡ ℬ $ j
--         bar = ⊑[ pos F ]-antisym y (ℬ $ j) q nts
--           where
--           nts : [ (ℬ $ j) ⊑[ pos F ] y ]
--           nts =
--             ℬ $ j                            ⊑⟨ ⋁[ F ]-upper _ _ (𝒿 , refl) ⟩
--             ⋁[ F ] ⁅ ℬ $ j ∣ j ε π₀ (ϕ y) ⁆  ⊑⟨ ≡⇒⊑ (pos F) (sym (⋁-unique F _ _ (π₀ υ₁) (π₁ υ₁))) ⟩
--             y                                ■

--         G𝟑c : ℬ $ k ≡ x ⊓[ F ] y
--         G𝟑c = ℬ $ k                  ≡⟨ ⊓-unique F _ _ _ (π₀ (π₀ (π₁ (π₁ ψ i j)))) ((π₁ (π₀ (π₁ (π₁ ψ i j))))) (λ w p q → π₁ (π₁ (π₁ ψ i j)) w (p , q)) ⟩
--               (ℬ $ i) ⊓[ F ] (ℬ $ j) ≡⟨ cong (λ - → - ⊓[ F ] (ℬ $ j)) (sym foo) ⟩
--               x ⊓[ F ] (ℬ $ j)       ≡⟨ cong (λ - → x ⊓[ F ] -) (sym bar) ⟩
--               x ⊓[ F ] y             ∎



-- TODO.
-- The definition of spectral should be the same as Stone but the requirement of clopen
-- basis replaced with the requirement of a compact basis.
```

```agda
compact-yoneda : isSpectral′
               → (x y : ∣ F ∣F)
               → ((b : ∣ F ∣F) → [ isCompactOpen F b ] →
                    [ b ⊑[ pos F ] x ] → [ b ⊑[ pos F ] y ])
               → [ x ⊑[ pos F ] y ]
compact-yoneda spec x y ϕ =
  ∥∥-rec (isProp[] (x ⊑[ pos F ] y)) G𝟏 spec
  where
  open PosetReasoning (pos F)

  G𝟏 : _
     → [ x ⊑[ pos F ] y ]
  G𝟏  (ℬ , κ , basis , _) =
    x                          ⊑⟨ ⦅𝟏⦆ ⟩
    ⋁[ F ] ⁅ ℬ $ j ∣ j ε 𝒥 ⁆   ⊑⟨ ⦅𝟐⦆ ⟩
    y                          ■
    where
    𝒥 : Fam 𝓦 (index ℬ)
    𝒥 = π₀ (basis x)

    𝒦 : Fam 𝓦 (index ℬ)
    𝒦 = π₀ (basis y)

    cover-x : x ≡ ⋁[ F ] ⁅ ℬ $ j ∣ j ε 𝒥 ⁆
    cover-x = uncurry (⋁-unique F ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ x) (π₁ (π₁ (basis x)))

    ⦅𝟏⦆ : [ x ⊑[ pos F ] ⋁[ F ] ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ ]
    ⦅𝟏⦆ = ≡⇒⊑ (pos F) cover-x

    ⦅𝟐⦆ : [ ⋁[ F ] ⁅ ℬ $ j ∣ j ε 𝒥 ⁆ ⊑[ pos F ] y ]
    ⦅𝟐⦆ = ⋁[ F ]-least _ _ ⦅𝟐a⦆
      where
      ⦅𝟐a⦆ : _
      ⦅𝟐a⦆ b (i , eq) = subst (λ - → [ - ⊑[ pos F ] y ]) eq (ϕ (ℬ $ (𝒥 $ i)) (κ (𝒥 $ i)) ⦅𝟐b⦆)
        where
        ⦅𝟐b⦆ : [ (ℬ $ 𝒥 $ i) ⊑[ pos F ] x ]
        ⦅𝟐b⦆ = subst
                 (λ - → [ (ℬ $ 𝒥 $ i) ⊑[ pos F ] - ])
                 (sym cover-x)
                 (⋁[ F ]-upper _ _ (i , refl))

compact-yoneda₁ : isSpectral′
                → (x y : ∣ F ∣F)
                → [ x ⊑[ pos F ] y ]
                → ((b : ∣ F ∣F) → [ isCompactOpen F b ] →
                     [ b ⊑[ pos F ] x ] → [ b ⊑[ pos F ] y ])
compact-yoneda₁ spec x y p b b-comp q =
  b ⊑⟨ q ⟩ x ⊑⟨ p ⟩ y ■
  where
  open PosetReasoning (pos F)
```

```agda
-- spectral→stone : (F : Frame 𝓤 𝓥 𝓦) → isSpectral F → [ isStone F ]
-- spectral→stone F F-spec = ?
```

```agda
resp-compactness : (f : ∣ F ∣F → ∣ F ∣F) → (𝓤 ∨ 𝓥 ∨ 𝓦 ⁺) ̇
resp-compactness f =
  (b x : ∣ F ∣F) →
    [ isCompactOpen F b ] →
      [ b ⊑[ pos F ] f x ] →
        Σ[ a ∈ ∣ F ∣F ]
          [ isCompactOpen F a ] × [ a ⊑[ pos F ] x ]  × [ b ⊑[ pos F ] f a ]

continuity-lemma : isSpectral′
                 → (f : ∣ F ∣F → ∣ F ∣F)
                 → isMonotonic (pos F) (pos F) f
                 → resp-compactness f
                 → isScottCont′ F f
continuity-lemma spec f mono comp U U-dir =
  ⊑[ pos F ]-antisym _ _ β γ
  where
  η : (b : ∣ F ∣F)
    → [ isCompactOpen F b ]
    → [ b ⊑[ pos F ] f (⋁[ F ] U) ]
    → [ b ⊑[ pos F ] ⋁[ F ] ⁅ f x ∣ x ε U ⁆ ]
  η b b-compact α =
    b                      ⊑⟨ π₁ (π₁ (π₁ (comp b _ b-compact α))) ⟩
    f a                    ⊑⟨ nts ⟩
    ⋁[ F ] ⁅ f x ∣ x ε U ⁆ ■
    where
    open PosetReasoning (pos F)

    a = π₀ (comp b _ b-compact α)

    a-comp : [ isCompactOpen F a ]
    a-comp = π₀ (π₁ (comp b _ b-compact α))

    q : [ a ⊑[ pos F ] ⋁[ F ] U ]
    q = π₀ (π₁ (π₁ (comp b _ b-compact α)))

    rem : Σ[ i ∈ index U ] [ a ⊑[ pos F ] (U $ i) ]
        → [ f a ⊑[ pos F ] ⋁[ F ] ⁅ f x ∣ x ε U ⁆ ]
    rem (i , p) =
      f a                    ⊑⟨ mono a (U $ i) p            ⟩
      f (U $ i)              ⊑⟨ ⋁[ F ]-upper _ _ (i , refl) ⟩
      ⋁[ F ] ⁅ f x ∣ x ε U ⁆ ■

    nts : [ f a ⊑[ pos F ] ⋁[ F ] ⁅ f x ∣ x ε U ⁆ ]
    nts = ∥∥-rec (isProp[] (_ ⊑[ pos F ] _)) rem (a-comp U U-dir q)

  β : [ f (⋁[ F ] U) ⊑[ pos F ] (⋁[ F ] ⁅ f x ∣ x ε U ⁆) ]
  β = compact-yoneda spec (f (⋁[ F ] U)) (⋁[ F ] ⁅ f x ∣ x ε U ⁆) η

  δ : (z : ∣ F ∣F) → z ε ⁅ f x ∣ x ε U ⁆ → [ z ⊑[ pos F ] f (⋁[ F ] U) ]
  δ z (i , eq) = subst (λ - → [ - ⊑[ pos F ] f (⋁[ F ] U) ]) eq nts
    where
    nts : [ f (U $ i) ⊑[ pos F ] (f (⋁[ F ] U)) ]
    nts = mono (U $ i) (⋁[ F ] U) (⋁[ F ]-upper _ _ (i , refl))

  γ : [ (⋁[ F ] ⁅ f x ∣ x ε U ⁆) ⊑[ pos F ] f (⋁[ F ] U) ]
  γ = ⋁[ F ]-least ⁅ f x ∣ x ε U ⁆ (f (⋁[ F ] U)) δ

  -- function-lemma : (f g : ∣ F ∣F → ∣ F ∣F)
  --                → isMonotonic (pos F) (pos F) f
  --                → isMonotonic (pos F) (pos F) g
  --                → ((b : ∣ F ∣F) → [ isCompactOpen F b ] → f b ≡ g b)
  --                → (x : ∣ F ∣F)
  --                → f x ≡ g x
  -- function-lemma f g f-sc g-sc ϕ x =
  --   f x ≡⟨ {!!} ⟩ f (⋁⟨ i ⟩ (b $ i)) ≡⟨ {!!} ⟩ {!f (⋁⟨ i ⟩ (b $ i))!} ≡⟨ {!!} ⟩ g x ∎
  --   where
  --   open JoinSyntax ∣ F ∣F (λ - → ⋁[ F ] -)

  --   b = π₀ (π₀ spec x)
```

```agda
-- patch-is-stone : [ isStone Patch ]
-- patch-is-stone = patch-is-compact , ∣ {!!} ∣
```

TODO:

1. Prove 3.3.(i)
2. Patch(A) is a Stone locale for every spectral A.
n
