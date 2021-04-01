---
title: The Initial Frame
author: Ayberk Tosun<br>(j.w.w. with Martín Escardó)
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

module Omega where

open import Basis
open import Cubical.Data.Sigma hiding (_∨_)
open import Cubical.Functions.Logic
open import Cubical.Foundations.Function
open import Poset
open import Frame
```
-->

This module contains a construction of the initial object in the category
**Frm** of frames.

## The underlying poset of the frame

Let us first write the down the partial order underlying the frame:

```agda
_≤_ : hProp 𝓤 → hProp 𝓤 → hProp 𝓤
A ≤ B = A ⇒ B
```

This gives us a poset structure at every universe 𝓤:

```agda
ΩP-str : (𝓤 : Universe) → PosetStr 𝓤 (hProp 𝓤)
ΩP-str 𝓤 = _≤_ , isSetHProp , ≤-reflexive , ≤-trans , ≤-antisym
  where
  ≤-reflexive : [ isReflexive _≤_ ]
  ≤-reflexive x = idfun _

  ≤-trans : [ isTransitive _≤_ ]
  ≤-trans _ _ _ p q = q ∘ p

  ≤-antisym : [ isAntisym isSetHProp _≤_ ]
  ≤-antisym _ _ = ⇔toPath
```

We will denote this poset by ΩP:

```agda
ΩP : (𝓤 : Universe) → Poset (𝓤 ⁺) 𝓤
ΩP 𝓤 = hProp 𝓤 , ΩP-str 𝓤
```

## Definition of the initial frame

```agda
Ω : (𝓤 : Universe) → Frame (𝓤 ⁺) 𝓤 𝓤
Ω 𝓤 =
  hProp 𝓤 , (ΩP-str 𝓤 , top 𝓤 , _⊓_ , ⋁_) , is-top , is-glb , is-lub , distr
  where
  ⋁_ : Fam 𝓤 (hProp 𝓤) → hProp 𝓤
  ⋁ (I , f) = ∥ (Σ[ i ∈ I ] [ f i ]) ∥Ω

  is-top : [ isTop (ΩP 𝓤) (top 𝓤) ]
  is-top _ _ = tt

  is-glb : [ isGLB (ΩP 𝓤) _⊓_ ]
  is-glb = (λ _ _ → fst , snd) , λ x y z p q → fst p q , snd p q

  is-lub : [ isLUB (ΩP 𝓤) ⋁_ ]
  is-lub = (λ { U _ (i , eq) q → ∣ i , subst [_] (sym eq) q ∣ }) , nts
    where
    nts : (U : Fam 𝓤 (hProp 𝓤)) (A : hProp 𝓤)
        → [ ∀[ B ε U ] (B ≤ A) ⇒ (⋁ U) ≤ A ]
    nts U x p q = ∥∥-rec (isProp[] x) rem q
      where
      rem : Σ[ i ∈ index U ] [ U $ i ] → [ x ]
      rem (i , eq) = p (U $ i) (i , refl) eq

  distr : [ isDist (ΩP 𝓤)  _⊓_ ⋁_ ]
  distr A U = ⇔toPath nts₀ nts₁
    where
    open JoinSyntax (hProp 𝓤) ⋁_

    nts₀ : _
    nts₀ (x , y) = ∥∥-rec (∥∥-prop _) (λ { (i , Uᵢ) → ∣ i , x , Uᵢ ∣ }) y

    nts₁ : [ ⋁⟨ i ⟩ (A ⊓ (U $ i)) ⇒ A ⊓ (⋁ U) ]
    nts₁ y = ∥∥-rec (isProp[] (A ⊓ (⋁ U))) (λ { (i , x , y) → x , ∣ i , y ∣ }) y
```

## Initiality

We now construct, for each frame $A$, a frame homomorphism ‼ : Ω → A. Let us
start by writing down the underlying function:

```agda
∣‼∣ : (A : Frame 𝓦 𝓥 𝓤) → hProp 𝓤 → ∣ A ∣F
∣‼∣ A P = ⋁[ A ] ⁅ ⊤[ A ] ∣ _ ∶ [ P ] ⁆
```

### ‼ is monotonic

This is a monotonic map between the underlying frames:

```agda
∣‼∣-mono : (A : Frame 𝓦 𝓥 𝓤) → isMonotonic (ΩP 𝓤) (pos A) (∣‼∣ A)
∣‼∣-mono A P Q P≤Q =
  ⋁[ A ]-least _ (∣‼∣ A Q) nts
  where
  nts : _
  nts x (p , eq) = ⋁[ A ]-upper _ _ (P≤Q p , eq)
```

```agda
‼m : (A : Frame 𝓦 𝓥 𝓤) → ΩP 𝓤 ─m→ pos A
‼m A = ∣‼∣ A , ∣‼∣-mono A
```

### ‼ is a frame homomorphism

```agda
∣‼∣-resp-⊤ : (A : Frame 𝓦 𝓥 𝓤) → ∣‼∣ A (top 𝓤) ≡ ⊤[ A ]
∣‼∣-resp-⊤ A =
  ⊑[ pos A ]-antisym _ _ (⊤[ A ]-top _) (⋁[ A ]-upper _ _ (tt , refl))
```

```agda
∣‼∣-resp-∧ : (A : Frame 𝓦 𝓥 𝓤) (P Q : hProp 𝓤)
           → ∣‼∣ A (P ⊓ Q) ≡ (∣‼∣ A P) ⊓[ A ] (∣‼∣ A Q)
∣‼∣-resp-∧ {𝓤 = 𝓤} A P Q =
  ∣‼∣ A (P ⊓ Q)                    ≡⟨ refl                           ⟩
  ⋁ ⁅ 𝟏 ∣ _ ∶ [ P ⊓ Q ] ⁆          ≡⟨ cong (λ - → ⋁ ⁅ - ∣ _ ∶ _ ⁆) p ⟩
  ⋁ ⁅ 𝟏 ⊓[ A ] 𝟏 ∣ _ ∶ [ P ⊓ Q ] ⁆ ≡⟨ sym (sym-distr A _ _ )         ⟩
  ∣‼∣ A P ⊓[ A ] ∣‼∣ A Q           ∎
  where
  𝟏  = ⊤[ A ]

  ⋁_ : Fam 𝓤 ∣ A ∣F → ∣ A ∣F
  ⋁ U = ⋁[ A ] U

  p : 𝟏 ≡ 𝟏 ⊓[ A ] 𝟏
  p = sym (x∧x=x A 𝟏)
```

```agda
∣‼∣-resp-⋁ : (A : Frame 𝓦 𝓥 𝓤) (U : Fam 𝓤 (hProp 𝓤))
           → ∣‼∣ A (⋁[ Ω 𝓤 ] U) ≡ ⋁[ A ] ⁅ ∣‼∣ A x ∣ x ε U ⁆
∣‼∣-resp-⋁ A U = ⊑[ pos A ]-antisym _ _ below above
  where
  open PosetNotation  (pos A) using () renaming (_≤_ to _⊑_)

  below : [ ∣‼∣ A (⋁[ Ω _ ] U) ⊑ (⋁[ A ] ⁅ ∣‼∣ A P ∣ P ε U ⁆) ]
  below = ⋁[ A ]-least _ _ goal
    where
    goal : _
    goal x (q , eq) = ∥∥-rec (isProp[] (_ ⊑[ pos A ] _)) rem q
      where
      rem : Σ[ i ∈ index U ] [ U $ i ] → [ x ⊑ (⋁[ A ] ⁅ ∣‼∣ A P ∣ P ε U ⁆) ]
      rem (i , p) = ⋁[ A ]-upper _ _ (i , sym (⋁-unique A _ x γ δ))
        where
        γ : _
        γ y (j , q) = subst (λ - → [ rel (pos A) y - ]) eq (⊤[ A ]-top y)

        δ : _
        δ w q = q x (p , eq)

  above : [ (⋁[ A ] ⁅ ∣‼∣ A P ∣ P ε U ⁆) ⊑ ∣‼∣ A (⋁[ Ω _ ] U) ]
  above = ⋁[ A ]-least _ _ goal
    where
    goal : _
    goal x (i , eq) = subst (λ - → [ - ⊑[ pos A ] _ ]) eq nts
      where
      rem : _
      rem x (p , eq-j) = ⋁[ A ]-upper _ _ (∣ i , p ∣ , eq-j)

      nts : [ ∣‼∣ A (U $ i) ⊑ ∣‼∣ A (⋁[ Ω _ ] U) ]
      nts = ⋁[ A ]-least _ _ rem
```

## Definition of ‼

```agda
‼ : (𝓤 : Universe) (A : Frame 𝓦 𝓥 𝓤) → Ω 𝓤 ─f→ A
‼ 𝓤 A = ‼m A , ∣‼∣-resp-⊤ A , ∣‼∣-resp-∧ A , ∣‼∣-resp-⋁ A
```

## Uniqueness of ‼

To prove uniqueness, we will need the following easy lemma:

```agda
main-lemma : (P : hProp 𝓤) → [ P ⊑[ ΩP 𝓤 ] ⋁[ Ω 𝓤 ] ⁅ top 𝓤 ∣ _ ∶ [ P ] ⁆ ]
main-lemma {𝓤 = 𝓤} P p =
  ⋁[ Ω 𝓤 ]-upper (⁅ top 𝓤 ∣ _ ∶ [ P ] ⁆) _ (p , refl) tt
```

We now prove uniqueness: given any other frame homomorphism ⁇ out of Ω, ‼ is
equal to ⁇:

```agda
‼-is-unique : (A : Frame 𝓦 𝓥 𝓤) → (⁇ : (Ω 𝓤) ─f→ A) → ‼ 𝓤 A ≡ ⁇
‼-is-unique {𝓤 = 𝓤} A ⁇@((∣⁇∣ , ⁇-mono) , (⁇-resp-⊤ , ⁇-resp-∧ , ⁇-resp-⋁)) =
  forget-homo (Ω 𝓤) A (‼ 𝓤 A) ⁇ (sym ∘ goal)
  where
  open PosetNotation  (pos A) using () renaming (_≤_ to _⊑_)
  open PosetReasoning (pos A) using (_⊑⟨_⟩_; _■)
  𝟏 = ⊤[ A ]

  goal : (P : hProp 𝓤) → ∣⁇∣ P ≡ ∣‼∣ A P
  goal P = ⋁-unique A _ _ upper-bound least
    where
    upper-bound : (x : ∣ A ∣F) → x ε ⁅ 𝟏 ∣ _ ∶ [ P ] ⁆ → [ x ⊑ ∣⁇∣ P ]
    upper-bound x (p , eq) =
      x           ⊑⟨ ≡⇒⊑ (pos A) (sym eq)       ⟩
      𝟏           ⊑⟨ ≡⇒⊑ (pos A) (sym ⁇-resp-⊤) ⟩
      ∣⁇∣ (top 𝓤) ⊑⟨ ⁇-mono (top 𝓤) P (const p) ⟩
      ∣⁇∣ P       ■

    least : (u : ∣ A ∣F)
          → ((x : ∣ A ∣F) → x ε ⁅ 𝟏 ∣ _ ∶ [ P ] ⁆ → [ x ⊑ u ]) → [ ∣⁇∣ P ⊑ u ]
    least u u-upper-bound =
      ∣⁇∣ P                                ⊑⟨ ⁇-mono P _ (main-lemma P)      ⟩
      ∣⁇∣ (⋁[ Ω 𝓤 ] ⁅ top 𝓤 ∣ p ∶ [ P ] ⁆) ⊑⟨ ≡⇒⊑ (pos A) (⁇-resp-⋁ _)       ⟩
      ⋁[ A ] ⁅ ∣⁇∣ (top 𝓤) ∣ p ∶ [ P ] ⁆   ⊑⟨ †                              ⟩
      ⋁[ A ] ⁅ ⊤[ A ] ∣ p ∶ [ P ] ⁆        ⊑⟨ ⋁[ A ]-least _ _ u-upper-bound ⟩
      u                                    ■
      where
      † : [ (⋁[ A ] ⁅ ∣⁇∣ (top 𝓤) ∣ p ∶ [ P ] ⁆) ⊑ (⋁[ A ] ⁅ 𝟏 ∣ p ∶ [ P ] ⁆) ]
      † = ≡⇒⊑ (pos A) (cong (λ - → (⋁[ A ] ⁅ - ∣ p ∶ [ P ] ⁆)) ⁇-resp-⊤)
```

```agda
ΩF-initial : (A : Frame 𝓦 𝓥 𝓤) → isContr (Ω 𝓤 ─f→ A)
ΩF-initial {𝓤 = 𝓤} A = ‼ 𝓤 A , ‼-is-unique A
```
