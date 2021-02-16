---
title: Sierpinski
---

```agda
{-# OPTIONS --cubical --safe #-}

module Sierpinski where

open import Basis hiding (_∨_)
open import Poset
open import FormalTopology renaming (pos to pos′)
open import Cubical.Data.Fin
open import Cubical.Data.Sum
open import Cubical.Data.Empty using () renaming (rec to ⊥-rec)
open import Cubical.Data.Nat hiding (Unit)
open import Frame
open import Cofinality

𝕊-pos : Poset ℓ-zero ℓ-zero
𝕊-pos = Bool 𝓤₀ , (_≤_ , Bool-set , ≤-refl , ≤-trans , ≤-antisym)
  where
  _≤_ : Bool 𝓤₀ → Bool 𝓤₀ → hProp ℓ-zero
  _     ≤ false = Unit ℓ-zero , Unit-prop
  true  ≤ true  = Unit ℓ-zero , Unit-prop
  _     ≤ _     = bot ℓ-zero

  ≤-refl : (x : Bool 𝓤₀) → [ x ≤ x ]
  ≤-refl false = tt
  ≤-refl true  = tt

  ≤-trans : (x y z : Bool 𝓤₀) → [ x ≤ y ] → [ y ≤ z ] → [ x ≤ z ]
  ≤-trans _ true true  p _ = p
  ≤-trans _ _    false _ _ = tt

  ≤-antisym : (x y : Bool 𝓤₀) → [ x ≤ y ] → [ y ≤ x ] → x ≡ y
  ≤-antisym false false p q = refl
  ≤-antisym true  true  p q = refl
```

The empty interaction system.

```agda
𝕊-exp : Bool 𝓤₀ → Type ℓ-zero
𝕊-exp _ = 𝟘 ℓ-zero

𝕊-out : {x : Bool 𝓤₀} → 𝕊-exp x → Type ℓ-zero
𝕊-out ()

𝕊-rev : {x : Bool 𝓤₀} {y : 𝕊-exp x} → 𝕊-out {x} y → Bool 𝓤₀
𝕊-rev {y = ()}

𝕊-IS : InteractionStr (Bool 𝓤₀)
𝕊-IS = 𝕊-exp , (λ {x} → 𝕊-out {x}) , 𝕊-rev

𝕊 : FormalTopology 𝓤₀ 𝓤₀
𝕊 = 𝕊-pos , 𝕊-IS , 𝕊-has-mono , 𝕊-has-sim
  where
  𝕊-has-mono : hasMono 𝕊-pos 𝕊-IS
  𝕊-has-mono _ () _

  𝕊-has-sim  : hasSimulation 𝕊-pos 𝕊-IS
  𝕊-has-sim _ _ _ ()

open import UniversalProperty
open import CoverFormsNucleus

open NucleusFrom 𝕊

𝔖 : Frame 𝓤₁ 𝓤₀ 𝓤₀
𝔖 = NucleusFrom.L 𝕊

open import Cover

thm-foo : (U : 𝒫 (Bool 𝓤₀)) (b : Bool 𝓤₀) → b ◁ U → [ b ∈ U ]
thm-foo U b (dir p) = p
thm-foo U b (squash p q i) =
  isProp[] (b ∈ U) (thm-foo U b p) (thm-foo U b q) i

⁅⊤⁆ : ∣ 𝔖 ∣F
⁅⊤⁆ = (Q , Q-dc) , fix
  where
  Q : 𝒫 ∣ 𝕊-pos ∣ₚ
  Q x = (x ≡ true) , Bool-set x true

  Q-dc : [ isDownwardsClosed 𝕊-pos Q ]
  Q-dc true  true  x∈Q _ = x∈Q
  Q-dc false true  x∈Q _ = ⊥-rec (true≠false (sym x∈Q))
  Q-dc false false x∈Q _ = x∈Q

  fix : NucleusFrom.𝕛 𝕊 (Q , Q-dc) ≡ (Q , Q-dc)
  fix = Σ≡Prop (isProp[] ∘ isDownwardsClosed 𝕊-pos) (⊆-antisym (thm-foo Q) (λ _ → dir))

⊤-lemma : (𝔘 : ∣ 𝔖 ∣F) → [ true ∈ ⦅ 𝔘 ⦆ ] → [ ⁅⊤⁆ ⊑[ pos 𝔖 ] 𝔘 ]
⊤-lemma 𝔘 p true  q = p
⊤-lemma 𝔘 p false q = ⊥-rec (true≠false (sym q))

𝔖-equality : (𝔘 𝔙 : ∣ 𝔖 ∣F) → ⦅ 𝔘 ⦆ ≡ ⦅ 𝔙 ⦆ → 𝔘 ≡ 𝔙
𝔖-equality 𝔘 𝔙 p = Σ≡Prop nts₀ (Σ≡Prop nts₁ p)
  where
  nts₀ : (U : ∣ DCPoset 𝕊-pos ∣ₚ) → isProp (𝕛 U ≡ U)
  nts₀ U = carrier-is-set (DCPoset 𝕊-pos) (𝕛 U) U

  nts₁ : (U : 𝒫 ∣ 𝕊-pos ∣ₚ) → isProp [ isDownwardsClosed 𝕊-pos U ]
  nts₁ U = isProp[] (isDownwardsClosed 𝕊-pos U)

⁅⊤⁆=η-true : ⁅⊤⁆ ≡ η true
⁅⊤⁆=η-true = Σ≡Prop nts₀ (Σ≡Prop nts₁ goal)
  where
  nts₀ : (U : ∣ DCPoset 𝕊-pos ∣ₚ) → isProp (𝕛 U ≡ U)
  nts₀ U = carrier-is-set (DCPoset 𝕊-pos) (𝕛 U) U

  nts₁ : (U : 𝒫 ∣ 𝕊-pos ∣ₚ) → isProp [ isDownwardsClosed 𝕊-pos U ]
  nts₁ U = isProp[] (isDownwardsClosed 𝕊-pos U)

  goal₀ : [ η true .π₀ .π₀ ⊆ ⁅⊤⁆ .π₀ .π₀ ]
  goal₀ true (dir _)        = refl
  goal₀ b    (squash p q i) = isProp[] (b ∈ ⦅ ⁅⊤⁆ ⦆) (goal₀ b p) (goal₀ b q ) i

  goal : ⁅⊤⁆ .π₀ .π₀ ≡ η true .π₀ .π₀
  goal = ⊆-antisym (⊤-lemma (η true) (dir tt)) goal₀

𝟏=η-false : ⊤[ 𝔖 ] ≡ η false
𝟏=η-false = 𝔖-equality ⊤[ 𝔖 ] (η false) (⊆-antisym goal λ _ _ → tt) 
  where
  goal : [ ⦅ ⊤[ 𝔖 ] ⦆ ⊆ ⦅ η false ⦆ ]
  goal true  x₁ = π₁ (π₀ (η false)) true _ (dir tt) tt
  goal false x₁ = dir (⊑[ 𝕊-pos ]-refl false)

true∈⊤𝔖 : [ true ∈ ⦅ ⊤[ 𝔖 ] ⦆ ]
true∈⊤𝔖 = tt

_≠∅ : (U : ∣ 𝔖 ∣F) → 𝓤₀ ̇
𝔘 ≠∅ = [ true ∈ ⦅ 𝔘 ⦆ ] ⊎ [ false ∈ ⦅ 𝔘 ⦆ ]
```

## Is this the correct Sierpinski space?

Fix a frame `A` whose index types are small.

```agda
module _ (A : Frame 𝓤 𝓥 𝓤₀) where
```

We will use the following shorthand for `A`'s operations:

```
  ⋁_ : Fam 𝓤₀ ∣ A ∣F → ∣ A ∣F
  ⋁ U = ⋁[ A ] U

  _∨_ : ∣ A ∣F → ∣ A ∣F → ∣ A ∣F
  x ∨ y = x ∨[ A ] y

  _∧_ : ∣ A ∣F → ∣ A ∣F → ∣ A ∣F
  x ∧ y = x ⊓[ A ] y

  _≤_ : ∣ A ∣F → ∣ A ∣F → hProp 𝓥
  x ≤ y = x ⊑[ pos A ] y 

  𝟏 : ∣ A ∣F
  𝟏 = ⊤[ A ]
```

### The easy direction

```agda
  to : (𝔖 ─f→ A) → ∣ A ∣F
  to ((f , _) , _) = f ⁅⊤⁆
```

```agda
  lemma : (F : Frame 𝓤 𝓥 𝓦) (I : 𝓦 ̇) (x : ∣ F ∣F)
        → ∥ I ∥ → ⋁[ F ] ⁅ x ∣ _ ∶ I ⁆ ≡ x
  lemma F I x ∣i∣ = ∥∥-rec (carrier-is-set (pos F) _ _) f ∣i∣
    where
    f : I → ⋁[ F ] ⁅ x ∣ _ ∶ I ⁆ ≡ x
    f i = ⊑[ pos F ]-antisym _ _ (⋁[ F ]-least _ _ nts) (⋁[ F ]-upper _ _ (i , refl))
      where
      nts : _
      nts _ (_ , eq) = ≡⇒⊑ (pos F) (sym eq)
```

### The converse direction

```agda
  _==>_ : hProp 𝓤₀ → ∣ A ∣F → Fam 𝓤₀ ∣ A ∣F
  p ==> x = ⁅ x ∣ _ ∶ [ p ] ⁆

  infixr 3 _==>_

  𝔨 : ∣ A ∣F → ∣ 𝔖 ∣F → Fam 𝓤₀ ∣ A ∣F
  𝔨 x 𝔘 = (true ∈ ⦅ 𝔘 ⦆ ==> x) ∪f (false ∈ ⦅ 𝔘 ⦆ ==> ⊤[ A ])

  from₀ : ∣ A ∣F → ∣ 𝔖 ∣F → ∣ A ∣F
  from₀ x 𝔘 = ⋁ 𝔨 x 𝔘

  from-lemma₀ : (x : ∣ A ∣F) → from₀ x ⁅⊤⁆ ≡ x
  from-lemma₀ x = ⊑[ pos A ]-antisym _ _ nts₀ nts₁
    where
    nts₀ : [ from₀ x ⁅⊤⁆ ⊑[ pos A ] x ]
    nts₀ = ⋁[ A ]-least _ _ λ { y (inl i , eq) → ≡⇒⊑ (pos A) (sym eq)
                              ; y (inr i , eq) → ⊥-rec (true≠false (sym i))
                              }

    nts₁ : [ x ⊑[ pos A ] from₀ x ⁅⊤⁆ ]
    nts₁ = ⋁[ A ]-upper _ _ (inl refl , refl)

  from-lemma₁ : (x : ∣ A ∣F) → from₀ x ⊤[ 𝔖 ] ≡ ⊤[ A ]
  from-lemma₁ x =
    ⊑[ pos A ]-antisym _ _ (⊤[ A ]-top _) (⋁[ A ]-upper _ _ (inr tt , refl))

  from-lemma₂ : (x : ∣ A ∣F) → from₀ x ⊥[ 𝔖 ] ≡ ⊥[ A ]
  from-lemma₂ x = ⊑[ pos A ]-antisym _ _ nts (⊥[ A ]-bottom _)
    where
    nts′ : [ ∀[ z ε _ ] (z ≤ ⊥[ A ]) ]
    nts′ z (inl (dir p)        , eq) = ∥∥-rec (isProp[] (_ ≤ _)) (λ { (() , _) }) p
    nts′ z (inl (squash p q i) , eq) = isProp[] (_ ≤ _) (nts′ z (inl p , eq)) (nts′ z (inl q , eq)) i
    nts′ z (inr (dir p)        , eq) = ∥∥-rec (isProp[] (_ ≤ _)) (λ { (() , _) }) p
    nts′ z (inr (squash p q i) , eq) = isProp[] (_ ≤ _) (nts′ z (inr p , eq)) (nts′ z (inr q , eq)) i

    nts : [ (from₀ x ⊥[ 𝔖 ]) ≤ ⊥[ A ] ]
    nts = ⋁[ A ]-least _ _ nts′

  another-lemma : (𝔘 : ∣ 𝔖 ∣F) → [ false ∈ ⦅ 𝔘 ⦆ ] → ⦅ 𝔘 ⦆ ≡ entire
  another-lemma ((U , U-dc) , _) false∈𝔘 = funExt nts
    where
    f : [ true ∈ U ] → entire true .π₀
    f x = tt

    g : entire true .π₀ → [ true ∈ U ]
    g x = U-dc false true false∈𝔘 tt

    sec : section f g
    sec tt = refl

    ret : retract f g
    ret p = isProp[] (true ∈ U) (U-dc false true false∈𝔘 tt) p

    f′ : [ false ∈ U ] → entire true .π₀
    f′ x = tt

    g′ : entire true .π₀ → [ false ∈ U ]
    g′ x = false∈𝔘

    nts : _
    nts true  = Σ≡Prop (λ _ → isPropIsProp ) (isoToPath (iso f g sec ret))
    nts false = Σ≡Prop (λ _ → isPropIsProp) (isoToPath (iso f′ g′ (Unit-prop tt) λ p → isProp[] (false ∈ U) false∈𝔘 p))

  another-lemma′ : (𝔘 : ∣ 𝔖 ∣F) → [ false ∈ ⦅ 𝔘 ⦆ ] → ⊤[ 𝔖 ] ≡ 𝔘
  another-lemma′ 𝔘 false∈𝔘 = sym (Σ≡Prop nts₀ (Σ≡Prop nts₁ nts))
    where
    nts₀ : (U : ∣ DCPoset 𝕊-pos ∣ₚ) → isProp (𝕛 U ≡ U)
    nts₀ U = carrier-is-set (DCPoset 𝕊-pos) (𝕛 U) U

    nts₁ : (U : 𝒫 ∣ 𝕊-pos ∣ₚ) → isProp [ isDownwardsClosed 𝕊-pos U ]
    nts₁ U = isProp[] (isDownwardsClosed 𝕊-pos U)

    nts : ⦅ 𝔘 ⦆ ≡ ⦅ ⊤[ 𝔖 ] ⦆
    nts = another-lemma 𝔘 false∈𝔘
```

#### Monotonicity

```agda
  from₀-mono : (x : ∣ A ∣F) → isMonotonic (pos 𝔖) (pos A) (from₀ x)
  from₀-mono x 𝔘 𝔙 𝔘⊆𝔙 = ⋁[ A ]-least _ _ nts
    where
    nts : _
    nts _ (inl i , eq) = ⋁[ A ]-upper _ _ (inl (𝔘⊆𝔙 true  i) , eq)
    nts _ (inr j , eq) = ⋁[ A ]-upper _ _ (inr (𝔘⊆𝔙 false j) , eq)
```

```agda
  from₀m : ∣ A ∣F → pos 𝔖 ─m→ pos A
  from₀m x = from₀ x , from₀-mono x
```

#### Continuity

```agda
  resp-⊤ : (x : ∣ A ∣F) → from₀ x ⊤[ 𝔖 ] ≡ ⊤[ A ]
  resp-⊤ x =
    ⊑[ pos A ]-antisym _ _ (⊤[ A ]-top _) (⋁[ A ]-upper _ _ (inr tt , refl))

```

```agda
  from₀-comm-∧ : (x : ∣ A ∣F) (𝔘 𝔙 : ∣ 𝔖 ∣F)
               → from₀ x (𝔘 ⊓[ 𝔖 ] 𝔙) ≡ (from₀ x 𝔘) ∧ (from₀ x 𝔙)
  from₀-comm-∧ x 𝔘@((_ , 𝔘-dc) , _) 𝔙@((_ , 𝔙-dc) , _) =
    from₀ x (𝔘 ⊓[ 𝔖 ] 𝔙)                    ≡⟨ refl                  ⟩
    ⋁ 𝔨 x (𝔘 ⊓[ 𝔖 ] 𝔙)                      ≡⟨ nts                   ⟩
    (⋁ ⁅ _ ∧ _ ∣ (_ , _) ∶ 𝔘 ≠∅ × 𝔙 ≠∅ ⁆ )  ≡⟨ sym (sym-distr A _ _) ⟩
    (⋁ 𝔨 x 𝔘) ∧ (⋁ 𝔨 x 𝔙)                   ≡⟨ refl                  ⟩
    (from₀ x 𝔘) ∧ (from₀ x 𝔙)               ∎
    where
    nts₀ : _
    nts₀ (inl (p , q)) = (inl p , inl q) , ≡⇒⊑ (pos A) (sym (x∧x=x A x))
    nts₀ (inr (p , q)) = (inr p , inr q) , ≡⇒⊑ (pos A) (sym (x∧x=x A ⊤[ A ]))

    nts₁ : _
    nts₁ (inl p , inl q) = inl (p , q) , ≡⇒⊑ (pos A) (x∧x=x A x)
    nts₁ (inl p , inr q) = inl (p , 𝔙-dc false true q tt) , ⊓[ A ]-lower₀ _ _
    nts₁ (inr p , inl q) = inl (𝔘-dc false true p tt , q) , ⊓[ A ]-lower₁ _ _
    nts₁ (inr p , inr q) = (inr (p , q)) , ≡⇒⊑ (pos A) (x∧x=x A ⊤[ A ])

    nts : (⋁ _) ≡ (⋁ _)
    nts = bicofinal→same-join A _ _ (nts₀ , nts₁)
```

```agda
  from₀-comm-⋁ : (x : ∣ A ∣F) (W : Fam 𝓤₀ ∣ 𝔖 ∣F)
               → from₀ x (⋁[ 𝔖 ] W) ≡ ⋁ ⁅ from₀ x 𝔘 ∣ 𝔘 ε W ⁆
  from₀-comm-⋁ x W =
    from₀ x (⋁[ 𝔖 ] W)      ≡⟨ refl ⟩
    ⋁ (⁅ x ∣ _ ∶ [ true ∈ ⦅ ⋁[ 𝔖 ] W ⦆ ] ⁆ ∪f ⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ ⦅ ⋁[ 𝔖 ] W ⦆ ] ⁆) ≡⟨ nts ⟩
    ⋁ ⁅ ⋁ (⁅ x ∣ _ ∶ [ true ∈ ⦅ 𝔘 ⦆ ] ⁆ ∪f ⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ ⦅ 𝔘 ⦆ ] ⁆) ∣ 𝔘 ε W ⁆ ≡⟨ refl ⟩
    ⋁ ⁅ from₀ x 𝔘 ∣ 𝔘 ε W ⁆ ∎
    where
    nts₀′ : [ ∀[ 𝔘 ε 𝔨 x (⋁[ 𝔖 ] W) ] (𝔘 ≤ (⋁ ⁅ from₀ x 𝔘 ∣ 𝔘 ε W ⁆)) ]
    nts₀′ 𝔘 (inl (dir p)        , r) = ∥∥-rec (isProp[] (_ ≤ _)) rem p
      where
      rem : _
      rem (q , q′) = {!q′!}
    nts₀′ 𝔘 (inl (squash p q i) , r) = {!!}
    nts₀′ 𝔘 (inr q , r) = {!!}

    nts₀ : [ (⋁ (⁅ x ∣ _ ∶ [ true ∈ ⦅ ⋁[ 𝔖 ] W ⦆ ] ⁆ ∪f ⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ ⦅ ⋁[ 𝔖 ] W ⦆ ] ⁆)) ≤ (⋁ ⁅ ⋁ (⁅ x ∣ _ ∶ [ true ∈ ⦅ 𝔘 ⦆ ] ⁆ ∪f ⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ ⦅ 𝔘 ⦆ ] ⁆) ∣ 𝔘 ε W ⁆) ]
    nts₀ = ⋁[ A ]-least _ _ nts₀′

    nts₁ : [  (⋁ ⁅ ⋁ (⁅ x ∣ _ ∶ [ true ∈ ⦅ 𝔘 ⦆ ] ⁆ ∪f ⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ ⦅ 𝔘 ⦆ ] ⁆) ∣ 𝔘 ε W ⁆) ≤ (⋁ (⁅ x ∣ _ ∶ [ true ∈ ⦅ ⋁[ 𝔖 ] W ⦆ ] ⁆ ∪f ⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ ⦅ ⋁[ 𝔖 ] W ⦆ ] ⁆)) ]
    nts₁ = ⋁[ A ]-least _ _ nts
      where
      nts : _
      nts z (i , eq) = subst (λ - → [ - ≤ _ ]) eq (⋁[ A ]-least _ _ nts′)
        where
          nts′ : _
          nts′ y (inl p , eq₁) = ⋁[ A ]-upper _ _ (inl (dir ∣ i , p ∣) , eq₁)
          nts′ y (inr q , eq₁) = ⋁[ A ]-upper _ _ ((inr (dir ∣ i , q ∣)) , eq₁)

    nts : ⋁ (⁅ x ∣ _ ∶ [ true ∈ ⦅ ⋁[ 𝔖 ] W ⦆ ] ⁆ ∪f ⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ ⦅ ⋁[ 𝔖 ] W ⦆ ] ⁆) ≡ (⋁ ⁅ ⋁ (⁅ x ∣ _ ∶ [ true ∈ ⦅ 𝔘 ⦆ ] ⁆ ∪f ⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ ⦅ 𝔘 ⦆ ] ⁆) ∣ 𝔘 ε W ⁆)
    nts = ⊑[ pos A ]-antisym _ _ nts₀ nts₁
```

```agda
  from₀-cont : (x : ∣ A ∣F) → isFrameHomomorphism 𝔖 A (from₀m x)
  from₀-cont x = resp-⊤ x , from₀-comm-∧ x  , from₀-comm-⋁ x
```

We are now ready to write down the inverse of `to`.

```agda
  from : ∣ A ∣F → 𝔖 ─f→ A
  π₀ (π₀ (from x)) = from₀ x
  π₁ (π₀ (from x)) = from₀-mono x
  π₁ (from x)      = from₀-cont x
```

#### Section

```agda
  sec : section to from
  sec x = to (from x) ≡⟨ refl ⟩ from₀ x ⁅⊤⁆ ≡⟨ from-lemma₀ x ⟩ x ∎
```

#### Retraction

```agda
  hauptsatz : (((f , _) , _) : 𝔖 ─f→ A) (𝔘 : ∣ 𝔖 ∣F)
            → ⋁[ A ] ⁅ f (η u) ∣ u ∈ ⦅ 𝔘 ⦆ ⁆ ≡ f 𝔘
  hauptsatz 𝒻@((f , _) , _ , _ , f-resp-⋁) 𝔘 =
    ⋁ ⁅ f (η u) ∣ u ∈ ⦅ 𝔘 ⦆ ⁆      ≡⟨ sym (f-resp-⋁ (⁅ η u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆)) ⟩
    f (⋁[ 𝔖 ] ⁅ η u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆) ≡⟨ sym (cong f (main-lemma 𝕊 𝔘))        ⟩
    f 𝔘                            ∎
```

```agda
  ret : retract to from
  ret 𝒻@((f , f-mono) , f-resp-⊤ , r-resp-∧ , _) =
    forget-homo 𝔖 A (from (to 𝒻)) 𝒻 goal
    where
    goal : (𝔘 : ∣ 𝔖 ∣F) → from (to 𝒻) .π₀ .π₀ 𝔘 ≡ f 𝔘
    goal 𝔘 = sym (⋁-unique A _ _ nts₀ nts₁)
      where
      open PosetReasoning (pos A)

      nts₀ : (x : ∣ A ∣F) → x ε 𝔨 (to 𝒻) 𝔘 → [ x ≤ (f 𝔘) ]
      nts₀ x (inl i , eq) = subst (λ - → [ - ≤ f 𝔘 ]) eq nts₀′
        where
        ⦅𝟏⦆ : [ f ⁅⊤⁆ ≤ f 𝔘 ]
        ⦅𝟏⦆ = f-mono _ _ (⊤-lemma 𝔘 i) 

        nts₀′ : [ (𝔨 (f ⁅⊤⁆) 𝔘 $ inl i) ≤ f 𝔘 ]
        nts₀′ = ⁅ f ⁅⊤⁆ ∣ _ ∶ [ true ∈ ⦅ 𝔘 ⦆ ] ⁆ $ i ⊑⟨ ≡⇒⊑ (pos A) refl ⟩
                f ⁅⊤⁆                                ⊑⟨ ⦅𝟏⦆              ⟩
                f 𝔘                                  ■
      nts₀ x (inr j , eq) = subst (λ - → [ - ≤ f 𝔘 ]) eq (≡⇒⊑ (pos A) p)
        where
        p : 𝔨 (to 𝒻) 𝔘 $ inr j ≡ f 𝔘
        p = 𝔨 (to 𝒻) 𝔘 $ inr j ≡⟨ refl                        ⟩
            ⊤[ A ]             ≡⟨ sym f-resp-⊤                ⟩
            f ⊤[ 𝔖 ]           ≡⟨ cong f (another-lemma′ 𝔘 j) ⟩
            f 𝔘                ∎

      nts₁ : (u : ∣ A ∣F)
           → ((x : ∣ A ∣F) → x ε 𝔨 (to 𝒻) 𝔘 → [ x ≤ u ]) → [ f 𝔘 ≤ u ]
      nts₁ u p = subst (λ - → [ - ≤ u ]) (hauptsatz 𝒻 𝔘) rem
        where
        aux₀ : [ false ∈ ⦅ 𝔘 ⦆ ] → [ ⊤[ A ] ≤ u ]
        aux₀ q = p ⊤[ A ] (inr q , refl)

        aux₁ : [ true ∈ ⦅ 𝔘 ⦆ ] → [ f ⁅⊤⁆ ≤ u ]
        aux₁ q = p (f ⁅⊤⁆) (inl q , refl)

        rem′ : [ ∀[ z ε ⁅ f (η u) ∣ u ∈ ⦅ 𝔘 ⦆ ⁆ ] (z ≤ u) ]
        rem′ z ((true  , q) , eq) = subst (λ - → [ - ≤ u ]) eq (f (η true) ⊑⟨ ≡⇒⊑ (pos A) (cong f (sym ⁅⊤⁆=η-true)) ⟩ f ⁅⊤⁆ ⊑⟨ aux₁ q  ⟩ u ■)
        rem′ z ((false , q) , eq) = subst (λ - → [ - ≤ u ]) eq (f (η false) ⊑⟨ ≡⇒⊑ (pos A) (cong f (sym 𝟏=η-false)) ⟩ f ⊤[ 𝔖 ] ⊑⟨ ≡⇒⊑ (pos A) f-resp-⊤ ⟩ ⊤[ A ] ⊑⟨ aux₀ q ⟩ u ■)

        rem : [ (⋁[ A ] ⁅ f (η u) ∣ u ∈ ⦅ 𝔘 ⦆ ⁆) ≤ u ]
        rem = ⋁[ A ]-least _ _ rem′

```

```agda
  𝔖-correct : (𝔖 ─f→ A) ≃ ∣ A ∣F
  𝔖-correct = isoToEquiv (iso to from sec ret)
--             nts′ : [ ⋁[ A ] (⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ U ] ⁆) ⊑[ pos A ] _ ]
--             nts′ = ⋁[ A ]-least _ _ nts′′

--       q : isFrameHomomorphism 𝔖 A (f , f-mono)
--       q = resp-⊤ , resp-∧ , {!!}
--         where
--         resp-⊤ : f ⊤[ 𝔖 ] ≡ ⊤[ A ]
--         resp-⊤ = ⊑[ pos A ]-antisym _ _ (⊤[ A ]-top _) (⋁[ A ]-upper _ _ (false , lemma A [ false ∈ ⦅ ⊤[ 𝔖 ] ⦆ ] ⊤[ A ] ∣ tt ∣))

--         resp-∧ : (U V : ∣ 𝔖 ∣F) → f (U ⊓[ 𝔖 ] V) ≡ f U ⊓[ A ] f V
--         resp-∧ U V = ⊑[ pos A ]-antisym _ _ nts₀ nts₁
--           where
--           nts₀ : [ (f (U ⊓[ 𝔖 ] V)) ⊑[ pos A ] (f U ⊓[ A ] f V) ]
--           nts₀ = ⊓[ A ]-greatest _ _ _ (f-mono (U ⊓[ 𝔖 ] V) U (⊓[ 𝔖 ]-lower₀ U V)) (f-mono (U ⊓[ 𝔖 ] V) V (⊓[ 𝔖 ]-lower₁ U V))

--           nts₁ : [ (f U ⊓[ A ] f V) ⊑[ pos A ] f (U ⊓[ 𝔖 ] V) ]
--           nts₁ = {!!}
--

-- --}
```
