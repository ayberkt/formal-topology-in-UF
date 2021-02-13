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

⊤ : ∣ 𝔖 ∣F
⊤ = (Q , Q-dc) , fix
  where
  Q : 𝒫 ∣ 𝕊-pos ∣ₚ
  Q _ = Unit 𝓤₀ , Unit-prop

  Q-dc : [ isDownwardsClosed 𝕊-pos Q ]
  Q-dc _ _ _ _ = tt

  fix : NucleusFrom.𝕛 𝕊 (Q , Q-dc) ≡ (Q , Q-dc)
  fix = ⊑[ DCPoset 𝕊-pos ]-antisym _ _ α β
    where
    α : [ (NucleusFrom.𝕛 𝕊 (Q , Q-dc)) ⊑[ DCPoset 𝕊-pos ] (Q , Q-dc) ]
    α _ _ = tt

    β : [ rel (DCPoset 𝕊-pos) (Q , Q-dc) (NucleusFrom.𝕛 𝕊 (Q , Q-dc)) ]
    β _ _ = dir tt
```

```agda
open import Cover
open CoverFromFormalTopology 𝕊 hiding (_◁_)

thm-foo : (U : ∣ 𝔖 ∣F) (b : Bool 𝓤₀) → b ◁ ⦅ U ⦆ → [ b ∈ ⦅ U ⦆ ]
thm-foo U b (dir p) = p
thm-foo U b (squash p q i) =
  isProp[] (b ∈ (π₀ (π₀ U))) (thm-foo U b p) (thm-foo U b q) i
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
  to ((f , _) , _) = f ⊤
```

```agda
  lemma : (F : Frame 𝓤 𝓥 𝓦) (I : 𝓦 ̇) (x : ∣ F ∣F) → ∥ I ∥ → ⋁[ F ] ⁅ x ∣ _ ∶ I ⁆ ≡ x
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
  from₀ : ∣ A ∣F → ∣ 𝔖 ∣F → ∣ A ∣F
  from₀ x 𝔘 =
    (⋁ ⁅ x ∣ _ ∶ [ true ∈ ⦅ 𝔘 ⦆ ] ⁆) ∨ (⋁ ⁅ 𝟏 ∣ _ ∶ [ false ∈ ⦅ 𝔘 ⦆ ] ⁆)
```

#### Monotonicity

```agda
  from₀-mono : (x : ∣ A ∣F) → isMonotonic (pos 𝔖) (pos A) (from₀ x)
  from₀-mono x 𝔘 𝔙 𝔘⊆𝔙 = ⋁[ A ]-least _ _ nts
    where
    nts : _
    nts y (true  , p₀) =
      subst (λ - → [ - ⊑[ pos A ] _ ]) p₀ (⋁[ A ]-least _ _ nts′)
      where
      nts′ : _
      nts′ z (b , p₁) =
        ⋁[ A ]-upper _ _ (true , subst (_ ≡_) p₁ (lemma A _ _ ∣ 𝔘⊆𝔙 true b ∣))
    nts y (false , eq) =
      subst (λ - → [ - ⊑[ pos A ] _ ]) eq (⋁[ A ]-least _ _ nts′) 
      where
      nts′ : _
      nts′ z (b , p₁) =
        ⋁[ A ]-upper _ _ (false , subst (_ ≡_) p₁ (lemma A _ _ ∣ 𝔘⊆𝔙 false b ∣))
{--
```

```agda
  from₀m : ∣ A ∣F → pos 𝔖 ─m→ pos A
  from₀m x = from₀ x , from₀-mono x
```

#### Continuity

```agda
  resp-⊤ : (x : ∣ A ∣F) → from₀ x ⊤[ 𝔖 ] ≡ ⊤[ A ]
  resp-⊤ x = ⊑[ pos A ]-antisym _ _ (⊤[ A ]-top _) nts
    where
    nts : [ ⊤[ A ] ⊑[ pos A ] from₀ x ⊤[ 𝔖 ] ]
    nts = ⋁[ A ]-upper _ _ (false , lemma A _ ⊤[ A ] ∣ tt ∣)
```

```agda
  from₀-comm-∧ : (x : ∣ A ∣F) (𝔘 𝔙 : ∣ 𝔖 ∣F)
               → from₀ x (𝔘 ⊓[ 𝔖 ] 𝔙) ≡ (from₀ x 𝔘) ∧ (from₀ x 𝔙)
  from₀-comm-∧ x 𝔘 𝔙 = nts
    where
    ϕ : [ from₀ x (𝔘 ⊓[ 𝔖 ] 𝔙) ⊑[ pos A ] from₀ x 𝔘 ]
    ϕ = from₀-mono x (𝔘 ⊓[ 𝔖 ] 𝔙) 𝔘 (⊓[ 𝔖 ]-lower₀ 𝔘 𝔙)

    ψ : [ from₀ x (𝔘 ⊓[ 𝔖 ] 𝔙) ⊑[ pos A ] from₀ x 𝔙 ]
    ψ = from₀-mono x (𝔘 ⊓[ 𝔖 ] 𝔙) 𝔙 (⊓[ 𝔖 ]-lower₁ 𝔘 𝔙)

    nts₀ : [ from₀ x (𝔘 ⊓[ 𝔖 ] 𝔙) ⊑[ pos A ] from₀ x 𝔘 ∧ from₀ x 𝔙 ]
    nts₀ = ⊓[ A ]-greatest _ _ _ ϕ ψ

    nts₁ : [ from₀ x 𝔘 ∧ from₀ x 𝔙 ⊑[ pos A ] from₀ x (𝔘 ⊓[ 𝔖 ] 𝔙) ]
    nts₁ = {!⊑[ pos A ]-antisym _ _ ? ?!}

    nts′ : from₀ x (𝔘 ⊓[ 𝔖 ] 𝔙) ≡ ⋁ ⁅ (⁅ ⋁ (⁅ x ∣ _ ∶ [ true ∈ ⦅ 𝔘 ⦆ ] ⁆) , ⋁ (⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ ⦅ 𝔘 ⦆ ] ⁆) ⁆ $ p) ∧ (⁅ {!!} , {!!} ⁆ $ q) ∣ (p , q) ∶ Bool 𝓤₀ × Bool 𝓤₀ ⁆
    nts′ = {!■substeq!}

    nts : from₀ x (𝔘 ⊓[ 𝔖 ] 𝔙) ≡ (from₀ x 𝔘) ∧ (from₀ x 𝔙)
    nts = from₀ x (𝔘 ⊓[ 𝔖 ] 𝔙)                                                                                       ≡⟨ refl ⟩
          ((⋁ ⁅ x ∣ _ ∶ [ true ∈ ⦅ 𝔘 ⊓[ 𝔖 ] 𝔙 ⦆ ] ⁆) ∨ (⋁ ⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ ⦅ 𝔘 ⊓[ 𝔖 ] 𝔙 ⦆ ] ⁆))              ≡⟨ nts′ ⟩
          (⋁ ⁅ _ ∧ _ ∣ _ ∶ Bool 𝓤₀ × Bool 𝓤₀ ⁆)                                                                      ≡⟨ sym (sym-distr A _ _) ⟩
          (((⋁ ⁅ x ∣ _ ∶ [ true ∈ ⦅ 𝔘 ⦆ ] ⁆) ∨ (⋁ ⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ ⦅ 𝔘 ⦆ ] ⁆)) ∧ ((⋁ ⁅ x ∣ _ ∶ [ true ∈ ⦅ 𝔙 ⦆ ] ⁆) ∨ (⋁ ⁅ ⊤[ A ] ∣ _ ∶ [ false ∈ ⦅ 𝔙 ⦆ ] ⁆))) ≡⟨ refl ⟩
          from₀ x 𝔘 ∧ from₀ x 𝔙     ∎
```

```agda
  from₀-comm-⋁ : (x : ∣ A ∣F) (W : Fam 𝓤₀ ∣ 𝔖 ∣F)
               → from₀ x (⋁[ 𝔖 ] W) ≡ (⋁[ A ] ⁅ from₀ x 𝔘 ∣ 𝔘 ε W ⁆)
  from₀-comm-⋁ = {!!}
```

```agda
  from₀-cont : (x : ∣ A ∣F) → isFrameHomomorphism 𝔖 A (from₀m x)
  from₀-cont x = resp-⊤ x , from₀-comm-∧ x  , from₀-comm-⋁ x
```

We are now ready to write down the inverse of `to`.

```agda
  from : ∣ A ∣F → 𝔖 ─f→ A
  from x = (from₀ x , from₀-mono x) , from₀-cont x
```

#### Section

```agda
  sec : section to from
  sec = {!!}
```

#### Retraction

```agda
  ret : retract to from
  ret = {!!}
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
