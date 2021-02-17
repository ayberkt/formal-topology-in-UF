---
title: Sierpiński
author: Ayberk Tosun (j.w.w. Martín Escardó)
---

<!--
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
open import CoverFormsNucleus

to-frame : FormalTopology 𝓤 𝓤 → Frame (𝓤 ⁺) 𝓤 𝓤
to-frame = NucleusFrom.L
```
-->

We present a construction of the Sierpiński frame from a formal topology in
cubical Agda. Essentially, we prove the following:

> there exists a formal topology ℱ such that the frame generated from ℱ
> classifies the opens of any locale.

In Agda, we express this as follows:

```agda
sierpiński-exists : Σ[ S ∈ FormalTopology 𝓤₀ 𝓤₀ ]
                     ((A : Frame 𝓤₁ 𝓤₀ 𝓤₀) → (to-frame S ─f→ A) ≃ ∣ A ∣F)
```

You can click [here](#15058) to jump directly to the inhabitant of this type
that we construct, and follow the construction in a top-down manner. Otherwise,
you can continue reading and follow in a bottom-up manner.

## Sierpiński formal topology

We start by writing down our poset of basic opens, which is the following
two element poset:

```text
        false
          |
          |
          |
        true
```

It is a bit counterintuitive that `true` is less than `false` but we are working
with opposites of the usual “information ordering” posets from domain theory.

```agda
S-pos : (𝓤 𝓥 : Universe) → Poset 𝓤 𝓥
S-pos 𝓤 𝓥 = Bool 𝓤 , (_≤_ , Bool-set , ≤-refl , ≤-trans , ≤-antisym)
  where
  _≤_ : Bool 𝓤 → Bool 𝓤 → hProp 𝓥
  _     ≤ false = Unit 𝓥 , Unit-prop
  true  ≤ true  = Unit 𝓥 , Unit-prop
  _     ≤ _     = bot 𝓥

  ≤-refl : (x : Bool 𝓤) → [ x ≤ x ]
  ≤-refl false = tt
  ≤-refl true  = tt

  ≤-trans : (x y z : Bool 𝓤) → [ x ≤ y ] → [ y ≤ z ] → [ x ≤ z ]
  ≤-trans _ true true  p _ = p
  ≤-trans _ _    false _ _ = tt

  ≤-antisym : (x y : Bool 𝓤) → [ x ≤ y ] → [ y ≤ x ] → x ≡ y
  ≤-antisym false false p q = refl
  ≤-antisym true  true  p q = refl
```

The Sierpiński formal topology is obtained by equipping this poset with the
empty interaction system, which ensures that the inductively generated covering
relation is trivial.

```agda
S : (𝓤 𝓥 : Universe) → FormalTopology 𝓤 𝓥
S 𝓤 𝓥 = S-pos 𝓤 𝓥 , S-IS , S-has-mono , S-has-sim
  where
  S-exp : Bool 𝓤 → 𝓤 ̇
  S-exp _ = 𝟘 𝓤

  S-out : {x : Bool 𝓤} → S-exp x → 𝓤 ̇
  S-out ()

  S-rev : {x : Bool 𝓤} {y : S-exp x} → S-out {x = x} y → Bool 𝓤
  S-rev {y = ()}

  S-IS : InteractionStr (Bool 𝓤)
  S-IS = S-exp , (λ {x} → S-out {x = x}) , S-rev

  S-has-mono : hasMono (S-pos 𝓤 𝓥) S-IS
  S-has-mono _ () _

  S-has-sim  : hasSimulation (S-pos 𝓤 𝓥) S-IS
  S-has-sim _ _ _ ()
```

## The Sierpiński frame

The Sierpínski frame 𝕊 is defined simply as `to-frame S`:

```agda
𝕊 : Frame 𝓤₁ 𝓤₀ 𝓤₀
𝕊 = to-frame (S 𝓤₀ 𝓤₀)
```

First of all, notice that the covering is trivial:

<!--
```agda
open NucleusFrom (S 𝓤₀ 𝓤₀)
```
-->

```agda
◁-triv : (U : 𝒫 (Bool 𝓤₀)) (b : Bool 𝓤₀) → b ◁ U → [ b ∈ U ]
◁-triv U b (dir p)        = p
◁-triv U b (squash p q i) = isProp[] (b ∈ U) (◁-triv U b p) (◁-triv U b q) i
```

Let us write down the fact that equality in the Sierpiński frame reduces to
equality of the underlying sets:

```agda
𝕊-equality : (𝔘 𝔙 : ∣ 𝕊 ∣F) → ⦅ 𝔘 ⦆ ≡ ⦅ 𝔙 ⦆ → 𝔘 ≡ 𝔙
𝕊-equality 𝔘 𝔙 p = Σ≡Prop nts₀ (Σ≡Prop nts₁ p)
  where
  nts₀ : (U : ∣ DCPoset (S-pos _ _) ∣ₚ) → isProp (𝕛 U ≡ U)
  nts₀ U = carrier-is-set (DCPoset (S-pos 𝓤₀ 𝓤₀)) (𝕛 U) U

  nts₁ : (U : 𝒫 ∣ S-pos 𝓤₀ 𝓤₀ ∣ₚ) → isProp [ isDownwardsClosed (S-pos 𝓤₀ 𝓤₀) U ]
  nts₁ U = isProp[] (isDownwardsClosed (S-pos 𝓤₀ 𝓤₀) U)
```

There are three inhabitants of the Sierpinski frame so let us write this down
to make things a bit more concrete.

The singleton set containing true:

```agda
⁅true⁆ : ∣ 𝕊 ∣F
⁅true⁆ = (Q , Q-dc) , fix
  where
  Q : 𝒫 ∣ S-pos 𝓤₀ 𝓤₀ ∣ₚ
  Q x = (x ≡ true) , Bool-set x true

  Q-dc : [ isDownwardsClosed (S-pos 𝓤₀ 𝓤₀) Q ]
  Q-dc true  true  x∈Q _ = x∈Q
  Q-dc false true  x∈Q _ = ⊥-rec (true≠false (sym x∈Q))
  Q-dc false false x∈Q _ = x∈Q

  fix : 𝕛 (Q , Q-dc) ≡ (Q , Q-dc)
  fix = Σ≡Prop
          (isProp[] ∘ isDownwardsClosed (S-pos _ _))
          (⊆-antisym (◁-triv Q) (λ _ → dir))
```

Note that this is the same thing as `η true` i.e. the set `_ ◁ ⁅ true ⁆`:

```agda
⊤-lemma : (𝔘 : ∣ 𝕊 ∣F) → [ true ∈ ⦅ 𝔘 ⦆ ] → [ ⁅true⁆ ⊑[ pos 𝕊 ] 𝔘 ]
⊤-lemma 𝔘 p true  q = p
⊤-lemma 𝔘 p false q = ⊥-rec (true≠false (sym q))

⁅true⁆=η-true : ⁅true⁆ ≡ η true
⁅true⁆=η-true = 𝕊-equality _ _ (⊆-antisym (⊤-lemma (η true) (dir tt)) goal)
  where
  goal : [ ⦅ η true ⦆ ⊆ ⦅ ⁅true⁆ ⦆ ]
  goal true (dir p)     = refl
  goal b (squash p q i) = isProp[] (b ∈ ⦅ ⁅true⁆ ⦆) (goal b p) (goal b q) i
```

The top element `⊤[ 𝕊 ]` which is the set containing both `true` and `false`. It
is the same thing as the downwards-closure of `η false`.

```agda
𝟏=η-false : ⊤[ 𝕊 ] ≡ η false
𝟏=η-false = 𝕊-equality ⊤[ 𝕊 ] (η false) (⊆-antisym goal λ _ _ → tt) 
  where
  goal : [ ⦅ ⊤[ 𝕊 ] ⦆ ⊆ ⦅ η false ⦆ ]
  goal true  _ = π₁ (π₀ (η false)) true _ (dir tt) tt
  goal false _ = dir (⊑[ S-pos 𝓤₀ 𝓤₀ ]-refl false)
```

We will sometimes how to talk about set being non-empty i.e. containing either
`true` or `false`. To do that, we define the following function:

```agda
_≠∅ : (U : ∣ 𝕊 ∣F) → 𝓤₀ ̇
𝔘 ≠∅ = [ true ∈ ⦅ 𝔘 ⦆ ] ⊎ [ false ∈ ⦅ 𝔘 ⦆ ]
```

<!--
```agda
open import UniversalProperty

open import Cover
```
-->

## Is this the correct Sierpiński frame?

Fix a frame `A` whose index types are small.

```agda
module _ (A : Frame 𝓤 𝓥 𝓤₀) where
```

We need to show that `𝕊` classifies the opens of `A`.

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

We now construct an isomorphism

```text
        to  :  (𝕊 ─f→ A)  ≃  A  :  from
```

### The forwards direction (easy)

```agda
  to : (𝕊 ─f→ A) → ∣ A ∣F
  to ((f , _) , _) = f ⁅true⁆
```

### The backwards direction

Let us first define an auxiliary function that we will need in the definition
of `from`, called `𝔨`, defined as:

```agda
  𝔨 : ∣ A ∣F → ∣ 𝕊 ∣F → Fam 𝓤₀ ∣ A ∣F
  𝔨 x 𝔘 = ⁅ x ∣ _ ∶ [ true ∈ ⦅ 𝔘 ⦆ ] ⁆ ∪f ⁅ 𝟏 ∣ _ ∶ [ false ∈ ⦅ 𝔘 ⦆ ] ⁆
```

We then define the underlying function of `from` that we call `from₀`:

```agda
  from₀ : ∣ A ∣F → ∣ 𝕊 ∣F → ∣ A ∣F
  from₀ x 𝔘 = ⋁ 𝔨 x 𝔘
```

To be able to define `from`, which is supposed to be a frame homomorphism for
every `x : ∣ A ∣`, we need to show that `from₀`:

1. is monotonic,
1. respects finite meets, and
1. respects joins,

Let us start by proving some lemmas that we will need to prove those.

First, we note that applying `from₀` to `⁅true⁆` gives back `x`:

```agda
  from-lemma₀ : (x : ∣ A ∣F) → from₀ x ⁅true⁆ ≡ x
  from-lemma₀ x = ⊑[ pos A ]-antisym _ _ nts₀ nts₁
    where
    nts₀ : [ from₀ x ⁅true⁆ ⊑[ pos A ] x ]
    nts₀ = ⋁[ A ]-least _ _ λ { y (inl i , eq) → ≡⇒⊑ (pos A) (sym eq)
                              ; y (inr i , eq) → ⊥-rec (true≠false (sym i))
                              }

    nts₁ : [ x ≤ from₀ x ⁅true⁆ ]
    nts₁ = ⋁[ A ]-upper _ _ (inl refl , refl)
```

`from₀` respects the top element:

```agda
  from₀-resp-⊤ : (x : ∣ A ∣F) → from₀ x ⊤[ 𝕊 ] ≡ ⊤[ A ]
  from₀-resp-⊤ x =
    ⊑[ pos A ]-antisym _ _ (⊤[ A ]-top _) (⋁[ A ]-upper _ _ (inr tt , refl))
```

It also respects the bottom element:

```agda
  from-resp-⊥ : (x : ∣ A ∣F) → from₀ x ⊥[ 𝕊 ] ≡ ⊥[ A ]
  from-resp-⊥ x =
    ⊑[ pos A ]-antisym _ _ (⋁[ A ]-least _ _ nts) (⊥[ A ]-bottom _)
    where
    nts : [ ∀[ z ε _ ] (z ≤ ⊥[ A ]) ]
    nts z (inl (dir p)        , eq) = ∥∥-rec (isProp[] (_ ≤ _)) (λ { (() , _) }) p
    nts z (inl (squash p q i) , eq) = isProp[] (_ ≤ _) (nts z (inl p , eq)) (nts z (inl q , eq)) i
    nts z (inr (dir p)        , eq) = ∥∥-rec (isProp[] (_ ≤ _)) (λ { (() , _) }) p
    nts z (inr (squash p q i) , eq) = isProp[] (_ ≤ _) (nts z (inr p , eq)) (nts z (inr q , eq)) i
```

If some `𝔘 : 𝕊` contains `false`, then it has to be the entire subset:

```agda
  false∈𝔘→𝔘-top : (𝔘 : ∣ 𝕊 ∣F) → [ false ∈ ⦅ 𝔘 ⦆ ] → ⊤[ 𝕊 ] ≡ 𝔘
  false∈𝔘→𝔘-top 𝔘 false∈𝔘 = 𝕊-equality ⊤[ 𝕊 ] 𝔘 (sym (goal 𝔘 false∈𝔘))
    where
    goal : (𝔘 : ∣ 𝕊 ∣F) → [ false ∈ ⦅ 𝔘 ⦆ ] → ⦅ 𝔘 ⦆ ≡ entire
    goal ((U , U-dc) , _) false∈𝔘 = ⊆-antisym nts₀ nts₁
      where
      nts₀ : [ U ⊆ entire ]
      nts₀ _ _ = tt

      nts₁ : [ entire ⊆ U ]
      nts₁ true  tt = U-dc false true false∈𝔘 tt
      nts₁ false tt = false∈𝔘
```

#### Monotonicity

Monotonicity of `from₀` is easy to show.

```agda
  from₀-mono : (x : ∣ A ∣F) → isMonotonic (pos 𝕊) (pos A) (from₀ x)
  from₀-mono x 𝔘 𝔙 𝔘⊆𝔙 = ⋁[ A ]-least _ _ nts
    where
    nts : _
    nts _ (inl i , eq) = ⋁[ A ]-upper _ _ (inl (𝔘⊆𝔙 true  i) , eq)
    nts _ (inr j , eq) = ⋁[ A ]-upper _ _ (inr (𝔘⊆𝔙 false j) , eq)
```

```agda
  from₀m : ∣ A ∣F → pos 𝕊 ─m→ pos A
  from₀m x = from₀ x , from₀-mono x
```

#### Continuity

We now prove that `from₀` is a frame homomorphism.

We have already shown that it respects the top element.

```agda
  resp-⊤ : (x : ∣ A ∣F) → from₀ x ⊤[ 𝕊 ] ≡ ⊤[ A ]
  resp-⊤ = from₀-resp-⊤
```

To show meet preservation, we make use of the fact that bi-cofinal families have
the same join.

```agda
  from₀-resp-∧ : (x : ∣ A ∣F) (𝔘 𝔙 : ∣ 𝕊 ∣F)
               → from₀ x (𝔘 ⊓[ 𝕊 ] 𝔙) ≡ from₀ x 𝔘 ∧ from₀ x 𝔙
  from₀-resp-∧ x 𝔘@((_ , 𝔘-dc) , _) 𝔙@((_ , 𝔙-dc) , _) =
    from₀ x (𝔘 ⊓[ 𝕊 ] 𝔙)                    ≡⟨ refl                  ⟩
    ⋁ 𝔨 x (𝔘 ⊓[ 𝕊 ] 𝔙)                      ≡⟨ nts                   ⟩
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

Preservation of joins is a bit more complicated. Let `W` be a family of
Sierpiński opens and let `x : A`. We use the uniqueness of
`⋁ ⁅ from₀ x 𝔘 ∣ 𝔘 ε W ⁆` by showing that `from₀ x (⋁[ 𝕊 ] W)` is the least
upper bound of `⁅ from₀ x 𝔘 ∣ 𝔘 ε W ⁆`. The fact that it is an upper bound
is given by `ub` and the fact that it is the least such is given in `least`.

```agda
  from₀-comm-⋁ : (x : ∣ A ∣F) (W : Fam 𝓤₀ ∣ 𝕊 ∣F)
               → from₀ x (⋁[ 𝕊 ] W) ≡ ⋁ ⁅ from₀ x 𝔘 ∣ 𝔘 ε W ⁆
  from₀-comm-⋁ x W = ⋁-unique A _ _ ub least
    where
    ub : [ ∀[ z ε ⁅ from₀ x 𝔘 ∣ 𝔘 ε W ⁆ ] (z ≤ from₀ x (⋁[ 𝕊 ] W)) ]
    ub z (i , eq) =
      subst (λ - → [ - ≤ _ ]) eq (from₀-mono x (W $ i) (⋁[ 𝕊 ] W) rem)
      where
      rem : [ (W $ i) ⊑[ pos 𝕊 ] (⋁[ 𝕊 ] W) ]
      rem _ x∈Wᵢ = dir ∣ i , x∈Wᵢ ∣

    least : (u : ∣ A ∣F)
          → (((z : ∣ A ∣F) → z ε ⁅ from₀ x 𝔘 ∣ 𝔘 ε W ⁆ → [ z ≤ u ]))
          → [ from₀ x (⋁[ 𝕊 ] W) ≤ u ]
    least u u-upper = ⋁[ A ]-least _ _ rem
      where
      open PosetReasoning (pos A)

      rem : (z : ∣ A ∣F) → z ε 𝔨 x (⋁[ 𝕊 ] W) → [ z ≤ u ]
      rem z (inl (dir p) , eq) =
        subst (λ - → [ - ≤ u ]) eq (∥∥-rec (isProp[] (_ ≤ _ )) goal p)
        where
        goal : _
        goal (j , true∈Wⱼ) =
          x                ⊑⟨ ≡⇒⊑ (pos A) (sym (from-lemma₀ x))    ⟩
          from₀ x ⁅true⁆   ⊑⟨ from₀-mono x ⁅true⁆ (W $ j) nts      ⟩
          from₀ x (W $ j)  ⊑⟨ u-upper (from₀ x (W $ j)) (j , refl) ⟩
          u                ■
          where
          nts : [ ⁅true⁆ ⊑[ pos 𝕊 ] (W $ j) ]
          nts true  _ = true∈Wⱼ
          nts false p = ⊥-rec (true≠false (sym p))
      rem z (inr (dir p) , eq) =
        subst (λ - → [ - ≤ u ]) eq (∥∥-rec (isProp[] (_ ≤ _)) goal p)
        where
        goal : _
        goal (j , false∈Wⱼ) = u-upper 𝟏 (j , nts)
          where
          Wⱼ=⊤ : W $ j ≡ ⊤[ 𝕊 ]
          Wⱼ=⊤ = sym (false∈𝔘→𝔘-top (W $ j) false∈Wⱼ)

          nts : from₀ x (W $ j) ≡ 𝟏
          nts = from₀ x (W $ j) ≡⟨ cong (from₀ x) Wⱼ=⊤ ⟩
                from₀ x ⊤[ 𝕊 ]  ≡⟨ resp-⊤ x            ⟩
                𝟏               ∎
      rem z (inl (squash p q i) , eq) =
        isProp[] (_ ≤ _) (rem z (inl p , eq)) (rem z (inl q , eq)) i
      rem z (inr (squash p q i) , eq) =
        isProp[] (_ ≤ _) (rem z (inr p , eq)) (rem z (inr q , eq)) i
```

The combination of these two proofs give us the fact that `from₀` is a frame
homomorphism (i.e. a continuous function):

```agda
  from₀-cont : (x : ∣ A ∣F) → isFrameHomomorphism 𝕊 A (from₀m x)
  from₀-cont x = resp-⊤ x , from₀-resp-∧ x  , from₀-comm-⋁ x
```

We are now ready to write down `from`:

```agda
  from : ∣ A ∣F → 𝕊 ─f→ A
  π₀ (π₀ (from x)) = from₀ x
  π₁ (π₀ (from x)) = from₀-mono x
  π₁ (from x)      = from₀-cont x
```

#### `to` cancels `from`

```agda
  to∘from=id : (x : ∣ A ∣F) → to (from x) ≡ x
  to∘from=id x = to (from x) ≡⟨ refl ⟩ from₀ x ⁅true⁆ ≡⟨ from-lemma₀ x ⟩ x ∎
```

#### `from` cancels `to`

To prove this result, we will make use of the following, rather important
lemma:

```agda
  useful-lemma : (((f , _) , _) : 𝕊 ─f→ A) (𝔘 : ∣ 𝕊 ∣F)
            → ⋁ ⁅ f (η u) ∣ u ∈ ⦅ 𝔘 ⦆ ⁆ ≡ f 𝔘
  useful-lemma 𝒻@((f , _) , _ , _ , f-resp-⋁) 𝔘 =
    ⋁ ⁅ f (η u) ∣ u ∈ ⦅ 𝔘 ⦆ ⁆      ≡⟨ sym (f-resp-⋁ (⁅ η u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆))   ⟩
    f (⋁[ 𝕊 ] ⁅ η u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆) ≡⟨ sym (cong f (main-lemma (S 𝓤₀ 𝓤₀) 𝔘))  ⟩
    f 𝔘                            ∎
```

We now prove that `from` cancels `to`:

```agda
  from∘to=id : (𝒻 : 𝕊 ─f→ A) → from (to 𝒻) ≡ 𝒻 
  from∘to=id 𝒻@((f , f-mono) , f-resp-⊤ , _) =
    forget-homo 𝕊 A (from (to 𝒻)) 𝒻 goal
    where
    goal : (𝔘 : ∣ 𝕊 ∣F) → from (to 𝒻) .π₀ .π₀ 𝔘 ≡ f 𝔘
    goal 𝔘 = sym (⋁-unique A _ _ ub least)
      where
      open PosetReasoning (pos A)

      ub : (x : ∣ A ∣F) → x ε 𝔨 (to 𝒻) 𝔘 → [ x ≤ (f 𝔘) ]
      ub x (inl i , eq) = subst (λ - → [ - ≤ f 𝔘 ]) eq nts
        where
        ⦅𝟏⦆ : [ f ⁅true⁆ ≤ f 𝔘 ]
        ⦅𝟏⦆ = f-mono _ _ (⊤-lemma 𝔘 i) 

        nts : [ (𝔨 (f ⁅true⁆) 𝔘 $ inl i) ≤ f 𝔘 ]
        nts = ⁅ f ⁅true⁆ ∣ _ ∶ [ true ∈ ⦅ 𝔘 ⦆ ] ⁆ $ i ⊑⟨ ≡⇒⊑ (pos A) refl ⟩
              f ⁅true⁆                                ⊑⟨ ⦅𝟏⦆              ⟩
              f 𝔘                                     ■
      ub x (inr j , eq) = subst (λ - → [ - ≤ f 𝔘 ]) eq (≡⇒⊑ (pos A) nts)
        where
        nts : 𝔨 (to 𝒻) 𝔘 $ inr j ≡ f 𝔘
        nts = 𝔨 (to 𝒻) 𝔘 $ inr j ≡⟨ refl                       ⟩
              ⊤[ A ]             ≡⟨ sym f-resp-⊤               ⟩
              f ⊤[ 𝕊 ]           ≡⟨ cong f (false∈𝔘→𝔘-top 𝔘 j) ⟩
              f 𝔘                ∎

      least : (u : ∣ A ∣F)
           → ((x : ∣ A ∣F) → x ε 𝔨 (to 𝒻) 𝔘 → [ x ≤ u ]) → [ f 𝔘 ≤ u ]
      least u p =
        subst (λ - → [ - ≤ u ]) (useful-lemma 𝒻 𝔘) (⋁[ A ]-least _ _ rem)
        where
        π : [ false ∈ ⦅ 𝔘 ⦆ ] → [ ⊤[ A ] ≤ u ]
        π q = p ⊤[ A ] (inr q , refl)

        ρ : [ true ∈ ⦅ 𝔘 ⦆ ] → [ f ⁅true⁆ ≤ u ]
        ρ q = p (f ⁅true⁆) (inl q , refl)

        rem : [ ∀[ z ε ⁅ f (η u) ∣ u ∈ ⦅ 𝔘 ⦆ ⁆ ] (z ≤ u) ]
        rem z ((true  , q) , eq) = subst (λ - → [ - ≤ u ]) eq nts
          where
          nts = f (η true) ⊑⟨ ≡⇒⊑ (pos A) (cong f (sym ⁅true⁆=η-true)) ⟩
                f ⁅true⁆   ⊑⟨ ρ q                                      ⟩
                u          ■
        rem z ((false , q) , eq) = subst (λ - → [ - ≤ u ]) eq nts
          where
          nts = f (η false) ⊑⟨ ≡⇒⊑ (pos A) (cong f (sym 𝟏=η-false)) ⟩
                f ⊤[ 𝕊 ]    ⊑⟨ ≡⇒⊑ (pos A) f-resp-⊤                 ⟩
                ⊤[ A ]      ⊑⟨ π q                                  ⟩
                u           ■
```

Finally, we write down the desired equivalence:

```agda
  𝕊-correct : (𝕊 ─f→ A) ≃ ∣ A ∣F
  𝕊-correct = isoToEquiv (iso to from to∘from=id from∘to=id)
```

```agda
main-proof        = S 𝓤₀ 𝓤₀ , 𝕊-correct
sierpiński-exists = main-proof
```
