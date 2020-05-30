```
{-# OPTIONS --cubical --safe #-}

module CantorSpace where

open import Basis                     hiding (A; B)
open import Cubical.Data.Empty.Base   using (⊥; rec)
open import Cubical.Data.Bool.Base    using (true; false; _≟_) renaming (Bool to 𝔹)
open import Cubical.Data.List         using (List; _∷_; [])    renaming (_++_ to _^_)
open import Cover
open import Poset
open import FormalTopology
```

We open the `SnocList` module with the type `𝔹` of booleans.

```
open import SnocList 𝔹  _≟_  renaming (SnocList to ℂ; SnocList-set to ℂ-set)
```

The empty list and the snoc operator are called `[]` and `⌢` respectively. Concatenation
operation on snoc lists is called `_++_`. Note that concatenation on lists is therefore
renamed to `_^_` to prevent conflict.

## The Cantor poset

`xs` is less than `ys` if there is some `zs` such that `xs = ys ++ zs`.

```
_≤_ : ℂ → ℂ → hProp zero
xs ≤ ys = (Σ[ zs ∈ ℂ ] xs ≡ ys ++ zs) , prop
  where
    prop : isProp (Σ[ zs ∈ ℂ ] xs ≡ ys ++ zs)
    prop (_ , p) (_ , q) = ΣProp≡ (λ ws → ℂ-set xs (ys ++ ws)) (++-lemma p q)
```

As `_≤_` is a partial order, we package it up as a poset.

```
ℂ-pos : Poset zero zero
ℂ-pos = ℂ , _≤_ , ℂ-set , ≤-refl , ≤-trans , ≤-antisym
  where
    ≤-refl : (xs : ℂ) → [ xs ≤ xs ]
    ≤-refl xs = [] , refl

    ≤-trans : (xs ys zs : ℂ) → [ xs ≤ ys ] → [ ys ≤ zs ] → [ xs ≤ zs ]
    ≤-trans xs ys zs (as , p) (bs , q) =
      (bs ++ as) , NTS
      where
        NTS : xs ≡ zs ++ (bs ++ as)
        NTS = xs               ≡⟨ p                      ⟩
              ys ++ as         ≡⟨ cong (λ - → - ++ as) q ⟩
              (zs ++ bs) ++ as ≡⟨ sym (assoc zs bs as)   ⟩
              zs ++ (bs ++ as) ∎

    ≤-antisym : (xs ys : ℂ) → [ xs ≤ ys ] → [ ys ≤ xs ] → xs ≡ ys
    ≤-antisym xs ys ([]     , p) ([]      , q) = p
    ≤-antisym xs ys ([]     , p) (bs ⌢ x  , q) = p
    ≤-antisym xs ys (as ⌢ x , p) ([]      , q) = sym q
    ≤-antisym xs ys (as ⌢ a , p) (bs ⌢ b  , q) =
      rec (lemma3 NTS)
      where
        NTS : xs ≡ xs ++ ((bs ⌢ b) ++ (as ⌢ a))
        NTS = xs                           ≡⟨ p                                ⟩
              ys ++ (as ⌢ a)               ≡⟨ cong (λ - → - ++ as ⌢ a) q       ⟩
              (xs ++ (bs ⌢ b)) ++ (as ⌢ a) ≡⟨ sym (assoc xs (bs ⌢ b) (as ⌢ a)) ⟩
              xs ++ ((bs ⌢ b) ++ (as ⌢ a)) ∎
```

## The Cantor formal topology

We give the formal topology of the Cantor space as an
[interaction system](http://www.dcs.ed.ac.uk/home/pgh/interactive_systems.html).

1. Each inhabitant of `ℂ` is like a stage of information.

1. At each stage of information we can perform a trivial experiment: querying the next
   bit.
```
ℂ-exp = λ (_ : ℂ) → Unit zero
```

1. Outcome of the trivial experiment is the delivery of the new bit.
```
ℂ-out = λ (_ : Unit zero) → 𝔹
```

1. This takes us to a new stage information, obtained by snoc'ing in the new bit to the
   current stage of information.
```
ℂ-rev : {_ : ℂ} → 𝔹 → ℂ
ℂ-rev {xs} b = xs ⌢ b
```

These four components together form an interaction system that satiesfies the monotonicity
and simulation properties (given in `ℂ-mono` and `ℂ-sim`).

```
ℂ-IS : InteractionStr ℂ
ℂ-IS = ℂ-exp , ℂ-out , λ {xs} → ℂ-rev {xs}

ℂ-mono : hasMono ℂ-pos ℂ-IS
ℂ-mono _ _ c = [] ⌢ c , refl

ℂ-sim : hasSimulation ℂ-pos ℂ-IS
ℂ-sim xs ys xs≤ys@([] , p) tt = tt , NTS
  where
    NTS : (b₁ : 𝔹) → Σ[ b₀ ∈ 𝔹 ] [ (xs ⌢ b₁) ≤ (ys ⌢ b₀) ]
    NTS b₁ = b₁ , subst (λ - → [ (xs ⌢ b₁) ≤ (- ⌢ b₁) ]) p (⊑[ ℂ-pos ]-refl _)
ℂ-sim xs ys xs≤ys@(zs ⌢ z , p) tt = tt , NTS
  where
    NTS : (c₀ : 𝔹) → Σ[ c ∈ 𝔹 ] [ (xs ⌢ c₀) ≤ (ys ⌢ c) ]
    NTS c₀ =
      head (zs ⌢ z) tt , subst (λ - → [ (- ⌢ c₀) ≤ _ ]) (sym p) NTS′
      where
        φ    = cong (λ - → ys ++ (- ⌢ c₀)) (sym (hd-tl-lemma (zs ⌢ z) tt))
        ψ    = cong (λ - → - ⌢ c₀) (sym (snoc-lemma ys _ _))
        rem  = (ys ++ zs) ⌢ z ⌢ c₀                                          ≡⟨ φ ⟩
                (ys ++ (([] ⌢ head (zs ⌢ z) tt) ++ (tail (zs ⌢ z) tt))) ⌢ c₀ ≡⟨ ψ ⟩
                ((ys ⌢ head (zs ⌢ z) tt) ++ tail (zs ⌢ z) tt) ⌢ c₀ ∎
        NTS′ : [ ((ys ++ zs) ⌢ z ⌢ c₀) ≤ (ys ⌢ head (zs ⌢ z) tt) ]
        NTS′ = ((tail (zs ⌢ z) tt) ⌢ c₀) , rem
```

We finally package up all this as a formal topology

```
cantor : FormalTopology zero zero
cantor = ℂ-pos , ℂ-IS , ℂ-mono , ℂ-sim
```

from which we get a covering relation

```
open CoverFromFormalTopology cantor renaming (_◀_ to _<ℂ|_)

_ : ℂ → (ℂ → hProp zero) → Type zero
_ = _<ℂ|_
```

## Statement of compactness

The statement of compactness then is as follows.

```
module _ (F : FormalTopology ℓ₀ ℓ₀) where

  open CoverFromFormalTopology F using (_◀_)

  private
    A = stage   F
    B = exp     F
    C = outcome F
    d = next    F

  down : List A → 𝒫 A
  down []       = λ _ → bot ℓ₀
  down (x ∷ xs) = λ y → ∥ [ y ⊑[ pos F ] x ] ⊎ [ down xs y ] ∥ , ∥∥-prop _

  isCompact : Type (suc ℓ₀)
  isCompact = (a : A) (U : 𝒫 A) (U-dc : [ isDownwardsClosed (pos F) U ]) →
                a ◀ U → ∥ Σ[ as ∈ List A ] (a ◀ down as) × [ down as ⊆ U ] ∥
```

## The Cantor formal topology is compact

We now want to view a list of `ℂ`s as a _finite cover_. We associate with some
`xss : List ℂ` a subset, being covered by which corresponds to being covered by this list.

```
ℂ-down : List ℂ → 𝒫 ℂ
ℂ-down = down cantor

syntax ℂ-down xss xs = xs ↓ xss
```

This subset is downwards-closed.

```
↓-dc : (xss : List ℂ) → [ isDownwardsClosed ℂ-pos (λ - → - ↓ xss) ]
↓-dc (xs ∷ xss) ys zs ys◀xs∷xss zs≤ys =
  ∥∥-rec (is-true-prop (zs ↓ (xs ∷ xss))) NTS ys◀xs∷xss
  where
    open PosetReasoning ℂ-pos using (_⊑⟨_⟩_; _■)

    NTS : [ ys ≤ xs ] ⊎ [ ys ↓ xss ] → [ zs ↓ (xs ∷ xss) ]
    NTS (inl ys≤xs)  = ∣ inl (zs ⊑⟨ zs≤ys ⟩ ys ⊑⟨ ys≤xs ⟩ xs ■) ∣
    NTS (inr ys◀xss) = ∣ inr (↓-dc xss ys zs ys◀xss zs≤ys)    ∣
```

We claim that the Cantor space is compact.

```
compact : isCompact cantor
```

### Two little lemmas

```
U⊆V⇒◀U⊆◀V : (xs : ℂ) (U : 𝒫 ℂ) (V : 𝒫 ℂ) → [ U ⊆ V ] → xs <ℂ| U → xs <ℂ| V
U⊆V⇒◀U⊆◀V xs U V U⊆V = lem₄ U V NTS xs
  where
    NTS : (u : ℂ) → [ u ∈ U ] → u <ℂ| V
    NTS u u∈U = dir (U⊆V u u∈U)

↓-++-left : (xss yss : List ℂ) → [ (λ - → - ↓ xss) ⊆ (λ - → - ↓ (xss ^ yss)) ]
↓-++-left []         yss _ ()
↓-++-left (xs ∷ xss) yss ys ys∈down-xs-xss =
  ∥∥-rec (is-true-prop (ys ↓ ((xs ∷ xss) ^ yss))) NTS ys∈down-xs-xss
  where
    NTS : [ ys ≤ xs ] ⊎ [ ys ↓ xss ] → [ ys ↓ (xs ∷ xss ^ yss) ]
    NTS (inl ys≤xs)       = ∣ inl ys≤xs ∣
    NTS (inr ys∈down-xss) = ∣ inr (↓-++-left xss yss ys ys∈down-xss) ∣

↓-++-right : (xss yss : List ℂ) → [ (λ - → - ↓ yss) ⊆ (λ - → - ↓ (xss ^ yss)) ]
↓-++-right xss        []         _  ()
↓-++-right []         (ys ∷ yss) zs zs∈◀ys∷yss = zs∈◀ys∷yss
↓-++-right (xs ∷ xss) (ys ∷ yss) zs zs∈◀ys∷yss =
  ∥∥-rec (is-true-prop (zs ↓ (xs ∷ xss ^ ys ∷ yss))) NTS zs∈◀ys∷yss
  where
    NTS : [ zs ≤ ys ] ⊎ [ zs ↓ yss ] → [ zs ↓ (xs ∷ xss ^ ys ∷ yss) ]
    NTS (inl zs≤ys)  = let IH = ↓-++-right xss _ _ ∣ inl (⊑[ ℂ-pos ]-refl ys) ∣
                        in ∣ inr (↓-dc (xss ^ ys ∷ yss) ys zs IH zs≤ys) ∣
    NTS (inr zs◀yss) = ∣ inr (↓-++-right xss _ zs ∣ inr zs◀yss ∣) ∣

◀^-decide : (xs : ℂ) (yss zss : List ℂ)
          → [ xs ↓ (yss ^ zss) ]
          → ∥ [ xs ↓ yss ] ⊎ [ xs ↓ zss ] ∥
◀^-decide xs []         zss k = ∣ inr k ∣
◀^-decide xs (ys ∷ yss) zss k = ∥∥-rec (∥∥-prop _) NTS₀ k
  where
    NTS₀ : [ xs ≤ ys ] ⊎ [ xs ↓ (yss ^ zss) ] → ∥ [ xs ↓ (ys ∷ yss) ] ⊎ [ xs ↓ zss ] ∥
    NTS₀ (inl xs≤ys) = ∣ inl ∣ inl xs≤ys ∣ ∣
    NTS₀ (inr xs◀yss^zss) = ∥∥-rec (∥∥-prop _) NTS₁ (◀^-decide xs yss zss xs◀yss^zss)
      where
        NTS₁ : [ xs ↓ yss ] ⊎ [ xs ↓ zss ] → ∥ [ xs ↓ (ys ∷ yss) ] ⊎ [ xs ↓ zss ] ∥
        NTS₁ (inl xs◀yss) = ∣ inl ∣ inr xs◀yss ∣ ∣
        NTS₁ (inr xs◀zss) = ∣ inr xs◀zss          ∣
```

### The proof

The proof is by induction on the proof of `xs ◀ U`.

```
compact xs U U-dc (dir xs∈U) = ∣ xs ∷ [] , NTS₀ , NTS₁ ∣
  where
    NTS₀ : xs <ℂ| (λ - → - ↓ (xs ∷ []))
    NTS₀ = dir ∣ inl (⊑[ ℂ-pos ]-refl xs) ∣

    NTS₁ : [ (λ - → - ↓ (xs ∷ [])) ⊆ U ]
    NTS₁ ys ∣ys◀[xs]∣ = ∥∥-rec (is-true-prop (ys ∈ U)) NTS₁′ ∣ys◀[xs]∣
      where
        NTS₁′ : [ ys ≤ xs ] ⊎ [ ys ↓ [] ] → [ U ys ]
        NTS₁′ (inl ys≤xs) = U-dc xs ys xs∈U ys≤xs

compact xs U U-dc (branch tt f) =
  let
    IH₀ : ∥ Σ[ yss₀ ∈ List ℂ ]
              ((xs ⌢ true) <ℂ| (λ - → - ↓ yss₀)) × [ ℂ-down yss₀ ⊆ U ] ∥
    IH₀ = compact (xs ⌢ true) U U-dc (f true)
    IH₁ : ∥ Σ[ yss ∈ List ℂ ]
              ((xs ⌢ false) <ℂ| (λ - → - ↓ yss) × [ ℂ-down yss ⊆ U ]) ∥
    IH₁ = compact (xs ⌢ false) U U-dc (f false)
  in
    ∥∥-rec (∥∥-prop _) (λ φ → ∥∥-rec (∥∥-prop _) (λ ψ → ∣ NTS φ ψ ∣) IH₁) IH₀
  where
    NTS : Σ[ yss₀ ∈ _ ] ((xs ⌢  true) <ℂ| λ - → - ↓ yss₀) × [ ℂ-down yss₀ ⊆ U ]
        → Σ[ yss₁ ∈ _ ] ((xs ⌢ false) <ℂ| λ - → - ↓ yss₁) × [ ℂ-down yss₁ ⊆ U ]
        → Σ[ yss  ∈ _ ] (xs <ℂ| λ - → - ↓ yss) × [ ℂ-down yss ⊆ U ]
    NTS (yss , φ , p) (zss , ψ , q) = yss ^ zss , branch tt g , NTS′
      where
        g : (c : 𝔹) → (xs ⌢ c) <ℂ| (λ - → ℂ-down (yss ^ zss) -)
        g false = U⊆V⇒◀U⊆◀V _ (ℂ-down zss) (ℂ-down (yss ^ zss)) (↓-++-right yss zss) ψ
        g true  = U⊆V⇒◀U⊆◀V _ (ℂ-down yss) (ℂ-down (yss ^ zss)) (↓-++-left  yss zss) φ

        NTS′ : [ (λ - → - ↓ (yss ^ zss)) ⊆ U ]
        NTS′ ys ys◀yss₀^yss₁ =
          ∥∥-rec (is-true-prop (ys ∈ U)) NTS₂ (◀^-decide _ yss _ ys◀yss₀^yss₁)
          where
            NTS₂ : [ ys ↓ yss ] ⊎ [ ys ↓ zss ] → [ ys ∈ U ]
            NTS₂ (inl ys◀yss₀) = p ys ys◀yss₀
            NTS₂ (inr ys◀yss₁) = q ys ys◀yss₁

compact xs U U-dc (squash xs◀U₀ xs◀U₁ i) =
  squash (compact xs U U-dc xs◀U₀) (compact xs U U-dc xs◀U₁) i
```
