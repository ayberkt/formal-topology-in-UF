```
{-# OPTIONS --cubical --safe #-}

module CoverFormsNucleus where

open import Basis          hiding (A) renaming (squash to squash′)
open import Poset
open import Frame
open import Cover
open import Nucleus           using    (isNuclear; Nucleus; 𝔣𝔦𝔵; idem)
open import Cubical.Data.Bool using    (Bool; true; false)
open import FormalTopology    renaming (pos to pos′)
```

We use a module that takes some formal topology `F` as a parameter to reduce
parameter-passing.

```
module NucleusFrom (ℱ : FormalTopology ℓ₀ ℓ₀) where
```

We refer to the underlying poset of `F` as `P` and the frame of downwards-closed subsets
of `P` as `P↓`.

```
  private
    P       = pos′ ℱ
    P↓      = DCFrame P
    _⊑_     = λ (x y : stage ℱ) → x ⊑[ P ] y

  open CoverFromFormalTopology ℱ public
```

Now, we define the *covering nucleus* which we denote by `𝕛`. At its heart, this is
nothing but the map `U ↦ - ◁ U`.

```
  𝕛 : ∣ P↓ ∣F → ∣ P↓ ∣F
  𝕛 (U , U-down) = (λ - → U ▷ -) , U▷-dc
    where
      -- This is not propositional unless we force it to be using the HIT definition!
      _▷_ : 𝒫 ∣ P ∣ₚ → 𝒫 ∣ P ∣ₚ
      U ▷ a = a ◁ U , squash

      U▷-dc : [ isDownwardsClosed P (λ - → (- ◁ U) , squash) ]
      U▷-dc a a₀ aεU₁ a₀⊑a = ◁-lem₁ U-down a₀⊑a aεU₁

  𝕛-nuclear : isNuclear P↓ 𝕛
  𝕛-nuclear = N₀ , N₁ , N₂
    where
      -- We reason by antisymmetry and prove in (d) 𝕛 (a₀ ⊓ a₁) ⊑ (𝕛 a₀) ⊓ (𝕛 a₁) and
      -- in (u) (𝕛 a₀) ⊓ (𝕛 a₁) ⊑ 𝕛 (a₀ ⊓ a₁).
      N₀ : (𝔘 𝔙 : ∣ P↓ ∣F) → 𝕛 (𝔘 ⊓[ P↓ ] 𝔙) ≡ (𝕛 𝔘) ⊓[ P↓ ] (𝕛 𝔙)
      N₀ 𝕌@(U , U-down) 𝕍@(V , V-down) =
        ⊑[ pos P↓ ]-antisym (𝕛 (𝕌 ⊓[ P↓ ] 𝕍)) (𝕛 𝕌 ⊓[ P↓ ] 𝕛 𝕍) down up
        where
          down : [ (𝕛 (𝕌 ⊓[ P↓ ] 𝕍)) ⊑[ pos P↓ ] (𝕛 𝕌 ⊓[ P↓ ] 𝕛 𝕍) ]
          down a (dir (a∈U , a∈V)) = dir a∈U , dir a∈V
          down a (branch b f)      = branch b (π₀ ∘ IH) , branch b (π₁ ∘ IH)
            where
              IH : (c : outcome ℱ b) → [ π₀ (𝕛 𝕌 ⊓[ P↓ ] 𝕛 𝕍) (next ℱ c) ]
              IH c = down (next ℱ c) (f c)
          down a (squash p q i) = squash (π₀ IH₀) (π₀ IH₁) i , squash (π₁ IH₀) (π₁ IH₁) i
            where
              _ : a ◁ π₀ (glb-of P↓ (U , U-down) (V , V-down))
              _ = p
              IH₀ = down a p
              IH₁ = down a q

          up : [ (𝕛 𝕌 ⊓[ P↓ ] 𝕛 𝕍) ⊑[ pos P↓ ] 𝕛 (𝕌 ⊓[ P↓ ] 𝕍) ]
          up a (a◁U , a◁V) = ◁-lem₃ V U V-down U-down (⊑[ P ]-refl a) a◁V a◁U

      N₁ : (𝔘 : ∣ P↓ ∣F) → [ 𝔘 ⊑[ pos P↓ ] (𝕛 𝔘) ]
      N₁ _ a₀ a∈U = dir a∈U

      N₂ : (𝔘 : ∣ P↓ ∣F) → [ π₀ (𝕛 (𝕛 𝔘)) ⊆ π₀ (𝕛 𝔘) ]
      N₂ 𝔘@(U , _) = ◁-lem₄ (π₀ (𝕛 𝔘)) U (λ _ q → q)
```

We denote by `L` the frame of fixed points for `𝕛`.

```
  L : Frame (suc ℓ₀) ℓ₀ ℓ₀
  L = 𝔣𝔦𝔵 P↓ (𝕛 , 𝕛-nuclear)
```

The following is a just a piece of convenient notation for projecting out the underlying
set of a downwards-closed subset equipped with the information that it is a fixed point
for `𝕛`.

```
  ⦅_⦆ : ∣ L ∣F → 𝒫 ∣ P ∣ₚ
  ⦅ ((U , _) , _) ⦆ = U
```

Given some `x` in `F`, we define a map taking `x` to its *downwards-closure*.

```
  ↓-clos : stage ℱ → ∣ P↓ ∣F
  ↓-clos x = x↓ , down-DC
    where
      x↓ = λ y → y ⊑[ P ] x
      down-DC : [ isDownwardsClosed P x↓ ]
      down-DC z y z⊑x y⊑z = ⊑[ P ]-trans y z x y⊑z z⊑x

  x◁x↓ : (x : stage ℱ) → x ◁ (λ - → - ⊑[ P ] x)
  x◁x↓ x = dir (⊑[ P ]-refl x)
```

By composing this with the covering nucleus, we define a map `e` from `F` to `P↓`.

```
  e : ∣ P ∣ₚ → ∣ P↓ ∣F
  e z = (λ a → (a ◁ (π₀ (↓-clos z))) , squash) , NTS
    where
      NTS : [ isDownwardsClosed P (λ a → (a ◁ (λ - → - ⊑[ P ] z)) , squash) ]
      NTS _ _ x y = ◁-lem₁ (λ _ _ x⊑y y⊑z → ⊑[ P ]-trans _ _ z y⊑z x⊑y) y x
```

We can further refine the codomain of `e` to `L`. In other words, we can prove that `j (e
x) = e x` for every `x`. We call the version `e` with the refined codomain `η`.

```
  fixing : (x : ∣ P ∣ₚ) → 𝕛 (e x) ≡ e x
  fixing x = ⊑[ pos P↓ ]-antisym (𝕛 (e x)) (e x) down up
    where
      down : ∀ y → [ π₀ (𝕛 (e x)) y ] → [ π₀ (e x) y ]
      down = ◁-lem₄ (π₀ (e x)) (π₀ (↓-clos x)) (λ _ q → q)

      up : [ e x ⊑[ pos P↓ ] 𝕛 (e x) ]
      up = π₀ (π₁ 𝕛-nuclear) (e x)

  η : stage ℱ → ∣ L ∣F
  η x = (e x) , (fixing x)
```

Furthermore, `η` is a monotonic map.

```
  ηm : P ─m→ pos L
  ηm = η , η-mono
    where
      η-mono : isMonotonic P (pos L) η
      η-mono x y x⊑y = ◁-lem₄ (π₀ (↓-clos x)) (π₀ (↓-clos y)) NTS
        where
          NTS : (u : ∣ P ∣ₚ) → [ u ∈ π₀ (↓-clos x) ] → u ◁ π₀ (↓-clos y)
          NTS _ p = ◁-lem₁ (π₁ (↓-clos y)) p (dir x⊑y)
```
