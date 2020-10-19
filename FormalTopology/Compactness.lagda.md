```agda
{-# OPTIONS --cubical --safe #-}

module Compactness where

open import Basis             hiding (A; B)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Nat  using  (ℕ)
open import CoverFormsNucleus
open import UniversalProperty using (main-lemma; compr)
open import Poset
open import FormalTopology
open import Cover
open import Frame             renaming (pos to posf)
```

# Compactness for formal topologies

```agda
module _ (F : FormalTopology ℓ₀ ℓ₀) where

  open CoverFromFormalTopology F using (_◁_)

  private
    A = stage   F
    B = exp     F
    C = outcome F
    d = next    F

  down : List A → 𝒫 A
  down []       = λ _ → bot ℓ₀
  down (x ∷ xs) = λ y → ∥ [ y ⊑[ pos F ] x ] ⊎ [ y ∈ down xs ] ∥ , ∥∥-prop _

  down-dc : (as : List A) → [ isDownwardsClosed (pos F) (down as) ]
  down-dc [] _ _ ()
  down-dc (a ∷ as) x y x∈U y⊑x =
    ∥∥-rec (∥∥-prop _) NTS x∈U
    where
      NTS : [ rel (pos F) x a ] ⊎ [ x ∈ down as ] → ∥ [ rel (pos F) y a ] ⊎ [ y ∈ down as ] ∥
      NTS (inl p) = ∣ inl (⊑[ pos F ]-trans _ _ _ y⊑x p) ∣
      NTS (inr q) = ∣ inr (down-dc as x y q y⊑x) ∣

  isCompact : Type (ℓ-suc ℓ₀)
  isCompact = (a : A) (U : 𝒫 A) (U-dc : [ isDownwardsClosed (pos F) U ]) →
                a ◁ U → ∥ Σ[ as ∈ List A ] (a ◁ down as) × [ down as ⊆ U ] ∥
```

## Compactness for frames

Johnstone's definition of a compact frame is simply a frame whose top element is
finite. Therefore, let us start by writing down Johnstone's notion of
finiteness (Lemma 3.1.ii, pg. 63).

```agda
isFinite₂ : (F : Frame ℓ₀ ℓ₁ ℓ₂)
          → ∣ F ∣F → Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-suc ℓ₂))
isFinite₂ {ℓ₂ = ℓ₂} F x =
  (U : Fam ℓ₂ ∣ F ∣F) →
    [ isDirected (Frame.pos F) U ] →
      x ≡ ⋁[ F ] U → ∥ Σ[ i ∈ index U ] [ x ⊑[ Frame.pos F ] (U $ i) ] ∥
```

A frame is compact iff its top element is finite.

```agda
isCompactFrame : (F : Frame ℓ₀ ℓ₁ ℓ₂) → hProp (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-suc ℓ₂))
isCompactFrame F = isFinite₂ F ⊤[ F ] , isPropΠ3 (λ x y z → ∥∥-prop _)
```

## Correspondence between the two

```agda
_elem_ : {A : Type ℓ} → A → List A → Type ℓ
y elem []       = 𝟘 _
y elem (x ∷ xs) = (x ≡ y) ⊎ (y elem xs)

compact-ft→compact-frame : (ℱ : FormalTopology ℓ₀ ℓ₀)
                         → isCompact ℱ
                         → [ isCompactFrame (NucleusFrom.L ℱ) ]
compact-ft→compact-frame ℱ ℱ-compact 𝒰 𝒰-dir ⊤=⋁U = NTS
  where
    Lℱ = NucleusFrom.L ℱ

    open CoverFromFormalTopology ℱ using (_◁_; dir; branch; squash)
    open NucleusFrom ℱ             using (η; ⦅_⦆)

    W = λ z → ∥ Σ[ j ∈ index 𝒰 ] [ z ∈ ⦅ 𝒰 $ j ⦆ ] ∥
            , ∥∥-prop (Σ[ j ∈ index 𝒰 ] [ z ∈ ⦅ 𝒰 $ j ⦆ ])

    anything-in-U : (x : ∣ pos ℱ ∣ₚ) → x ◁ W
    anything-in-U x = subst (λ - → [ x ∈ ⦅ - ⦆ ]) ⊤=⋁U tt

    W-dc : [ isDownwardsClosed (pos ℱ) W ]
    W-dc x y x∈W y⊑x = ∥∥-rec (isProp[] (y ∈ W)) rem x∈W
      where
        rem : (Σ[ i ∈ (index 𝒰) ] ([ x ∈ ⦅ 𝒰 $ i ⦆ ])) → [ y ∈ W ]
        rem (i , x∈Uᵢ) = ∣ i , π₁ (π₀ (𝒰 $ i)) x y x∈Uᵢ y⊑x ∣

    NTS : ∥ Σ[ i ∈ index 𝒰 ] [ ⊤[ Lℱ ] ⊑[ posf Lℱ ] (𝒰 $ i) ] ∥
    NTS = ∥∥-rec (∥∥-prop _) rem (π₀ 𝒰-dir)
      where
        rem : index 𝒰 → ∥ Σ[ i ∈ index 𝒰 ] [ ⊤[ Lℱ ] ⊑[ posf Lℱ ] (𝒰 $ i) ] ∥
        rem i = ∣ i , rem₁ ∣
          where
            rem₁ : [ ⊤[ Lℱ ] ⊑[ posf Lℱ ] (𝒰 $ i) ]
            rem₁ x tt = ∥∥-rec (isProp[] (x ∈ ⦅ 𝒰 $ i ⦆)) rem₂ fin-cover
              where
                x◀W : x ◁ W
                x◀W = anything-in-U x

                fin-cover : ∥ Σ[ as ∈ List ∣ pos ℱ ∣ₚ ] (x ◁ down ℱ as) × [ down ℱ as ⊆ W ] ∥
                fin-cover = ℱ-compact x W W-dc x◀W

                fixing : (z : ∣ pos ℱ ∣ₚ) → z ◁ ⦅ 𝒰 $ i ⦆ → [ z ∈ ⦅ 𝒰 $ i ⦆ ]
                fixing z = subst (λ - → [ z ∈ π₀ - ]) (π₁ (𝒰 $ i))

                𝒰-upwards-dir : [ ∀[ i ∶ index 𝒰 ] ∀[ j ∶ index 𝒰 ] ∃[ k ∶ index 𝒰 ]
                                    rel₂ (posf Lℱ) (𝒰 $ i) (𝒰 $ j) (𝒰 $ k) ]
                𝒰-upwards-dir = π₁ 𝒰-dir

                rem₂ : Σ[ as ∈ List ∣ pos ℱ ∣ₚ ] (x ◁ down ℱ as × [ down ℱ as ⊆ W ])
                     → [ x ∈ ⦅ 𝒰 $ i ⦆ ]
                rem₂ (as , x◀down-as , down-as⊆W) = rem₃ as x◀down-as down-as⊆W
                  where
                    rem₃ : (as : List ∣ pos ℱ ∣ₚ)
                         → x ◁ down ℱ as → [ down ℱ as ⊆ W ] → [ x ∈ ⦅ 𝒰 $ i ⦆ ]
                    rem₃ = {!!}
```
