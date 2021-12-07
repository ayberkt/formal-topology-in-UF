---
title: Regular Locales
---

```agda
{-# OPTIONS --cubical --safe #-}

module Regular where

open import Cubical.Core.Everything hiding (_∧_; _∨_)
open import Basis hiding (_∨_)
open import Poset
open import Nucleus
open import Frame
open import CoverFormsNucleus

```

## Definition

We define the well-inside relation exactly as in Johstone. This is a pointless
characterisation of the relation that *U* ⋜ *V* := Clos(*U*) ⊆ *V*. Notice why this is
called "well-inside": if Clos(*U*) ⊆ *V* it means *U* is inside *V* in such way that it
doesn't touch its boundary.

```agda
well-inside : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → ∣ F ∣F → Type ℓ₀
well-inside F x y =
  Σ[ z ∈ ∣ F ∣F ] (x ⊓[ F ] z ≡ ⊥[ F ]) × (y ∨[ F ] z ≡ ⊤[ F ])

syntax well-inside F x y = x ⋜[ F ] y
```

We denote by ⇊ *x* the set of everything well-inside *x*.

```agda
⇊ : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → Fam ℓ₀ ∣ F ∣F
⇊ F x = (Σ[ y ∈ ∣ F ∣F ] y ⋜[ F ] x) , π₀
```

A locale *L* is then called **regular** iff every element in it is the join of all
elements well-inside it.

```agda
isRegular : (F : Frame ℓ₀ ℓ₁ ℓ₂) → hProp (ℓ-max ℓ₀ ℓ₁)
isRegular F = ∀[ x ∶ ∣ F ∣F ] isSup (pos F) (⇊ F x) x
```

## Some properties

```agda
complements : (F : Frame 𝓤 𝓥 𝓦) → ∣ F ∣F → ∣ F ∣F → Type 𝓤
complements F x y = (x ⊓[ F ] y ≡ ⊥[ F ]) × (x ∨[ F ] y ≡ ⊤[ F ])
```

```agda
-- In other words, x is clopen.
hasComplement : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → Type ℓ₀
hasComplement F x =
  Σ[ y ∈ ∣ F ∣F ] (x ⊓[ F ] y ≡ ⊥[ F ]) × (x ∨[ F ] y ≡ ⊤[ F ])

hasComplement′ : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) ℓ₂)
hasComplement′ {ℓ₂ = ℓ₂} F x =
  Σ[ y ∈ ∣ F ∣F ] [ isInf (pos F) ⊥[ F ] x y ] × [ isSup {ℓ₂ = ℓ₂} (pos F) ⁅ x , y ⁆ ⊤[ F ] ]

fclopens : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → Fam ℓ₀ ∣ F ∣F
fclopens F x = (Σ[ x ∈ ∣ F ∣F ] hasComplement F x) , π₀

complements-unique : (F : Frame 𝓤 𝓥 𝓦)
                   → (x y₀ y₁ : ∣ F ∣F)
                   → complements F x y₀ → complements F x y₁ → y₀ ≡ y₁
complements-unique F x y y′ (p , q) (p′ , q′) = nts
  where
  abstract
    nts : y ≡ y′
    nts =
      y                                  ≡⟨ sym (x∧⊤=x F y)                                         ⟩
      y ⊓[ F ] ⊤[ F ]                    ≡⟨ cong (λ - → y ⊓[ F ] -) (sym q′)                        ⟩
      y ⊓[ F ] (x ∨[ F ] y′)             ≡⟨ bin-dist F y x y′                                       ⟩
      (y ⊓[ F ] x) ∨[ F ] (y ⊓[ F ] y′)  ≡⟨ cong (λ - → - ∨[ F ] (y ⊓[ F ] y′)) (comm F y x)        ⟩
      (x ⊓[ F ] y) ∨[ F ] (y ⊓[ F ] y′)  ≡⟨ cong (λ - → - ∨[ F ] (y ⊓[ F ] y′)) p                   ⟩
      ⊥[ F ] ∨[ F ] (y ⊓[ F ] y′)        ≡⟨ cong (λ - → - ∨[ F ] (y ⊓[ F ] y′)) (sym p′)            ⟩
      (x ⊓[ F ] y′) ∨[ F ] (y ⊓[ F ] y′) ≡⟨ cong (λ - → - ∨[ F ] (y ⊓[ F ] y′)) (comm F x y′)       ⟩
      (y′ ⊓[ F ] x) ∨[ F ] (y ⊓[ F ] y′) ≡⟨ sym (cong (λ - → (y′ ⊓[ F ] x) ∨[ F ] -) (comm F y′ y)) ⟩
      (y′ ⊓[ F ] x) ∨[ F ] (y′ ⊓[ F ] y) ≡⟨ sym (bin-dist F y′ x y)                                 ⟩
      y′ ⊓[ F ] (x ∨[ F ] y)             ≡⟨ comm F y′ (x ∨[ F ] y)                                  ⟩
      (x ∨[ F ] y) ⊓[ F ] y′             ≡⟨ cong (λ - → - ⊓[ F ] y′) q                              ⟩
      ⊤[ F ] ⊓[ F ] y′                   ≡⟨ comm F ⊤[ F ] y′                                        ⟩
      y′ ⊓[ F ] ⊤[ F ]                   ≡⟨ x∧⊤=x F y′                                              ⟩
      y′                                 ∎

hasComplement-prop : (F : Frame 𝓤 𝓥 𝓦) → (x : ∣ F ∣F) → isProp (hasComplement F x)
hasComplement-prop F x (y , p , q) (y′ , p′ , q′) =
  Σ≡Prop
    (λ w → isPropΣ (F-set _ _) λ _ → F-set _ _)
    (complements-unique F x y y′ (p , q) (p′ , q′))
  where
  F-set : isSet ∣ F ∣F
  F-set = carrier-is-set (pos F)

module SomePropertiesOf⋜ (F : Frame ℓ₀ ℓ₁ ℓ₂) where

  private
    _⊑_ = λ (x y : ∣ F ∣F) → x ⊑[ pos F ] y

  ⋜-comp : (x : ∣ F ∣F) → (x ⋜[ F ] x) ↔ hasComplement F x
  ⋜-comp x = (λ x → x) , (λ x → x)

  a⋜b→a⊑b : (x y : ∣ F ∣F) → x ⋜[ F ] y → [ x ⊑[ pos F ] y ]
  a⋜b→a⊑b x y (z , p , q) = x=x∧y⇒x⊑y F NTS
    where
      open PosetReasoning (pos F)

      NTS : x ≡ x ⊓[ F ] y
      NTS = x                                ≡⟨ sym (x∧⊤=x F x)                 ⟩
            x ⊓[ F ] ⊤[ F ]                  ≡⟨ cong (λ - → x ⊓[ F ] -) (sym q) ⟩
            x ⊓[ F ] (y ∨[ F ] z)            ≡⟨ bin-dist F x y z                ⟩
            (x ⊓[ F ] y) ∨[ F ] (x ⊓[ F ] z) ≡⟨ cong (λ - → _ ∨[ F ] -) p       ⟩
            (x ⊓[ F ] y) ∨[ F ] ⊥[ F ]       ≡⟨ ∨-comm F (x ⊓[ F ] y) ⊥[ F ]    ⟩
            ⊥[ F ] ∨[ F ] (x ⊓[ F ] y)       ≡⟨ x∨⊥=x F (x ⊓[ F ] y)            ⟩
            x ⊓[ F ] y                       ∎

  a⋜c≤d : {x y z : ∣ F ∣F} → x ⋜[ F ] y → [ y ⊑[ pos F ] z ] → x ⋜[ F ] z
  a⋜c≤d {x} {y} {z} (c , p , q) y⊑z =
    c , (p , ⊑[ pos F ]-antisym _ _ (⊤[ F ]-top _) ⊤⊑z∨c)
    where
      open PosetReasoning (pos F)

      y⊑z∨c : [ y ⊑[ pos F ] (z ∨[ F ] c) ]
      y⊑z∨c = y ⊑⟨ y⊑z ⟩ z ⊑⟨ ⊔[ F ]-upper₀ z c ⟩ z ∨[ F ] c ■

      ⊤⊑z∨c : [ ⊤[ F ] ⊑[ pos F ] (z ∨[ F ] c) ]
      ⊤⊑z∨c =
        subst (λ - → [ - ⊑[ pos F ] _ ]) q (⊔[ F ]-least _ _ _ y⊑z∨c (⊔[ F ]-upper₁ z c))
```

## Alternative characterisation

Another way of characterising regularity is this: a locale *L* is called regular iff each
of its elements can be written as the join of a _clopen_ family. Before looking at this
though, let us first discuss how we can express clopen-ness.

We say that some open *x* ∈ *L* is clopen iff it has a complement. This can be motivated
by the fact that a set is clopen iff its boundary is empty i.e. it satisfies LEM. Now
we can write down the alternative characterisation we mentioned.

```agda
hasClopenBasis : (F : Frame ℓ₀ ℓ₁ ℓ₂) → Type (ℓ-max ℓ₀ (ℓ-suc ℓ₂))
hasClopenBasis {ℓ₂ = ℓ₂} F =
  (x : ∣ F ∣F) →
    Σ[ U ∈ Fam ℓ₂ ∣ F ∣F ] ((y : ∣ F ∣F) → y ε U → hasComplement F y) × (x ≡ ⋁[ F ] U)
```

```agda
regularity-lemma : (F : Frame ℓ₀ ℓ₁ ℓ₂) → hasClopenBasis F → [ isRegular F ]
regularity-lemma F p x = upper , subst goal (sym x=⋁𝔘) ψ
  where
    open PosetReasoning (pos F)
    open SomePropertiesOf⋜ F

    goal = λ - → (y : ∣ F ∣F) → [ ∀[ k ε ⇊ F x ] (k ⊑[ pos F ] y) ] → [ - ⊑[ pos F ] y ]

    𝔘 = π₀ (p x)

    x=⋁𝔘 : x ≡ ⋁[ F ] 𝔘
    x=⋁𝔘 = π₁ (π₁ (p x))

    has-comp : (y : ∣ F ∣F) → y ε 𝔘 → hasComplement F y
    has-comp = π₀ (π₁ (p x))

    upper : [ ∀[ y ε (⇊ F x) ] (y ⊑[ pos F ] x) ]
    upper y ((_ , wi) , eq) = subst (λ - → [ - ⊑[ pos F ] x ]) eq (a⋜b→a⊑b _ x wi)

    ψ : (y : ∣ F ∣F) → [ ∀[ k ε ⇊ F x ] (k ⊑[ pos F ] y) ] → [ (⋁[ F ] 𝔘) ⊑[ pos F ] y ]
    ψ y q = ⋁[ F ]-least 𝔘 y NTS
      where
        NTS : [ ∀[ k ε 𝔘 ] (k ⊑[ pos F ] y) ]
        NTS k (i , eq) = q k kε⇊Fx
          where
            𝔘ᵢ-has-comp : hasComplement F (𝔘 $ i)
            𝔘ᵢ-has-comp = has-comp (𝔘 $ i) (i , refl)

            𝔘ᵢ⋜⋁𝔘 : (𝔘 $ i) ⋜[ F ] (⋁[ F ] 𝔘)
            𝔘ᵢ⋜⋁𝔘 = a⋜c≤d 𝔘ᵢ-has-comp (⋁[ F ]-upper 𝔘 (𝔘 $ i) (i , refl))

            kε⇊Fx : k ε ⇊ F x
            kε⇊Fx = (𝔘 $ i , subst (λ - → _ ⋜[ F ] -) (sym x=⋁𝔘) 𝔘ᵢ⋜⋁𝔘) , eq
```

```agda
∧-complement : (F : Frame ℓ₀ ℓ₁ ℓ₂)
             → (x y x′ y′ : ∣ F ∣F)
             → complements F x x′
             → complements F y y′
             → complements F (x ⊓[ F ] y) (x′ ∨[ F ] y′)
∧-complement F x y x′ y′ (x∧x=⊥ , x∨x′=⊤) (y∧y′=⊥ , y∨y′=⊤) = G𝟏 , G𝟐
  where
  _∧_ : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
  x ∧ y = x ⊓[ F ] y

  _∨_ : ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
  x ∨ y = x ∨[ F ] y

  G𝟏 : (x ∧ y) ∧ (x′ ∨ y′) ≡ ⊥[ F ]
  G𝟏 = (x ∧ y) ∧ (x′ ∨ y′)              ≡⟨ ⦅𝟏⦆ ⟩
       ((x ∧ y) ∧ x′) ∨ ((x ∧ y) ∧ y′)  ≡⟨ ⦅𝟐⦆ ⟩
       ((y ∧ x) ∧ x′) ∨ ((x ∧ y) ∧ y′)  ≡⟨ ⦅𝟑⦆ ⟩
       (y ∧ (x ∧ x′)) ∨ ((x ∧ y) ∧ y′)  ≡⟨ ⦅𝟒⦆ ⟩
       (y ∧ ⊥[ F ]) ∨ ((x ∧ y) ∧ y′)    ≡⟨ ⦅𝟓⦆ ⟩
       ⊥[ F ] ∨ ((x ∧ y) ∧ y′)          ≡⟨ ⦅𝟔⦆ ⟩
       (x ∧ y) ∧ y′                     ≡⟨ ⦅𝟕⦆ ⟩
       x ∧ (y ∧ y′)                     ≡⟨ ⦅𝟖⦆ ⟩
       x ∧ ⊥[ F ]                       ≡⟨ ⦅𝟗⦆ ⟩
       ⊥[ F ]                           ∎
    where
    ⦅𝟏⦆ = bin-dist F (x ∧ y) x′ y′
    ⦅𝟐⦆ = cong (λ - → (- ∧ x′) ∨ ((x ∧ y) ∧ y′)) (comm F x y)
    ⦅𝟑⦆ = cong (λ - → - ∨ ((x ∧ y) ∧ y′)) (⊓[ F ]-assoc y x x′)
    ⦅𝟒⦆ = cong (λ - → (y ∧ -) ∨ ((x ∧ y) ∧ y′)) x∧x=⊥
    ⦅𝟓⦆ = cong (λ - → - ∨ ((x ∧ y) ∧ y′)) (x∧⊥=⊥ F y)
    ⦅𝟔⦆ = x∨⊥=x F ((x ∧ y) ∧ y′)
    ⦅𝟕⦆ = ⊓[ F ]-assoc x y y′
    ⦅𝟖⦆ = cong (λ - → x ∧ -) y∧y′=⊥
    ⦅𝟗⦆ = x∧⊥=⊥ F x

  G𝟐 : (x ∧ y) ∨ (x′ ∨ y′) ≡ ⊤[ F ]
  G𝟐 = (x ∧ y) ∨ (x′ ∨ y′)                  ≡⟨ ⦅𝟏⦆  ⟩
       (x′ ∨ y′) ∨ (x ∧ y)                  ≡⟨ ⦅𝟐⦆  ⟩
       (((x′ ∨ y′) ∨ x) ∧ ((x′ ∨ y′) ∨ y))  ≡⟨ ⦅𝟑⦆  ⟩
       (((y′ ∨ x′) ∨ x) ∧ ((x′ ∨ y′) ∨ y))  ≡⟨ ⦅𝟒⦆  ⟩
       ((y′ ∨ (x′ ∨ x)) ∧ ((x′ ∨ y′) ∨ y))  ≡⟨ ⦅𝟓⦆  ⟩
       ((y′ ∨ ⊤[ F ]) ∧ ((x′ ∨ y′) ∨ y))    ≡⟨ ⦅𝟔⦆  ⟩
       ⊤[ F ] ∧ ((x′ ∨ y′) ∨ y)             ≡⟨ ⦅𝟕⦆  ⟩
       ((x′ ∨ y′) ∨[ F ] y)                 ≡⟨ ⦅𝟖⦆  ⟩
       x′ ∨ (y′ ∨[ F ] y)                   ≡⟨ ⦅𝟗⦆  ⟩
       x′ ∨ ⊤[ F ]                          ≡⟨ ⦅𝟏𝟎⦆ ⟩
       ⊤[ F ]                               ∎
    where
    ⦅𝟏⦆  = ∨-comm F (x ∧ y) (x′ ∨ y′)
    ⦅𝟐⦆  = bin-dist-op F (x′ ∨ y′) x y
    ⦅𝟑⦆  = cong (λ - → (- ∨ x) ∧ ((x′ ∨ y′) ∨ y)) (∨-comm F x′ y′)
    ⦅𝟒⦆  = cong (λ - → - ∧ ((x′ ∨ y′) ∨ y)) (∨[ F ]-assoc y′ x′ x)
    ⦅𝟓⦆  = cong (λ - → (y′ ∨ -) ∧ ((x′ ∨ y′) ∨ y)) (_ ≡⟨ ∨-comm F x′ x ⟩ _  ≡⟨ x∨x′=⊤ ⟩ _ ∎)
    ⦅𝟔⦆  = cong (λ - → - ∧ ((x′ ∨ y′) ∨ y)) (x∨⊤=⊤ F y′ )
    ⦅𝟕⦆  = ⊤[ F ] ∧ ((x′ ∨ y′) ∨ y)  ≡⟨ comm F ⊤[ F ] ((x′ ∨ y′) ∨ y) ⟩
           ((x′ ∨ y′) ∨ y) ∧ ⊤[ F ]  ≡⟨ x∧⊤=x F ((x′ ∨ y′) ∨ y) ⟩
           (x′ ∨ y′) ∨ y             ∎
    ⦅𝟖⦆  = ∨[ F ]-assoc x′ y′ y
    ⦅𝟗⦆  = cong (λ - → x′ ∨ -) (_ ≡⟨ ∨-comm F y′ y ⟩ y ∨[ F ] y′ ≡⟨ y∨y′=⊤ ⟩ _ ∎)
    ⦅𝟏𝟎⦆ = x∨⊤=⊤ F x′

complements-sym : (F : Frame 𝓤 𝓥 𝓦)
                → {x x′ : ∣ F ∣F}
                → complements F x  x′
                → complements F x′ x
complements-sym F {x} {x′} (p , q) = G𝟏 , G𝟐
  where
  G𝟏 : x′ ⊓[ F ] x ≡ ⊥[ F ]
  G𝟏 = x′ ⊓[ F ] x  ≡⟨ comm F x′ x ⟩
       x  ⊓[ F ] x′ ≡⟨ p ⟩
       ⊥[ F ]       ∎

  G𝟐 : x′ ∨[ F ] x ≡ ⊤[ F ]
  G𝟐 = x′ ∨[ F ] x  ≡⟨ ∨-comm F x′ x ⟩
       x  ∨[ F ] x′ ≡⟨ q ⟩
       ⊤[ F ]       ∎

∧-has-complement : (F : Frame 𝓤 𝓥 𝓦) (x y : ∣ F ∣F)
                 → hasComplement F x
                 → hasComplement F y
                 → hasComplement F (x ⊓[ F ] y)
∧-has-complement F x y (¬x , ¬x-complements-x) (¬y , ¬y-complements-y) =
  ¬x ∨[ F ] ¬y , ∧-complement F x y ¬x ¬y ¬x-complements-x ¬y-complements-y
```
