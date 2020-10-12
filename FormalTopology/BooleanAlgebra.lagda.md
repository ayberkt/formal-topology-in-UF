---
title: Boolean Algebra
---

## Preamble

```agda
{-# OPTIONS --cubical --safe #-}

module BooleanAlgebra where

open import Cubical.Core.Everything     hiding (_∧_; _∨_)
open import Cubical.Foundations.Logic   using  (hProp; [_])
open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.Sigma

open import Poset
open import Lattice renaming (pos to pos-of-lattice)

open import Basis using (isoToEquiv; section; retract; isoToPath)

private
  variable
    ℓ ℓ₀ ℓ₁ : Level
```

## Definition

```agda
hasComplements : (L : Lattice ℓ₀ ℓ₁) → Type ℓ₀
hasComplements L =
  (x : ∣ L ∣ₗ) → Σ[ ¬x ∈ ∣ L ∣ₗ ] (¬x ∧[ L ] x ≡ ⊥[ L ]) × (¬x ∨[ L ] x ≡ ⊤[ L ])

BooleanAlgebra : (ℓ₀ ℓ₁ : Level) → Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁))
BooleanAlgebra ℓ₀ ℓ₁ = Σ[ L ∈ Lattice ℓ₀ ℓ₁ ] isDistributive L × hasComplements L

∣_∣B : BooleanAlgebra ℓ₀ ℓ₁ → Type ℓ₀
∣ L , _ ∣B = ∣ L ∣ₗ

¬[_]_ : (B : BooleanAlgebra ℓ₀ ℓ₁) → ∣ B ∣B → ∣ B ∣B
¬[ _ , _ , ¬_ ] x = fst (¬ x)

pos : BooleanAlgebra ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁
pos (L , _ , _) = pos-of-lattice L

latt : BooleanAlgebra ℓ₀ ℓ₁ → Lattice ℓ₀ ℓ₁
latt (L , _) = L

¬-inv-∧ : (B : BooleanAlgebra ℓ₀ ℓ₁)
        → (x : ∣ B ∣B) → (¬[ B ] x) ∧[ latt B ] x ≡ ⊥[ latt B ]
¬-inv-∧ (_ , _ , comp) x = fst (snd (comp x))

¬-inv-∨ : (B : BooleanAlgebra ℓ₀ ℓ₁)
        → (x : ∣ B ∣B) → (¬[ B ] x) ∨[ latt B ] x ≡ ⊤[ latt B ]
¬-inv-∨ (_ , _ , comp) x = snd (snd (comp x))
```

# Symmetric difference

```agda
sym-diff : (B : BooleanAlgebra ℓ₀ ℓ₁) → ∣ B ∣B → ∣ B ∣B → ∣ B ∣B
sym-diff B@(L , _) x y = (x ∧[ L ] (¬[ B ] y)) ∨[ L ] (y ∧[ L ] (¬[ B ] x))

syntax sym-diff B x y = x ⊕[ B ] y

module SymmetricDifference (B : BooleanAlgebra ℓ₀ ℓ₁) where

  L = fst B

  _⊕_ : ∣ B ∣B → ∣ B ∣B → ∣ B ∣B
  x ⊕ y = x ⊕[ B ] y

  -- TODO: prove the following
  -- ⊕-dist : (x y z : ∣ B ∣B) → x ∧[ L ] (y ⊕ z) ≡ (x ∧[ L ] y) ⊕ (x ∧[ L ] z)
```

# Direct Definition of Boolean Algebras

```agda
record BooleanAlgebraStr (A : Type ℓ) : Type ℓ where
  field
    _⊓_ : A → A → A
    _⊔_ : A → A → A
    ⊤   : A
    ⊥   : A
    ¬_  : A → A

    ⊓-assoc : (x y z : A) → x ⊓ (y ⊓ z) ≡ (x ⊓ y) ⊓ z
    ⊔-assoc : (x y z : A) → x ⊔ (y ⊔ z) ≡ (x ⊔ y) ⊔ z

    ⊓-comm  : (x y   : A) → x ⊓ y ≡ y ⊓ x
    ⊔-comm  : (x y   : A) → x ⊔ y ≡ y ⊔ x

    ⊓-absorb : (x y : A) → x ⊓ (y ⊔ x) ≡ x
    ⊔-absorb : (x y : A) → x ⊔ (y ⊓ x) ≡ x

    ⊤-id : (x : A) → x ⊓ ⊤ ≡ x
    ⊥-id : (x : A) → x ⊔ ⊥ ≡ x

    ∧-dist : (x y z : A) → x ⊓ (y ⊔ z) ≡ (x ⊓ y) ⊔ (x ⊓ z)
    ∨-dist : (x y z : A) → x ⊔ (y ⊓ z) ≡ (x ⊔ y) ⊓ (x ⊔ z)

    ∧-inv : (x : A) → x ⊓ (¬ x) ≡ ⊥
    ∨-inv : (x : A) → (¬ x) ⊔ x ≡ ⊤

    A-set : isSet A

  x⊓x=x : (x : A) → x ⊓ x ≡ x
  x⊓x=x x = x ⊓ x          ≡⟨ cong (λ - → x ⊓ -) (sym (⊥-id x)) ⟩
               x ⊓ (x ⊔ ⊥) ≡⟨ cong (λ - → x ⊓ -) (⊔-comm x ⊥)   ⟩
               x ⊓ (⊥ ⊔ x) ≡⟨ ⊓-absorb x ⊥                      ⟩
               x           ∎


  ⊥-anni : (x : A) → x ⊓ ⊥ ≡ ⊥
  ⊥-anni x = x ⊓ ⊥            ≡⟨ cong (λ - → x ⊓ -) (sym (∧-inv x)) ⟩
             x ⊓ (x ⊓ (¬ x))  ≡⟨ ⊓-assoc x x (¬ x)                  ⟩
             (x ⊓ x) ⊓ (¬ x)  ≡⟨ cong (λ - → - ⊓ (¬ x)) (x⊓x=x x)   ⟩
             x ⊓ (¬ x)        ≡⟨ ∧-inv x                            ⟩
             ⊥                ∎

  ⊓-comm-tac : (P : A → Type ℓ₁) {x y : A} → P (x ⊓ y) → P (y ⊓ x)
  ⊓-comm-tac P {x} {y} = subst P (⊓-comm x y)
```

```agda
BooleanAlgebra′ : (ℓ : Level) → Type (ℓ-suc ℓ)
BooleanAlgebra′ ℓ = Σ[ A ∈ Type ℓ ] BooleanAlgebraStr A
```

## Equivalence of These Definitions

```agda
bool⇒bool′ : BooleanAlgebra ℓ₀ ℓ₁ → BooleanAlgebra′ ℓ₀
bool⇒bool′ B@(L , dist , complements) = ∣ L ∣ₗ , BA
  where
    open BooleanAlgebraStr

    BA : BooleanAlgebraStr ∣ L ∣ₗ
    _⊓_      BA  = λ x y → x ∧[ L ] y
    _⊔_      BA  = λ x y → x ∨[ L ] y
    ⊤        BA  = ⊤[ L ]
    ⊥        BA  = ⊥[ L ]
    ¬        BA  = λ x → ¬[ B ] x
    ⊓-assoc  BA  = ∧-assoc L
    ⊔-assoc  BA  = ∨-assoc L
    ⊓-comm   BA  = ∧-comm L
    ⊔-comm   BA  = ∨-comm L
    ⊓-absorb BA  = ∧-absorb L
    ⊔-absorb BA  = ∨-absorb L
    ⊤-id     BA  = ∧-id L
    ⊥-id     BA  = ∨-id L
    ∧-dist   BA  = dist
    ∨-dist   BA  = dist⇒distᵒᵖ L dist
    ∧-inv    BA  = λ x → subst (λ - → - ≡ ⊥[ L ]) (∧-comm L _ _) (¬-inv-∧ B x)
    ∨-inv    BA  = ¬-inv-∨ B
    A-set    BA  = carrier-is-set (pos-of-lattice L)
```

```agda
pos-ba : BooleanAlgebra′ ℓ₀ → Poset ℓ₀ ℓ₀
pos-ba (A , B-str) = A , _⊑_ , A-set , ⊑-refl , ⊑-trans , ⊑-antisym
  where
    open BooleanAlgebraStr B-str

    _⊑_ : A → A → hProp _
    x ⊑ y = (x ⊓ y ≡ x) , A-set (x ⊓ y) x

    ⊑-refl : [ isReflexive _⊑_ ]
    ⊑-refl x = x ⊓ x       ≡⟨ cong (λ - → x ⊓ -) (sym (⊥-id x)) ⟩
               x ⊓ (x ⊔ ⊥) ≡⟨ cong (λ - → x ⊓ -) (⊔-comm x ⊥)   ⟩
               x ⊓ (⊥ ⊔ x) ≡⟨ ⊓-absorb x ⊥                      ⟩
               x           ∎

    ⊑-trans : [ isTransitive _⊑_ ]
    ⊑-trans x y z x⊑y y⊑z = x ⊓ z       ≡⟨ cong (λ - → - ⊓ z) (sym x⊑y) ⟩
                            (x ⊓ y) ⊓ z ≡⟨ sym (⊓-assoc x y z)          ⟩
                            x ⊓ (y ⊓ z) ≡⟨ cong (λ - → x ⊓ -) y⊑z       ⟩
                            x ⊓ y       ≡⟨ x⊑y                          ⟩
                            x           ∎

    ⊑-antisym : [ isAntisym A-set _⊑_ ]
    ⊑-antisym x y x⊑y y⊑x =
      x ≡⟨ sym x⊑y ⟩ x ⊓ y ≡⟨ ⊓-comm x y ⟩ y ⊓ x ≡⟨ y⊑x ⟩ y ∎
```

```agda
latt-ba : BooleanAlgebra′ ℓ₀ → Lattice ℓ₀ ℓ₀
latt-ba (A , B-str) = pos-ba (A , B-str) , is-lattice
  where
    open BooleanAlgebraStr B-str

    P = pos-ba (A , B-str)

    is-lattice : isALattice (pos-ba (A , B-str))
    is-lattice = ((⊤ , ⊤-id) , NTS) , (⊥ , λ y → ⊓-comm-tac (λ - → - ≡ ⊥) (⊥-anni y)) , bin-joins
      where
        NTS : hasBinaryMeets (pos-ba (A , B-str))
        NTS x y = x ⊓ y , (x⊓y⊓x=x⊓y , x⊓y⊓y=x⊓y) , NTS′
          where
            x⊓y⊓x=x⊓y : ((x ⊓ y) ⊓ x) ≡ x ⊓ y
            x⊓y⊓x=x⊓y = (x ⊓ y) ⊓ x  ≡⟨ cong (λ - → - ⊓ x) (⊓-comm x y)    ⟩
                        (y ⊓ x) ⊓ x  ≡⟨ sym (⊓-assoc y x x)                ⟩
                        y ⊓ (x ⊓ x)  ≡⟨ cong (λ - → y ⊓ -) (⊑[ P ]-refl x) ⟩
                        y ⊓ x        ≡⟨ ⊓-comm y x                         ⟩
                        x ⊓ y        ∎

            x⊓y⊓y=x⊓y : ((x ⊓ y) ⊓ y) ≡ x ⊓ y
            x⊓y⊓y=x⊓y = (x ⊓ y) ⊓ y  ≡⟨ sym (⊓-assoc x y y) ⟩
                        x ⊓ (y ⊓ y)  ≡⟨ cong (λ - → x ⊓ -) (⊑[ P ]-refl y) ⟩
                        x ⊓ y        ∎

            NTS′ : (x′ : ∣ pos-ba (A , B-str) ∣ₚ) → [ rel₂ᵒᵖ (pos-ba (A , B-str)) x y x′ ] → [ rel (pos-ba (A , B-str)) x′ (x ⊓ y) ]
            NTS′ z (z⊑x , z⊑y) = z ⊓ (x ⊓ y)    ≡⟨ ⊓-assoc z x y          ⟩
                                 (z ⊓ x) ⊓ y    ≡⟨ cong (λ - → - ⊓ y) z⊑x ⟩
                                 (z ⊓ y)        ≡⟨ z⊑y                    ⟩
                                 z              ∎

        bin-joins : hasBinaryJoins P
        bin-joins x y = (x ⊔ y) , (x⊓x⊔y=x , ⊓-absorb y x) , rem
          where
            x⊓x⊔y=x : x ⊓ (x ⊔ y) ≡ x
            x⊓x⊔y=x = x ⊓ (x ⊔ y) ≡⟨ cong (λ - → x ⊓ -) (⊔-comm x y) ⟩
                      x ⊓ (y ⊔ x) ≡⟨ ⊓-absorb x y                    ⟩
                      x           ∎

            rem : (x′ : ∣ P ∣ₚ) → [ rel₂ P x y x′ ] → [ rel P (x ⊔ y) x′ ]
            rem z (x⊑z , y⊑z) =
              (x ⊔ y) ⊓ z       ≡⟨ ⊓-comm _ _                            ⟩
              z ⊓ (x ⊔ y)       ≡⟨ ∧-dist z x y                          ⟩
              (z ⊓ x) ⊔ (z ⊓ y) ≡⟨ cong (λ - → - ⊔ (z ⊓ y)) (⊓-comm z x) ⟩
              (x ⊓ z) ⊔ (z ⊓ y) ≡⟨ cong (λ - → (x ⊓ z) ⊔ -) (⊓-comm z y) ⟩
              (x ⊓ z) ⊔ (y ⊓ z) ≡⟨ cong (λ - → - ⊔ (y ⊓ z)) x⊑z          ⟩
              x       ⊔ (y ⊓ z) ≡⟨ cong (λ - → x ⊔ -) y⊑z                ⟩
              x       ⊔ y       ∎
```

```agda
bool′⇒bool : BooleanAlgebra′ ℓ₀ → BooleanAlgebra ℓ₀ ℓ₀
bool′⇒bool (A , B-str) = L , ∧-dist , comps
  where
    L = latt-ba (A , B-str)

    open BooleanAlgebraStr B-str

    comps : hasComplements L
    comps x = (¬ x) , (¬x∧x=⊥ , ∨-inv x)
      where
        ¬x∧x=⊥ : (¬ x) ∧[ L ] x ≡ ⊥[ L ]
        ¬x∧x=⊥ =
          (¬ x) ∧[ L ] x ≡⟨ ∧-comm L _ _ ⟩ x ∧[ L ] (¬ x) ≡⟨ ∧-inv x ⟩ ⊥[ L ] ∎
```

```agda
bool≃bool′ : BooleanAlgebra′ ℓ₀ ≃ BooleanAlgebra ℓ₀ ℓ₀
bool≃bool′ {ℓ₀} = isoToEquiv (Basis.iso bool′⇒bool bool⇒bool′ sec ret)
  where
    sec : section bool′⇒bool bool⇒bool′
    sec (L , _) = Σ≡Prop {!!} {!!}

    ret : retract bool′⇒bool bool⇒bool′
    ret (A , B-str) = fst ΣPathP≃PathPΣ (refl , {!!})
```

## Some laws
