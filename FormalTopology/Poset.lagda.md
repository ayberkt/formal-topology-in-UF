```
{-# OPTIONS --without-K --cubical --safe #-}

module Poset where

open import Basis
open import Cubical.Foundations.SIP
open import Cubical.Structures.Axioms
open import Cubical.Foundations.Equiv using (_≃⟨_⟩_) renaming (_■ to _𝔔𝔈𝔇)
```

## Definition of poset

```agda
Order : (ℓ₁ : Level) → Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ₁))
Order ℓ₁ A = A → A → hProp ℓ₁

Order-set : (ℓ₁ : Level) (A : Type ℓ₀) → isSet (Order ℓ₁ A)
Order-set ℓ₁ A = isSetΠ2 λ _ _ → isSetHProp

isReflexive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ-max ℓ₀ ℓ₁)
isReflexive {A = X} _⊑_ =
  ((x : X) → [ x ⊑ x ]) , isPropΠ (λ x → is-true-prop (x ⊑ x))

isTransitive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ-max ℓ₀ ℓ₁)
isTransitive {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = X} _⊑_ = ⊑-trans , ⊑-trans-prop
  where
    ⊑-trans : Type (ℓ-max ℓ₀ ℓ₁)
    ⊑-trans = ((x y z : X) → [ x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z ])

    ⊑-trans-prop : isProp  ⊑-trans
    ⊑-trans-prop = isPropΠ3 λ x y z → is-true-prop (x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z)

isAntisym : {A : Type ℓ₀} → isSet A → Order ℓ₁ A → hProp (ℓ-max ℓ₀ ℓ₁)
isAntisym {A = A} A-set _⊑_ = ⊑-antisym , ⊑-antisym-prop
  where
    ⊑-antisym = (x y : A) → [ x ⊑ y ] → [ y ⊑ x ] → x ≡ y

    ⊑-antisym-prop : isProp ⊑-antisym
    ⊑-antisym-prop = isPropΠ2 λ x y → isPropΠ2 λ _ _ → A-set x y

PosetAx : (A : Type ℓ₀) → Order ℓ₁ A → hProp (ℓ-max ℓ₀ ℓ₁)
PosetAx {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} A _⊑_ = isAPartialSet , isAPartialSet-prop
  where
    isAPartialSet =
      Σ[ A-set ∈ isSet A ] [ isReflexive _⊑_ ⊓ isTransitive _⊑_ ⊓ isAntisym A-set _⊑_ ]

    isAPartialSet-prop =
      isPropΣ isPropIsSet λ A-set →
        is-true-prop (isReflexive _⊑_ ⊓ isTransitive _⊑_ ⊓ isAntisym A-set _⊑_)
```

A poset structure with level `ℓ₁`.

```agda
PosetStr : (ℓ₁ : Level) → Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ₁))
PosetStr ℓ₁ A = Σ[ ⊑ ∈ Order ℓ₁ A ] [ PosetAx A ⊑ ]

PosetStr-set : (ℓ₁ : Level) (A : Type ℓ₀) → isSet (PosetStr ℓ₁ A)
PosetStr-set ℓ₁ A =
  isSetΣ (isSetΠ λ _ → isSetΠ λ _ → isSetHProp) λ _⊑_ →
  isSetΣ (isProp→isSet isPropIsSet) λ A-set →
    isProp→isSet (is-true-prop (isReflexive _⊑_ ⊓ isTransitive _⊑_ ⊓ isAntisym A-set _⊑_))
```

A poset with carrier level `ℓ₀` and relation level `ℓ₁`.

```agda
Poset : (ℓ₀ ℓ₁ : Level) → Type (ℓ-max (ℓ-suc ℓ₀) (ℓ-suc ℓ₁))
Poset ℓ₀ ℓ₁ = Σ (Type ℓ₀) (PosetStr ℓ₁)
```

## Projections

Given a poset `P`, `∣ P ∣ₚ` denotes its carrier set and `strₚ P` its order structure.

```agda
∣_∣ₚ : Poset ℓ₀ ℓ₁ → Type ℓ₀
∣ X , _ ∣ₚ = X

strₚ : (P : Poset ℓ₀ ℓ₁) → PosetStr ℓ₁ ∣ P ∣ₚ
strₚ (_ , s) = s
```

We refer to to the order of `P` as `_⊑[ P ]_`.

```agda
rel : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ → hProp ℓ₁
rel (_ , _⊑_ , _) = _⊑_

infix 9 rel

syntax rel P x y = x ⊑[ P ] y

rel₂ : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ → hProp ℓ₁
rel₂ P x y z = (x ⊑[ P ] z) ⊓ (y ⊑[ P ] z)

syntax rel₂ P x y z = ⟨ x , y ⟩⊑[ P ] z

relᵒᵖ : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ → hProp ℓ₁
relᵒᵖ (_ , _⊑_ , _) x y = y ⊑ x

syntax relᵒᵖ P x y = x ⊒[ P ] y
```

Similarly, we define projections for the poset properties.

```agda
⊑[_]-refl : (P : Poset ℓ₀ ℓ₁) → (x : ∣ P ∣ₚ) → [ x ⊑[ P ] x ]
⊑[_]-refl (_ , _ , _ , ⊑-refl , _) = ⊑-refl

⊑[_]-trans : (P : Poset ℓ₀ ℓ₁) (x y z : ∣ P ∣ₚ)
           → [ x ⊑[ P ] y ] → [ y ⊑[ P ] z ] → [ x ⊑[ P ] z ]
⊑[_]-trans (_ , _ , _ , _ , ⊑-trans , _) = ⊑-trans

⊑[_]-antisym : (P : Poset ℓ₀ ℓ₁) (x y : ∣ P ∣ₚ)
             → [ x ⊑[ P ] y ] → [ y ⊑[ P ] x ] → x ≡ y
⊑[_]-antisym (_ , _ , _ , _ , _ , ⊑-antisym) = ⊑-antisym

carrier-is-set : (P : Poset ℓ₀ ℓ₁) → isSet ∣ P ∣ₚ
carrier-is-set (_ , _ , is-set , _) = is-set
```

## Partial order reasoning

```agda
module PosetNotation (P : Poset 𝓤 𝓥) where

  _≤_ : ∣ P ∣ₚ → ∣ P ∣ₚ → hProp 𝓥
  x ≤ y = x ⊑[ P ] y
```

Some convenient notation for carrying out inequality reasoning.

```agda
module PosetReasoning (P : Poset ℓ₀ ℓ₁) where

  _⊑⟨_⟩_ : (x : ∣ P ∣ₚ) {y z : ∣ P ∣ₚ}
         → [ x ⊑[ P ] y ] → [ y ⊑[ P ] z ] → [ x ⊑[ P ] z ]
  _ ⊑⟨ p ⟩ q = ⊑[ P ]-trans _ _ _ p q

  _■ : (x : ∣ P ∣ₚ) → [ x ⊑[ P ] x ]
  _■ = ⊑[ P ]-refl

  infixr 0 _⊑⟨_⟩_
  infix  1 _■
```

It is not convenient to have to keep applying `subst` for the show that two equal things
are below each other so let us make note of the following trivial fact.

```agda
≡⇒⊑ : (P : Poset ℓ₀ ℓ₁) → {x y : ∣ P ∣ₚ} → x ≡ y → [ x ⊑[ P ] y ]
≡⇒⊑ P {x = x} p = subst (λ z → [ x ⊑[ P ] z ]) p (⊑[ P ]-refl x)
```

## Monotonic functions

We can define the notion preserving the order of a order structure for all types with
orders.

```agda
isOrderPreserving : (M : Σ (Type ℓ₀) (Order ℓ₁)) (N : Σ (Type ℓ₀′) (Order ℓ₁′))
                  → (π₀ M → π₀ N) → Type _
isOrderPreserving (A , _⊑₀_) (B , _⊑₁_) f = (x y : A) → [ x ⊑₀ y ] → [ f x ⊑₁ f y ]
```

Technically, this is called "monotonic" as well but we will reserve that term for posets.

```agda
isMonotonic : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′)
            → (∣ P ∣ₚ → ∣ Q ∣ₚ) → Type _
isMonotonic (A , (_⊑₀_ , _)) (B , (_⊑₁_ , _)) = isOrderPreserving (A , _⊑₀_) (B , _⊑₁_)
```

Both of these notions are propositional.

```agda
isOrderPreserving-prop : (M : Σ (Type ℓ₀) (Order ℓ₁)) (N : Σ (Type ℓ₀′) (Order ℓ₁′))
                         (f : π₀ M → π₀ N)
                       → isProp (isOrderPreserving M N f)
isOrderPreserving-prop M (_ , _⊑₁_) f = isPropΠ3 λ x y p → is-true-prop ((f x) ⊑₁ (f y))

isMonotonic-prop : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′) (f : ∣ P ∣ₚ → ∣ Q ∣ₚ)
                 → isProp (isMonotonic P Q f)
isMonotonic-prop (A , (_⊑₀_ , _)) (B , (_⊑₁_ , _)) f =
  isOrderPreserving-prop (A , _⊑₀_) (B , _⊑₁_) f
```

We then collect monotonic functions in the following type.

```agda
_─m→_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀′ ℓ₁′ → Type _
_─m→_ P Q = Σ (∣ P ∣ₚ → ∣ Q ∣ₚ) (isMonotonic P Q)
```

Projection for the underlying function of a monotonic map.

```agda
_$ₘ_ = π₀
```

The identity monotonic map and composition of monotonic maps.

```agda
𝟏m : (P : Poset ℓ₀ ℓ₁) → P ─m→ P
𝟏m P = id ∣ P ∣ₚ , (λ x y x⊑y → x⊑y)

_∘m_ : {P : Poset ℓ₀ ℓ₁} {Q : Poset ℓ₀′ ℓ₁′} {R : Poset ℓ₀′′ ℓ₁′′}
     → (Q ─m→ R) → (P ─m→ Q) → (P ─m→ R)
(g , pg) ∘m (f , pf) = g ∘ f , λ x y p → pg (f x) (f y) (pf x y p)
```


We will often deal with the task of showing the equality of two monotonic functions. As
being monotonic is propositional, we can quickly reduce this to showing the equality of
the underlying functions using `ΣProp≡` but it is more convenient to record this fact in
advance.

```agda
forget-mono : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′) ((f , f-mono) (g , g-mono) : P ─m→ Q)
            → f ≡ g
            → (f , f-mono) ≡ (g , g-mono)
forget-mono P Q (f , f-mono) (g , g-mono) =
  Σ≡Prop (λ f → isPropΠ3 λ x y x⊑y → is-true-prop (f x ⊑[ Q ] f y))
```

## Downward-closure

We denote by `↓[ P ] x` the type of everything in `P` that is below `x`.

```agda
↓[_]_ : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → Type _
↓[ P ] a = Σ[ b ∈ ∣ P ∣ₚ ] [ b ⊑[ P ] a ]
```

```agda
isDownwardsClosed : (P : Poset ℓ₀ ℓ₁) → 𝒫 ∣ P ∣ₚ → hProp _
isDownwardsClosed P U =
  ((x y : ∣ P ∣ₚ) → [ x ∈ U ] → [ y ⊑[ P ] x ] → [ y ∈ U ]) , prop
  where
    prop : isProp ((x y : ∣ P ∣ₚ) → [ U x ] → [ y ⊑[ P ] x ] → [ U y ])
    prop = isPropΠ λ _ → isPropΠ λ x → isPropΠ λ _ → isPropΠ λ _ → is-true-prop (x ∈ U)

DCSubset : (P : Poset ℓ₀ ℓ₁) → Type _
DCSubset P = Σ[ U ∈ 𝒫 ∣ P ∣ₚ ] [ isDownwardsClosed P U ]

DCSubset-set : (P : Poset ℓ₀ ℓ₁) → isSet (DCSubset P)
DCSubset-set P =
  isSetΣ (𝒫-set ∣ P ∣ₚ) λ U → isProp→isSet (is-true-prop (isDownwardsClosed P U))
```

## Directedness

The notion of a *directed subset*, manifested here as a directed *family*.

```agda
isDirected : {ℓ₂ : Level} → (P : Poset ℓ₀ ℓ₁) → Fam ℓ₂ ∣ P ∣ₚ → hProp (ℓ-max ℓ₁ ℓ₂)
isDirected P U@(I , _) =
  U-inhabited ⊓ (∀[ i ∶ I ] ∀[ j ∶ I ] ∥ Σ[ k ∈ I ] [ ⟨ (U $ i) , (U $ j) ⟩⊑[ P ] (U $ k) ] ∥ , ∥∥-prop _)
  where
    U-inhabited : hProp _
    U-inhabited = ∥ index U ∥ , (∥∥-prop I)
```

## Product of two posets

```agda
_×ₚ_ : (P : Poset ℓ₀ ℓ₁) (Q : Poset ℓ₀′ ℓ₁′) → Poset _ _
P ×ₚ Q = (∣ P ∣ₚ × ∣ Q ∣ₚ) , _⊑_ , carrier-set , (⊑-refl , ⊑-trans , ⊑-antisym)
  where
    _⊑_ : ∣ P ∣ₚ × ∣ Q ∣ₚ → ∣ P ∣ₚ × ∣ Q ∣ₚ → hProp _
    _⊑_ (x₀ , y₀) (x₁ , y₁) = x₀ ⊑[ P ] x₁ ⊓ y₀ ⊑[ Q ] y₁

    carrier-set : isSet (∣ P ∣ₚ × ∣ Q ∣ₚ)
    carrier-set = isSetΣ (carrier-is-set P) λ _ → (carrier-is-set Q)

    ⊑-refl : (p : ∣ P ∣ₚ × ∣ Q ∣ₚ) → [ p ⊑ p ]
    ⊑-refl (x , y) = (⊑[ P ]-refl x) , (⊑[ Q ]-refl y)

    ⊑-trans : (p q r : ∣ P ∣ₚ × ∣ Q ∣ₚ) → [ p ⊑ q ] → [ q ⊑ r ] → [ p ⊑ r ]
    ⊑-trans (x₀ , y₀) (x₁ , y₁) (x₂ , y₂) (x₀⊑x₁ , y₀⊑y₁) (x₁⊑x₂ , y₁⊑y₂) =
      ⊑[ P ]-trans _ _ _ x₀⊑x₁ x₁⊑x₂ , ⊑[ Q ]-trans _ _ _ y₀⊑y₁ y₁⊑y₂

    ⊑-antisym : (p q : ∣ P ∣ₚ × ∣ Q ∣ₚ) → [ p ⊑ q ] → [ q ⊑ p ] → p ≡ q
    ⊑-antisym (x₀ , y₀) (x₁ , y₁) (x₀⊑x₁ , y₀⊑y₁) (x₁⊑x₀ , y₁⊑y₀) =
      ΣPathTransport→PathΣ (x₀ , y₀) (x₁ , y₁) (⊑[ P ]-antisym _ _ x₀⊑x₁ x₁⊑x₀ , sym NTS)
      where
        NTS : y₁ ≡ transport refl y₀
        NTS = subst (_≡_ y₁) (sym (transportRefl y₀)) (⊑[ Q ]-antisym _ _ y₁⊑y₀ y₀⊑y₁)
```

The *diagonal* monotonic map.

```agda
Δ : (P : Poset ℓ₀ ℓ₁) → P ─m→ (P ×ₚ P)
Δ P = f , f-mono
  where
    f : ∣ P ∣ₚ → ∣ P ×ₚ P ∣ₚ
    f x = x , x

    f-mono : isMonotonic P (P ×ₚ P) f
    f-mono x y x⊑y = x⊑y , x⊑y
```

## Posetal Yoneda lemma

```agda
yoneda : (P : Poset ℓ₀ ℓ₁)
       → (x y : ∣ P ∣ₚ)
       → [ (x ⊑[ P ] y) ⇔ (∀[ z ∶ ∣ P ∣ₚ ] z ⊑[ P ] x ⇒ z ⊑[ P ] y) ]
yoneda P x y = forwards , backwards
  where
    open PosetReasoning P

    forwards : [ x ⊑[ P ] y ⇒ (∀[ z ∶ ∣ P ∣ₚ ] z ⊑[ P ] x ⇒ z ⊑[ P ] y) ]
    forwards x⊑y z z⊑x = z ⊑⟨ z⊑x ⟩ x ⊑⟨ x⊑y ⟩ y ■

    backwards : [ (∀[ z ∶ ∣ P ∣ₚ ] z ⊑[ P ] x ⇒ z ⊑[ P ] y) ⇒ x ⊑[ P ] y ]
    backwards p = p x (⊑[ P ]-refl x)
```

## Galois connections

```agda
module GaloisConnection (P Q : Poset ℓ₀ ℓ₁) where

  _⊣_ : (P ─m→ Q) → (Q ─m→ P) → hProp (ℓ-max ℓ₀ ℓ₁)
  f ⊣ g = ∀[ x ∶ ∣ P ∣ₚ ] ∀[ y ∶ ∣ Q ∣ₚ ] f $ₘ x ⊑[ Q ] y ⇔ x ⊑[ P ] g $ₘ y

  ⊣-unique-right : (f : P ─m→ Q) (g₀ g₁ : Q ─m→ P)
                 → [ f ⊣ g₀ ] → [ f ⊣ g₁ ] → g₀ ≡ g₁
  ⊣-unique-right f g₀ g₁ f⊣g₀ f⊣g₁ = forget-mono Q P g₀ g₁ (funExt g₀~g₁)
    where
      g₀~g₁ : (y : ∣ Q ∣ₚ) → g₀ $ₘ y ≡ g₁ $ₘ y
      g₀~g₁ y = ⊑[ P ]-antisym (g₀ $ₘ y) (g₁ $ₘ y) NTS₀ NTS₁
        where
          α : [ f $ₘ (g₀ $ₘ y) ⊑[ Q ] y ⇔ (g₀ $ₘ y ⊑[ P ] g₁ $ₘ y) ]
          α = f⊣g₁ (g₀ $ₘ y) y

          β : [ (f $ₘ (g₀ $ₘ y)) ⊑[ Q ] y ⇔ (g₀ $ₘ y) ⊑[ P ] (g₀ $ₘ y) ]
          β = f⊣g₀ (g₀ $ₘ y) y

          NTS₀ : [ g₀ $ₘ y ⊑[ P ] g₁ $ₘ y ]
          NTS₀ = π₀ α (π₁ β (⊑[ P ]-refl _))

          φ : [ (f $ₘ (g₁ $ₘ y) ⊑[ Q ] y) ⇔ (g₁ $ₘ y ⊑[ P ] g₀ $ₘ y) ]
          φ = f⊣g₀ (g₁ $ₘ y) y

          ψ : [ f $ₘ (g₁ $ₘ y) ⊑[ Q ] y ⇔ ((g₁ $ₘ y) ⊑[ P ] (g₁ $ₘ y))]
          ψ = f⊣g₁ (g₁ $ₘ y) y

          NTS₁ : [ g₁ $ₘ y ⊑[ P ] g₀ $ₘ y ]
          NTS₁ = π₀ φ (π₁ ψ (⊑[ P ]-refl _))

  GaloisConnection : Type (ℓ-max ℓ₀ ℓ₁)
  GaloisConnection = Σ[ f ∈ P ─m→ Q  ] Σ[ g ∈ Q ─m→ P ] [ f ⊣ g ]
```


## Poset univalence

Now, we would like to show that ordered structures, as given by `Order`, are a standard
notion of structure. As we have already written down what it means for a function to be
order-preserving, we can express what it means for a *type equivalence* to be order
preserving.

```agda
isAnOrderPreservingEqv : (M N : Σ (Type ℓ₀) (Order ℓ₁)) → π₀ M ≃ π₀ N → Type _ 
isAnOrderPreservingEqv M N e@(f , _) =
  isOrderPreserving M N f × isOrderPreserving N M g
  where
    g = equivFun (invEquiv e)
```

`Order` coupled with `isAnOrdePreservingEqv` gives us an SNS.

```agda
Order-is-SNS : SNS {ℓ} (Order ℓ₁) isAnOrderPreservingEqv
Order-is-SNS {ℓ = ℓ} {ℓ₁ = ℓ₁} {X = X}  _⊑₀_ _⊑₁_ = f , record { equiv-proof = f-equiv }
  where
    f : isAnOrderPreservingEqv (X , _⊑₀_) (X , _⊑₁_) (idEquiv X) → _⊑₀_ ≡ _⊑₁_
    f e@(φ , ψ) = funExt₂ λ x y → ⇔toPath (φ x y) (ψ x y)

    g : _⊑₀_ ≡ _⊑₁_ → isAnOrderPreservingEqv (X , _⊑₀_) (X , _⊑₁_) (idEquiv X)
    g p =
      subst
        (λ _⊑_ → isAnOrderPreservingEqv (X , _⊑₀_) (X , _⊑_) (idEquiv X))
        p
        ((λ _ _ x⊑₁y → x⊑₁y) , λ _ _ x⊑₁y → x⊑₁y)

    ret-f-g : retract f g
    ret-f-g (φ , ψ) =
      isPropΣ
        (isOrderPreserving-prop (X , _⊑₀_) (X , _⊑₁_) (id X))
        (λ _ → isOrderPreserving-prop (X , _⊑₁_) (X , _⊑₀_) (id X))
        (g (f (φ , ψ))) (φ , ψ)

    f-equiv : (p : _⊑₀_ ≡ _⊑₁_) → isContr (fiber f p)
    f-equiv p = ((to , from) , eq) , NTS
      where
        to : isOrderPreserving (X , _⊑₀_) (X , _⊑₁_) (id _)
        to x y = subst (λ _⊑_ → [ x ⊑₀ y ] → [ x ⊑ y ]) p (id _)

        from : isOrderPreserving (X , _⊑₁_) (X , _⊑₀_) (id _)
        from x y = subst (λ _⊑_ → [ x ⊑ y ] → [ x ⊑₀ y ]) p (id _)

        eq : f (to , from) ≡ p
        eq = Order-set ℓ₁ X _⊑₀_ _⊑₁_ (f (to , from)) p

        NTS : (fib : fiber f p) → ((to , from) , eq) ≡ fib
        NTS ((φ , ψ) , eq) =
          Σ≡Prop
            (λ i′ → isOfHLevelSuc 2 (Order-set ℓ₁ X) _⊑₀_ _⊑₁_ (f i′) p)
            (Σ≡Prop
               (λ _ → isOrderPreserving-prop (X , _⊑₁_) (X , _⊑₀_) (id _))
               (isOrderPreserving-prop (X , _⊑₀_) (X , _⊑₁_) (id _) to φ))
```

This is the substantial part of the work required to establish univalence for posets.
Adding partial order axioms on top of this is not too hard.

First, let us define what is means for a type equivalence to be monotonic.

```agda
isAMonotonicEqv : (P Q : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ ≃ ∣ Q ∣ₚ → Type _
isAMonotonicEqv (A , (_⊑₀_ , _)) (B , (_⊑₁_ , _)) =
  isAnOrderPreservingEqv (A , _⊑₀_) (B , _⊑₁_)

isAMonotonicEqv-prop : (P Q : Poset ℓ₀ ℓ₁) (eqv : ∣ P ∣ₚ ≃ ∣ Q ∣ₚ)
                     → isProp (isAMonotonicEqv P Q eqv)
isAMonotonicEqv-prop P Q e@(f , _) =
  isPropΣ (isMonotonic-prop P Q f) λ _ → isMonotonic-prop Q P g
  where
    g = equivFun (invEquiv e)
```

We denote by `_≃ₚ_` the type of monotonic poset equivalences.

```agda
_≃ₚ_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Type _
_≃ₚ_ P Q = Σ[ i ∈ ∣ P ∣ₚ ≃ ∣ Q ∣ₚ ] isAMonotonicEqv P Q i
```

From this, we can already establish that posets form an SNS and prove that the category
of posets is univalent.

```agda
poset-is-SNS : SNS {ℓ} (PosetStr ℓ₁) isAMonotonicEqv
poset-is-SNS {ℓ₁ = ℓ₁} =
  UnivalentStr→SNS (PosetStr ℓ₁) isAMonotonicEqv poset-forms-univalent-str
  where
    NTS : (A : Type ℓ) (_⊑_ : Order ℓ₁ A) → isProp [ PosetAx A _⊑_ ]
    NTS A _⊑_ = isProp[] (PosetAx A _⊑_)

    poset-forms-univalent-str : UnivalentStr (PosetStr ℓ₁) isAMonotonicEqv
    poset-forms-univalent-str =
      axiomsUnivalentStr _ NTS (SNS→UnivalentStr isAnOrderPreservingEqv Order-is-SNS)

poset-univ₀ : (P Q : Poset ℓ₀ ℓ₁) → (P ≃ₚ Q) ≃ (P ≡ Q)
poset-univ₀ = SIP (SNS→UnivalentStr isAMonotonicEqv poset-is-SNS)
```

This result is almost what we want but it is better talk directly about poset
_isomorphisms_ rather than equivalences. In the case when types `A` and `B` are sets, the
type of isomorphisms between `A` and `B` is equivalent to the type of equivalences betwee
them.

Let us start by writing down what a poset isomorphisms is.

```agda
isPosetIso : (P Q : Poset ℓ₀ ℓ₁) → (P ─m→ Q) → Type _
isPosetIso P Q (f , _) = Σ[ (g , _) ∈ (Q ─m→ P) ] section f g × retract f g

isPosetIso-prop : (P Q : Poset ℓ₀ ℓ₁) (f : P ─m→ Q)
                → isProp (isPosetIso P Q f)
isPosetIso-prop P Q (f , f-mono) (g₀ , sec₀ , ret₀) (g₁ , sec₁ , ret₁) =
  Σ≡Prop NTS g₀=g₁
  where
    NTS : ((g , _) : Q ─m→ P) → isProp (section f g × retract f g)
    NTS (g , g-mono) = isPropΣ
                         (isPropΠ λ x → carrier-is-set Q (f (g x)) x) λ _ →
                          isPropΠ λ x → carrier-is-set P (g (f x)) x

    g₀=g₁ : g₀ ≡ g₁
    g₀=g₁ =
      forget-mono Q P g₀ g₁ (funExt λ x →
        π₀ g₀ x             ≡⟨ sym (cong (λ - → π₀ g₀ -) (sec₁ x)) ⟩
        π₀ g₀ (f (π₀ g₁ x)) ≡⟨ ret₀ (π₀ g₁ x) ⟩
        π₀ g₁ x             ∎)
```

We will denote by `P ≅ₚ Q` the type of isomorphisms between posets `P` and `Q`.

```agda
_≅ₚ_ : Poset ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁ → Type _
P ≅ₚ Q = Σ[ f ∈ P ─m→ Q ] isPosetIso P Q f
```

As we have mentioned before, `P ≅ₚ Q` is equivalent to `P ≃ₚ Q`.

```agda
≃ₚ≃≅ₚ : (P Q : Poset ℓ₀ ℓ₁) → (P ≅ₚ Q) ≃ (P ≃ₚ Q)
≃ₚ≃≅ₚ P Q = isoToEquiv (iso from to ret sec)
  where
    to : P ≃ₚ Q → P ≅ₚ Q
    to (e@(f , _) , (f-mono , g-mono)) = (f , f-mono) , (g , g-mono) , sec-f-g , ret-f-g
      where
        is = equivToIso e
        g  = equivFun (invEquiv e)

        sec-f-g : section f g
        sec-f-g = Iso.rightInv (equivToIso e)

        ret-f-g : retract f g
        ret-f-g = Iso.leftInv (equivToIso e)

    from : P ≅ₚ Q → P ≃ₚ Q
    from ((f , f-mono) , ((g , g-mono) , sec , ret)) = isoToEquiv is , f-mono , g-mono
      where
        is : Iso ∣ P ∣ₚ ∣ Q ∣ₚ
        is = iso f g sec ret

    sec : section to from
    sec (f , _) = Σ≡Prop (isPosetIso-prop P Q) refl

    ret : retract to from
    ret (e , _) = Σ≡Prop (isAMonotonicEqv-prop P Q) (Σ≡Prop isPropIsEquiv refl)
```

Once this equivalence has been established, the main result follows easily: *the category
of posets is univalent*.

```agda
poset-univ : (P Q : Poset ℓ₀ ℓ₁) → (P ≅ₚ Q) ≃ (P ≡ Q)
poset-univ P Q = P ≅ₚ Q ≃⟨ ≃ₚ≃≅ₚ P Q ⟩ P ≃ₚ Q ≃⟨ poset-univ₀ P Q ⟩ P ≡ Q 𝔔𝔈𝔇
```
