---
title: Kuratowski Finiteness
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

module KuratowskiFinite where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Fin renaming (Fin to Fin′)
open import Cubical.Data.Nat
open import Cubical.Data.Empty using (rec)
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr; _⊎_)
open import Cubical.Data.Sum using (isSetSum)
open import Cubical.Foundations.Logic hiding (inl; inr) renaming (ℙ to ℙ′; powersets-are-sets to isSetℙ′)
open import Cubical.Foundations.Isomorphism using (isoToPath; iso; section; retract; Iso)
open import Cubical.Foundations.Equiv       using (equivToIso)
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Basis using (bot; ∥_∥; ∥∥-rec; ∥∥-prop; ∣_∣; ∥∥-×)

private
  variable
    ℓ ℓ₀ ℓ₁ : Level
```
-->

## Preliminaries ##

`ψ ℓ` denotes the type of h-set at level `ℓ`. Given an h-set `A`, we denote by
`⟦ A ⟧` its underlying type and by `isSet⟦⟧ A` the proof that is is an h-set.

```agda
Ψ : (ℓ : Level) → Type (ℓ-suc ℓ)
Ψ ℓ = Σ[ A ∈ Type ℓ ] isSet A

⟦_⟧ : Ψ ℓ → Type ℓ
⟦ A , _ ⟧ = A

isSet⟦⟧ : (A : Ψ ℓ) → isSet (fst A)
isSet⟦⟧ (_ , A-set) = A-set
```

For convenience, we define some new versions of operators that work on
inhabitants of `Ψ` directly.

```agda
_⊍_ : Ψ ℓ₀ → Ψ ℓ₁ → Ψ (ℓ-max ℓ₀ ℓ₁)
A ⊍ B = (⟦ A ⟧ ⊎ ⟦ B ⟧) , isSetSum (isSet⟦⟧ A) (isSet⟦⟧ B)

ℙ : Ψ ℓ → Type (ℓ-suc ℓ)
ℙ (A , _) = ℙ′ A

Fin : ℕ → Ψ ℓ-zero
Fin n = Fin′ n , isSetFin

𝟎 : ⟦ Fin 1 ⟧
𝟎 = 0 , (0 , refl)
```

Definition of surjectivity.

```agda
isSurjective : (A : Ψ ℓ₀) (B : Ψ ℓ₁) → (⟦ A ⟧ → ⟦ B ⟧) → hProp (ℓ-max ℓ₀ ℓ₁)
isSurjective A B f = ((y : ⟦ B ⟧) → ∥ Σ[ x ∈ ⟦ A ⟧ ] f x ≡ y ∥) , is-prop
  where
    is-prop : isProp ((y : ⟦ B ⟧) → ∥ Σ[ x ∈ ⟦ A ⟧ ] f x ≡ y ∥)
    is-prop = isPropΠ λ y → ∥∥-prop (Σ[ x ∈ ⟦ A ⟧ ] f x ≡ y)
```

As we will talk about *subsets* i.e. subsets of inhabitants of a type that
satisfy a certain predicate, we write down a convenient notation for it.

```agda
_restricted-to_ : (A : Ψ ℓ) → ℙ A → Ψ ℓ
_restricted-to_ {ℓ} (A , A-set) U = (Σ[ x ∈ A ] [ U x ]) , is-set where
    is-set : isSet (Σ[ x ∈ A ] [ U x ])
    is-set = isSetΣ A-set (isProp→isSet ∘ isProp[] ∘ U)
```

`A ↠ B` denotes the type of surjections from `A` to `B`.

```agda
_↠_ : Ψ ℓ₀ → Ψ ℓ₁ → Ψ (ℓ-max ℓ₀ ℓ₁)
A ↠ B = (Σ[ f ∈ (⟦ A ⟧ → ⟦ B ⟧) ] [ isSurjective A B f ]) , ↠-set
  where
    ↠-set : isSet (Σ[ f ∈ (⟦ A ⟧ → ⟦ B ⟧) ] [ isSurjective A B f ])
    ↠-set = isSetΣ (isSetΠ (λ _ → isSet⟦⟧ B)) λ f →
              isProp→isSet (isProp[] (isSurjective A B f))
```

A more suggestive notation for the underlying function of an inhabitant of `A ↠
B`.

```agda
_$_ = fst
```

## Definition of Kuratowski-finiteness ##

Our definition of [Kuratowski-finite][0] set `A` is: there exists a surjection
from `Fin n` (for some `n`) to `A`:

```agda
isKFin : (A : Ψ ℓ) → ℙ A → hProp ℓ
isKFin A U =
  ∥ Σ[ n ∈ ℕ ] ⟦ Fin n ↠ (A restricted-to U) ⟧ ∥ , ∥∥-prop _

isKFin-set : (A : Ψ ℓ) → (U : ℙ A) → isSet [ isKFin A U ]
isKFin-set A U = isProp→isSet (isProp[] (isKFin A U))
```

The h-set of Kuratowski-finite sets is defined as:

```agda
KFin : Ψ ℓ → Ψ (ℓ-suc ℓ)
KFin A = (Σ[ U ∈ ℙ A ] [ isKFin A U ]) , is-set
  where
    is-set : isSet (Σ[ U ∈ ℙ A ] [ isKFin A U ])
    is-set = isSetΣ isSetℙ′ (isKFin-set A)
```

The following is nothing but a convenient notation for the irrelevance
of Kuratowski-finiteness proof to the equality.

```agda
KFin-eq : (A : Ψ ℓ) → (U V : ⟦ KFin A ⟧) → fst U ≡ fst V → U ≡ V
KFin-eq A U V U=V = Σ≡Prop (isProp[] ∘ isKFin A) U=V
```

## Operations on Kuratowski-finite sets ##

In this section, we assume a fixed h-set `A`.

```agda
module _ (A : Ψ ℓ) where
```

### The empty Kuratowski-finite set ###

```agda
  ∅ : ⟦ KFin A ⟧
  ∅ = (λ _ → bot ℓ) , ∣ 0 , f ∣
    where
      f : ⟦ Fin 0 ↠ (A restricted-to (λ x → bot ℓ)) ⟧
      f  = (λ { (_ , n<0) → rec (¬-<-zero n<0) }) , λ ()

  ∅-uninhabited : ⟦ A restricted-to fst ∅ ⟧ → [ ⊥ ]
  ∅-uninhabited (_ , ())
```

### Singleton Kuratowski-finite set ###

```agda
  single : ⟦ A ⟧ → ℙ A
  single x = λ y → (x ≡ y) , isSet⟦⟧ A x y

  η : ⟦ A ⟧ → ⟦ KFin A ⟧
  η x =  single x , ∣ 1 , f ∣
    where
      ⁅x⁆ : Ψ ℓ
      ⁅x⁆ = A restricted-to (single x)

      f : ⟦ Fin 1 ↠ ⁅x⁆ ⟧
      f = (λ _ → x , refl) , surj
        where
          surj : [ isSurjective (Fin 1) ⁅x⁆ (λ _ → x , refl) ]
          surj (y , p) = ∣ 𝟎 , Σ≡Prop (isProp[] ∘ single x) p ∣
```

### Union of two Kuratowski-finite sets ###

Some arithmetic lemmata. It is likely that these have either been proven in
`cubical` or can be proven more efficiently using other lemmata that have been
proven in `cubical`. If you have any suggestions please make a PR.

```agda
o<m→o<m+n : (m n o : ℕ) → o < m → o < (m + n)
o<m→o<m+n m n o (k , p) =
  (n + k) , (n + k + suc o    ≡⟨ sym (+-assoc n k _)  ⟩
              n + (k + suc o)  ≡⟨ cong (λ - → n + -) p ⟩
              n + m            ≡⟨ +-comm n m           ⟩
              m + n            ∎)
```

```agda
main-lemma : (m n o : ℕ) → o < m + n → m ≤ o → (o ∸ m) < n
main-lemma zero    n o       o<m+n m<o = o<m+n
main-lemma (suc m) n zero    o<m+n m<o = rec (¬-<-zero m<o)
main-lemma (suc m) n (suc o) o<m+n m<o =
  main-lemma m n o (pred-≤-pred o<m+n) (pred-≤-pred m<o)
```

```agda
≤-refl′ : {m n : ℕ} → m ≡ n → m ≤ n
≤-refl′ {m} {n} m=n = subst (λ - → m ≤ -) m=n ≤-refl
```

We will often be interested in whether `m < n` or not.

```agda
_≤?_ : (m n : ℕ) → (m < n) ⊎ (n ≤ m)
_≤?_ m n with m ≟ n
(m ≤? n) | lt m<n = inl m<n
(m ≤? n) | eq m=n = inr (≤-refl′ (sym m=n))
(m ≤? n) | gt n<m = inr (<-weaken n<m)

¬-<-and-≥ : {m n : ℕ} → m < n → n ≤ m → [ ⊥ ]
¬-<-and-≥ {m} {zero}    m<n n≤m = ¬-<-zero m<n
¬-<-and-≥ {zero} {suc n} m<n n≤m = ¬-<-zero n≤m
¬-<-and-≥ {suc m} {suc n} m<n n≤m =
  ¬-<-and-≥ (pred-≤-pred m<n) (pred-≤-pred n≤m)
```

I'm a bit surprised this one isn't already in `cubical`.

```agda
m+n∸n=m : (n m : ℕ) → (m + n) ∸ n ≡ m
m+n∸n=m zero    k = +-zero k
m+n∸n=m (suc m) k =
  (k + suc m) ∸ suc m   ≡⟨ cong (λ - → - ∸ suc m) (+-suc k m) ⟩
  suc (k + m) ∸ (suc m) ≡⟨ refl                               ⟩
  (k + m) ∸ m           ≡⟨ m+n∸n=m m k                        ⟩
  k                     ∎
```

It's quite hard to come up with a descriptive name for this one...

```agda
∸-lemma : {m n : ℕ} → m ≤ n → m + (n ∸ m) ≡ n
∸-lemma {zero}  {k}     _   = refl {x = k}
∸-lemma {suc m} {zero}  m≤k = rec (¬-<-and-≥ (suc-≤-suc zero-≤) m≤k)
∸-lemma {suc m} {suc k} m≤k =
  suc m + (suc k ∸ suc m)   ≡⟨ refl                                 ⟩
  suc (m + (suc k ∸ suc m)) ≡⟨ refl                                 ⟩
  suc (m + (k ∸ m))         ≡⟨ cong suc (∸-lemma (pred-≤-pred m≤k)) ⟩
  suc k                     ∎
```


```agda
Fin+≃Fin⊎Fin : (m n : ℕ) → ⟦ Fin (m + n) ⟧ ≡ ⟦ Fin m ⟧ ⊎ ⟦ Fin n ⟧
Fin+≃Fin⊎Fin m n = isoToPath (iso f g sec-f-g ret-f-g)
  where
    f : ⟦ Fin (m + n) ⟧ → ⟦ Fin m ⟧ ⊎ ⟦ Fin n ⟧
    f (k , k<m+n) with k ≤? m
    f (k , k<m+n) | inl k<m = inl (k , k<m)
    f (k , k<m+n) | inr k≥m = inr (k ∸ m , main-lemma m n k k<m+n k≥m)

    g : ⟦ Fin m ⟧ ⊎ ⟦ Fin n ⟧ → ⟦ Fin (m + n) ⟧
    g (inl (k , k<m)) = k     , o<m→o<m+n m n k k<m
    g (inr (k , k<n)) = m + k , <-k+ k<n

    sec-f-g : section f g
    sec-f-g (inl (k , k<m))
        with k ≤? m
    ... | inl _   = cong inl (Σ≡Prop (λ _ → m≤n-isProp) refl)
    ... | inr m≤k = rec (¬-<-and-≥ k<m m≤k)
    sec-f-g (inr (k , k<n))
        with (m + k) ≤? m
    ... | inl p   = rec (¬m+n<m {m} {k} p)
    ... | inr k≥m = cong inr (Σ≡Prop (λ _ → m≤n-isProp) NTS)
      where
        NTS : (m + k) ∸ m ≡ k
        NTS = subst (λ - → - ∸ m ≡ k) (sym (+-comm m k)) (m+n∸n=m m k)

    ret-f-g : retract f g
    ret-f-g (k , k<m+n) with k ≤? m
    ret-f-g (k , k<m+n) | inl _   = Σ≡Prop (λ _ → m≤n-isProp) refl
    ret-f-g (k , k<m+n) | inr m≥k = Σ≡Prop (λ _ → m≤n-isProp) (∸-lemma m≥k)

Fin-sum-lemma′ : (m n : ℕ) → Fin (m + n) ≡ (Fin m) ⊍ (Fin n)
Fin-sum-lemma′ m n = Σ≡Prop (λ A → isPropIsSet {A = A}) (Fin+≃Fin⊎Fin m n)
```

Let us first define the union of two subsets.

```agda
module _ (A : Ψ ℓ) where

  _∪ℙ_ : ℙ A → ℙ A → ℙ A
  _∪ℙ_ U V = λ x → ∥ (x ∈ U) ⊎ (x ∈ V) ∥ , ∥∥-prop _

  _∪_ : ⟦ KFin A ⟧ → ⟦ KFin A ⟧ → ⟦ KFin A ⟧
  _∪_ (U , U-kfin) (V , V-kfin) =
    (U ∪ℙ V) , ∥∥-rec (isProp[] (isKFin A (U ∪ℙ V))) NTS (∥∥-× U-kfin V-kfin)
    where
      NTS : (Σ[ m ∈ ℕ ] ⟦ Fin m ↠ (A restricted-to U) ⟧)
          × (Σ[ n ∈ ℕ ] ⟦ Fin n ↠ (A restricted-to V) ⟧)
          → [ isKFin A (U ∪ℙ V) ]
      NTS ((m , f) , (n , g)) = ∣ (m + n) , Fin-m+n↠U ∣
        where
          f-surj = snd f
          g-surj = snd g

          h : ⟦ Fin m ⊍ Fin n ⟧ → ⟦ A restricted-to (U ∪ℙ V) ⟧
          h (inl (k , k<m)) = let (x , x∈U) = f $ (k , k<m) in x , ∣ inl x∈U ∣
          h (inr (k , k<n)) = let (y , y∈V) = g $ (k , k<n) in y , ∣ inr y∈V ∣

          h-surj : [ isSurjective (Fin m ⊍ Fin n) (A restricted-to (U ∪ℙ V)) h ]
          h-surj (x , ∣x∈U∪V∣) =
            ∥∥-rec (∥∥-prop (Σ[ _ ∈ _ ] _)) rem ∣x∈U∪V∣
            where
              rem : (x ∈ U) ⊎ (x ∈ V)
                  → ∥ Σ[ k ∈ ⟦ Fin m ⊍ Fin n ⟧ ] h k ≡ (x , ∣x∈U∪V∣) ∥
              rem (inl x∈U) =
                ∥∥-rec (∥∥-prop (Σ[ _ ∈ _ ] _)) rem′ (f-surj (x , x∈U))
                where
                  rem′ : _
                  rem′ (k , fk=x) =
                    ∣ inl k , Σ≡Prop (isProp[] ∘ U ∪ℙ V) (λ i → fst (fk=x i)) ∣
              rem (inr x∈V) =
                ∥∥-rec (∥∥-prop (Σ-syntax _ _)) rem′ (g-surj (x , x∈V))
                where
                  rem′ : _
                  rem′ (k , gk=x) =
                    ∣ inr k , Σ≡Prop (isProp[] ∘ U ∪ℙ V) (λ i → fst (gk=x i)) ∣

          Fin-m+n↠U : ⟦ Fin (m + n) ↠ (A restricted-to (U ∪ℙ V)) ⟧
          Fin-m+n↠U =
             subst
               (λ - → ⟦ - ↠ (A restricted-to (U ∪ℙ V)) ⟧)
               (sym (Fin-sum-lemma′ m n))
               (h , h-surj)
```


```agda
{--
KFin1→isContr : (A : Ψ ℓ) → ⟦ Fin 1 ↠ A ⟧ → isContr ⟦ A ⟧
KFin1→isContr A (f , f-surj) = f centre , NTS
  where
    centre = fst isContrFin1

    NTS : (y : ⟦ A ⟧) → f centre ≡ y
    NTS y = f centre           ≡⟨ cong f (snd isContrFin1 (fst (f-surj y))) ⟩
            f (fst (f-surj y)) ≡⟨ snd (f-surj y) ⟩
            y                  ∎

KFin1-lemma : (A : Ψ ℓ) → (f : ⟦ Fin 1 ↠ A ⟧) → (x : ⟦ A ⟧) → x ≡ f $ 𝟎
KFin1-lemma A f x = x ≡⟨ sym (contr x) ⟩ centre ≡⟨ contr centre ⟩ f $ 𝟎 ∎
  where
    centre = fst (KFin1→isContr A f)
    contr  = snd (KFin1→isContr A f)

lemma1 : (A : Ψ ℓ) (U : ℙ A)
       → ⟦ Fin 1 ↠ (A restricted-to U) ⟧
       → Σ[ y ∈ fst A ] U ≡ fst (η A y)
lemma1 A U f =
  fst (f $ 𝟎) , ⊆-extensionality U (single A (fst (f $ 𝟎))) (down , up)
  where
    U-contr : isContr ⟦ A restricted-to U ⟧
    U-contr = KFin1→isContr (A restricted-to U) f

    centre = fst U-contr

    down : U ⊆ single A (fst (f $ 𝟎))
    down x x∈U =
      fst (PathΣ→ΣPathTransport _ _ (sym (KFin1-lemma (A restricted-to U) f (x , x∈U))))

    up : single A (fst (f $ 𝟎)) ⊆ U
    up x p = subst ([_] ∘ U) p (snd (f $ 𝟎))

lemma2 : (A : Ψ ℓ) → (U : ⟦ KFin A ⟧)
       → (f : ⟦ Fin 1 ↠ (A restricted-to (fst U)) ⟧)
       → U ≡ η A (fst (f $ 𝟎))
lemma2 A U f = KFin-eq A U (η A _) (snd (lemma1 A (fst U) f))


lemma3 : (A : Ψ ℓ) → (U : ⟦ KFin A ⟧)
       → (f : ⟦ Fin 0 ↠ (A restricted-to (fst U)) ⟧)
       → U ≡ ∅ A
lemma3 A U f =
  KFin-eq A U (∅ A) (⊆-extensionality (fst U) (fst (∅ A)) (NTS₀ , NTS₁))
  where
    NTS₀ : fst U ⊆ fst (∅ A)
    NTS₀ x x∈U = rec (¬Fin0 (fst (snd f (x , x∈U))))

    NTS₁ : fst (∅ A) ⊆ fst U
    NTS₁ x x∈∅ = rec (∅-uninhabited A (x , x∈∅))

-- K-ind : (A : Ψ ℓ) (P : ℙ (KFin A))
--       → [ P (∅ A) ]
--       → ((x : fst A) → [ P (η A x) ])
--       → [ ∀[ U ∶ ⟦ KFin A ⟧ ] ∀[ V ∶ ⟦ KFin A ⟧ ] (P U ⇒ P V ⇒ P {!U ∪ V!}) ]
--       → (U : ⟦ KFin A ⟧) → [ P U ]
-- K-ind A P ε σ ι (U , p) = ∥∥-rec (isProp[] (P (U , p))) (uncurry NTS) p
--   where
--     NTS : (n : ℕ) → ⟦ Fin n ↠ (A restricted-to U) ⟧ → [ P (U , p) ]
--     NTS zero          f = subst (λ - → [ P - ])  (sym (lemma3 A (U , p) f)) ε
--     NTS 1             f = subst (λ - → [ P - ]) (sym (lemma2 A (U , p) f) ) (σ (fst (f $ 𝟎)))
--     NTS (suc (suc n)) f = {!!}

-- --}
-- --}
```

[0]: https://ncatlab.org/nlab/show/finite+set#Constructivist
