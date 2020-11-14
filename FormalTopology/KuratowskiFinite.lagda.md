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
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Fin
              renaming (Fin to Fin′)
open import Cubical.Data.Empty
              using (rec)
open import Cubical.Data.Sum
              using (inl; inr; _⊎_)
open import Cubical.Data.Sum
              using (isSetSum)
open import Cubical.Foundations.Structure
              using    ()
              renaming (⟨_⟩ to [_])
open import Cubical.Functions.Logic
              renaming (isProp⟨⟩ to isProp[])
              hiding   (inl; inr)
open import Cubical.Foundations.Powerset
              using (_∈_; _⊆_; ⊆-extensionality; ⊆-isProp; ⊆-refl)
              renaming (ℙ to ℙ′; powersets-are-sets to isSetℙ′)
open import Cubical.Foundations.Isomorphism
              using (isoToPath; iso; section; retract; Iso)
open import Cubical.Foundations.Equiv
              using (equivToIso)
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Poset
open import Basis
              using (bot; ∥_∥; ∥∥-rec; ∥∥-prop; ∣_∣; ∥∥-×; fmap; compr-∶-syntax; fiber)

private
  variable
    ℓ ℓ₀ ℓ₁ ℓ′ ℓ₀′ ℓ₁′ : Level
```
-->

# Preliminaries #

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
_restricted-to_ : (A : Ψ ℓ) → (⟦ A ⟧ → hProp ℓ′) → Ψ (ℓ-max ℓ ℓ′)
_restricted-to_ (A , A-set) U = (Σ[ x ∈ A ] [ U x ]) , is-set
  where
    is-set : isSet (Σ[ x ∈ A ] [ U x ])
    is-set = isSetΣ A-set (isProp→isSet ∘ isProp[] ∘ U)
```

`A ↠ B` denotes the type of surjections from `A` to `B`.

```agda
_↠_ : Ψ ℓ₀ → Ψ ℓ₁ → Ψ (ℓ-max ℓ₀ ℓ₁)
A ↠ B = (Σ[ f ∈ (⟦ A ⟧ → ⟦ B ⟧) ] [ isSurjective A B f ]) , ↠-set
  where
    ↠-set : isSet (Σ[ f ∈ (⟦ A ⟧ → ⟦ B ⟧) ] [ isSurjective A B f ])
    ↠-set = isSetΣ
              (isSetΠ (λ _ → isSet⟦⟧ B))
              (isProp→isSet ∘ isProp[] ∘ isSurjective A B)
```

A more suggestive notation for the underlying function of an inhabitant of `A ↠
B`.

```agda
_$_ = fst
```

# Definition of Kuratowski-finiteness #

Our definition of [Kuratowski-finite][0] set `A` is: there exists a surjection
from `Fin n` (for some `n`) to `A`:

```agda
isKFin : (A : Ψ ℓ) → (⟦ A ⟧ → hProp ℓ′) → hProp (ℓ-max ℓ ℓ′)
isKFin A U =
  ∥ Σ[ n ∈ ℕ ] ⟦ Fin n ↠ (A restricted-to U) ⟧ ∥ , ∥∥-prop _

isKFin-set : (A : Ψ ℓ) → (U : ⟦ A ⟧ → hProp ℓ′) → isSet [ isKFin A U ]
isKFin-set A U = isProp→isSet (isProp[] (isKFin A U))
```

The h-set of Kuratowski-finite sets is defined as:

```agda
KFin : (ℓ′ : Level) → Ψ ℓ → Ψ (ℓ-max ℓ (ℓ-suc ℓ′))
KFin ℓ′ A = (Σ[ U ∈ (⟦ A ⟧ → hProp ℓ′) ] [ isKFin A U ]) , is-set
  where
    is-set : isSet (Σ[ U ∈ (⟦ A ⟧ → hProp ℓ′) ] [ isKFin A U ])
    is-set = isSetΣ (isSetΠ λ x → isSetHProp) λ U → isProp→isSet (isProp[] (isKFin A U))
```

The following is nothing but a convenient notation for the irrelevance
of Kuratowski-finiteness proof to the equality.

```agda
KFin-eq : (A : Ψ ℓ) → (U V : ⟦ KFin ℓ′ A ⟧) → fst U ≡ fst V → U ≡ V
KFin-eq A U V U=V = Σ≡Prop (isProp[] ∘ isKFin A) U=V
```

# Operations on Kuratowski-finite sets #

In this section, we assume a fixed h-set `A`.

```agda
module _ (A : Ψ ℓ) where
```

## The empty Kuratowski-finite set ##

```agda
  ∅ : (ℓ′ : Level) → ⟦ KFin ℓ′ A ⟧
  ∅ ℓ′ = (λ _ → bot ℓ′) , ∣ 0 , f ∣
    where
      f : ⟦ Fin 0 ↠ (A restricted-to (λ x → bot ℓ′)) ⟧
      f  = (λ { (_ , n<0) → rec (¬-<-zero n<0) }) , λ ()

  ∅-uninhabited : ⟦ A restricted-to (fst (∅ ℓ′)) ⟧ → [ ⊥ ]
  ∅-uninhabited ()
```

## Singleton Kuratowski-finite set ##

```agda
  single : ⟦ A ⟧ → ℙ A
  single x = λ y → (x ≡ y) , isSet⟦⟧ A x y

  η : ⟦ A ⟧ → ⟦ KFin ℓ A ⟧
  η x =  single x , ∣ 1 , f ∣
    where
      ⁅x⁆ : Ψ ℓ
      ⁅x⁆ = A restricted-to (single x)

      f : ⟦ Fin 1 ↠ ⁅x⁆ ⟧
      f = (λ _ → x , refl) , surj
        where
          surj : [ isSurjective (Fin 1) ⁅x⁆ (λ _ → x , refl) ]
          surj (y , p) = ∣ 𝟎 , Σ≡Prop (isProp[] ∘ single x) p ∣

  η-inj : (x y : ⟦ A ⟧) → η x ≡ η y → x ≡ y
  η-inj x y ηx=ηy = y∈η-x
    where
      y∈η-x : y ∈ fst (η x)
      y∈η-x = subst (λ - → y ∈ fst -) (sym ηx=ηy) refl
```

## Union of two Kuratowski-finite sets ##

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

### `Fin (m + n) ≡ Fin m ⊎ Fin n` ###

The following fact is crucial for the definition of union for Kuratowski-finite
sets.

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

  _∪ℙ_ : (⟦ A ⟧ → hProp ℓ₀) → (⟦ A ⟧ → hProp ℓ₁) → ⟦ A ⟧ → hProp (ℓ-max ℓ₀ ℓ₁)
  _∪ℙ_ U V = λ x → ∥ [ U x ] ⊎ [ V x ] ∥ , ∥∥-prop ([ U x ] ⊎ [ V x ])

  _∪_ : ⟦ KFin ℓ₀ A ⟧ → ⟦ KFin ℓ₁ A ⟧ → ⟦ KFin (ℓ-max ℓ₀ ℓ₁) A ⟧
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
              rem : [ U x ] ⊎ [ V x ] → ∥ Σ[ k ∈ ⟦ Fin m ⊍ Fin n ⟧ ] h k ≡ (x , ∣x∈U∪V∣) ∥
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

# Induction principle of Kuratowski-finite sets #

We prove in this section the induction principle of Kuratowski-finite sets:

to show that _all_ Kuratowski-finite sets satisfy some predicate $P$, it
suffices to show

  1. $∅$ satisfies P;
  2. $\left\{ x \right\}$ satisfies $P$, for every $x$; and
  3. given two Kuratowski-finite sets $U$ and $V$ satisfying $P$,
     the union $U ∪ V$ satisfies $P$.

The proof of this induction principle is given at the very end of this section.

If a surjection exists from `Fin 1` to `A`, `A` is contractible.

```agda
  KFin1→isContr : ⟦ Fin 1 ↠ A ⟧ → isContr ⟦ A ⟧
  KFin1→isContr (f , f-surj) =
    f centre , λ y → ∥∥-rec (isSet⟦⟧ A (f centre) y) (nts y) (f-surj y)
    where
      centre = fst isContrFin1
      shrink = snd isContrFin1

      nts : (y : ⟦ A ⟧) → Σ[ i ∈ ⟦ Fin 1 ⟧ ] (f i ≡ y) → f centre ≡ y
      nts y (i , fi=y)= f centre ≡⟨ cong f (shrink i) ⟩ f i ≡⟨ fi=y ⟩ y ∎

  KFin1-lemma : (f : ⟦ Fin 1 ↠ A ⟧) → (x : ⟦ A ⟧) → x ≡ f $ 𝟎
  KFin1-lemma f x = x ≡⟨ sym (contr x) ⟩ centre ≡⟨ contr centre ⟩ f $ 𝟎 ∎
    where
      centre = fst (KFin1→isContr f)
      contr  = snd (KFin1→isContr f)
```

Some more lemmata we will need.

```agda
module _ (A : Ψ ℓ) where

  lemma1 : (U : ⟦ A ⟧ → hProp ℓ)
        → ⟦ Fin 1 ↠ (A restricted-to U) ⟧
        → Σ[ y ∈ ⟦ A ⟧ ] U ≡ fst (η A y)
  lemma1 U f =
    fst (f $ 𝟎) , ⊆-extensionality U (single A (fst (f $ 𝟎))) (down , up)
    where
      U-contr : isContr ⟦ A restricted-to U ⟧
      U-contr = KFin1→isContr (A restricted-to U) f

      centre = fst U-contr

      down : U ⊆ single A (fst (f $ 𝟎))
      down x x∈U = λ i → fst (KFin1-lemma (A restricted-to U) f (x , x∈U) (~ i))

      up : single A (fst (f $ 𝟎)) ⊆ U
      up x p = subst ([_] ∘ U) p (snd (f $ 𝟎))

  lemma2 : (U : ⟦ KFin ℓ A ⟧)
         → (f : ⟦ Fin 1 ↠ (A restricted-to (fst U)) ⟧)
         → U ≡ η A (fst (f $ 𝟎))
  lemma2 U f = KFin-eq A U (η A _) (snd (lemma1 (fst U) f))

  lemma3 : (U : ⟦ KFin ℓ A ⟧)
         → (f : ⟦ Fin 0 ↠ (A restricted-to (fst U)) ⟧)
         → U ≡ ∅ A ℓ
  lemma3 U (f , f-surj) =
    KFin-eq A U (∅ A ℓ) (⊆-extensionality (fst U) (fst (∅ A ℓ)) (NTS₀ , NTS₁))
    where
      NTS₀ : fst U ⊆ fst (∅ A ℓ)
      NTS₀ x x∈U =
        ∥∥-rec (isProp[] (fst (∅ A ℓ) x)) (rec ∘ ¬Fin0 ∘ fst) (f-surj (x , x∈U))

      NTS₁ : fst (∅ A ℓ) ⊆ fst U
      NTS₁ x x∈∅ = rec (∅-uninhabited A (x , x∈∅))

  _+1 : {n : ℕ} → ⟦ Fin n ⟧ → ⟦ Fin (suc n) ⟧
  (k , k<n) +1 = k , suc-≤-suc (<-weaken k<n)

```

This is the real content of the proof which amounts taking a Kuratowski-finite
set $U$ of size `n ≥ 2` and decomposing it as $U = \{ x \} ∪ U′$.

```agda
  K-ind-lemma : (P : ⟦ KFin ℓ A ⟧ → hProp ℓ₁)
              → [ P (∅ A ℓ) ]
              → ((x : fst A) → [ P (η A x) ])
              → [ ∀[ U ∶ ⟦ KFin ℓ A ⟧ ] ∀[ V ∶ ⟦ KFin ℓ A ⟧ ] (P U ⇒ P V ⇒ P (_∪_ A U V)) ]
              → (U : ℙ A)
              → (n : ℕ)
              → (f : ⟦ Fin n ↠ (A restricted-to U) ⟧)
              → [ P (U , ∣ n , f  ∣) ]
  K-ind-lemma P ε σ ι U zero          f = subst (λ - → [ P - ])  (sym (lemma3 _ f)) ε
  K-ind-lemma P ε σ ι U (suc zero)    f = subst (λ - → [ P - ]) (sym (lemma2 _ f) ) (σ (fst (f $ 𝟎)))
  K-ind-lemma P ε σ ι U (suc (suc n)) f = subst (λ - → [ P - ]) (sym U=x∪U′) (ι (η A hd) U′ (σ hd) (K-ind-lemma P ε σ ι U′s (suc n) (h , h-surj) ))
    where
      U′s : ℙ A
      U′s x = ∥ Σ[ k ∈ ⟦ Fin (suc n) ⟧ ] fst (f $ (k +1)) ≡ x ∥ , ∥∥-prop _

      h : ⟦ Fin (suc n) ⟧ → ⟦ A restricted-to U′s ⟧
      h k = (fst (f $ (k +1))) , ∣ k , refl ∣

      h-surj : [ isSurjective (Fin (suc n)) (A restricted-to U′s) h ]
      h-surj (x , x∈U′) = ∥∥-rec (∥∥-prop (Σ[ _ ∈ _ ] _)) rem x∈U′
        where
          rem : _
          rem (k , fk=x) = ∣ k , Σ≡Prop (isProp[] ∘ U′s) fk=x ∣

      U′ : ⟦ KFin ℓ A ⟧
      U′ = U′s , ∣ suc n , h , h-surj ∣

      hd : ⟦ A ⟧
      hd = fst (f $ (suc n , ≤-refl))

      U⊆x∪U′ : U ⊆ fst (_∪_ A (η A hd) U′)
      U⊆x∪U′ x x∈U = ∥∥-rec (∥∥-prop _) rem (snd f (x , x∈U))
        where
          rem : Σ[ i ∈ ⟦ Fin (suc (suc n)) ⟧ ] f $ i ≡ (x , x∈U) → ∥ (x ∈ fst (η A hd)) ⊎ (x ∈ fst U′) ∥
          rem ((k , k<suc-suc-n) , fk=x) =
            case k ≟ suc n of λ
              { (lt k<suc-n) →
                  let
                    rem₀ : fst (f $ ((k , k<suc-n) +1)) ≡ x
                    rem₀ = fst (f $ ((k , k<suc-n) +1)) ≡⟨ cong (λ - → fst (f $ -)) (Σ≡Prop (λ _ → m≤n-isProp) refl) ⟩
                            fst (f $ (k , k<suc-suc-n))  ≡⟨ (λ i → fst (fk=x i)) ⟩
                            _ ∎
                  in
                    ∣ inr ∣ (k , k<suc-n) , rem₀ ∣ ∣
              ; (eq k=suc-n) →
                  let
                    fk=x    : fst (f $ (k , _)) ≡ x
                    fk=x    = fst (PathΣ→ΣPathTransport _ _ fk=x)
                    k=suc-n : (k , _) ≡ (suc n , _)
                    k=suc-n = (Σ≡Prop (λ _ → m≤n-isProp) k=suc-n)
                  in
                    ∣ inl (subst (λ - → fst (fst f -) ≡ x) k=suc-n fk=x) ∣
              ; (gt k>suc-n) → rec (¬-<-and-≥ k>suc-n (pred-≤-pred k<suc-suc-n))
              }

      x∪U′⊆U : fst (_∪_ A (η A hd) U′) ⊆ U
      x∪U′⊆U x p = ∥∥-rec (isProp[] (U x)) rem₀ p
        where
          rem₀ : (x ∈ fst (η A hd)) ⊎ (x ∈ fst U′) → [ U x ]
          rem₀ (inl x∈η-hd) = subst (λ - → [ U - ]) x∈η-hd (snd (f $ (suc n , ≤-refl)))
          rem₀ (inr x∈U′) = ∥∥-rec (isProp[] (U x)) rem₁ x∈U′
            where
              rem₁ : Σ[ k ∈ ⟦ Fin (suc n) ⟧ ] fst (f $ (k +1)) ≡ x → [ U x ]
              rem₁ (k , fk=x) = subst (λ - → [ U - ]) fk=x (snd (f $ (k +1)))

      U=x∪U′ : (U , ∣ suc (suc n) , f ∣) ≡ _∪_ A (η A hd) U′
      U=x∪U′ =
        Σ≡Prop (isProp[] ∘ isKFin A) (⊆-extensionality U _ (U⊆x∪U′ , x∪U′⊆U))
```

## The proof of the induction principle ##

```agda
K-ind : (A : Ψ ℓ)
      → (P : ⟦ KFin ℓ A ⟧ → hProp ℓ′)
      → [ P (∅ A ℓ) ]
      → ((x : fst A) → [ P (η A x) ])
      → [ ∀[ U ∶ ⟦ KFin ℓ A ⟧ ] ∀[ V ∶ ⟦ KFin ℓ A ⟧ ] (P U ⇒ P V ⇒ P (_∪_ A U V)) ]
      → (U : ⟦ KFin ℓ A ⟧) → [ P U ]
K-ind A P ε σ ι (U , p) =
  ∥∥-rec (isProp[] (P (U , p))) nts p
  where
    nts : Σ-syntax ℕ (λ n → ⟦ Fin n ↠ (A restricted-to U) ⟧) → [ P (U , p) ]
    nts (n , f) =
      subst
        (λ - → [ P - ])
        (Σ≡Prop (isProp[] ∘ isKFin A) refl) (K-ind-lemma A P ε σ ι U n f)
```

# `KFin A` is the free join-semilattice on `A` #

```agda
open import Semilattice
```

```agda
carrier-set : (A : JoinSemilattice ℓ₀ ℓ₁) → Ψ ℓ₀
carrier-set A = carrier , carrier-is-set pos
  where
    open JoinSemilatticeNotation A
```

```agda
isUB : (A : JoinSemilattice ℓ₀ ℓ₁) (u : ⟦ carrier-set A ⟧) → ⟦ KFin ℓ′ (carrier-set A) ⟧ → hProp (ℓ-max (ℓ-max ℓ₀ ℓ₁) ℓ′)
isUB A u (U , U-kfin) = ((x : ∣A∣) → [ U x ] → [ x ⊑[ pos ] u ]) , isUB-prop
  where
    open JoinSemilatticeNotation A renaming (carrier to ∣A∣)

    isUB-prop : isProp ((x : ∣A∣) → [ U x ] → [ x ⊑[ pos ] u ])
    isUB-prop = isPropΠ λ x → isPropΠ λ x∈U → isProp[] (x ⊑[ pos ] u)

isLeastSuch : (A : JoinSemilattice ℓ₀ ℓ₁) (u : ⟦ carrier-set A ⟧)
            → ⟦ KFin ℓ′ (carrier-set A) ⟧ → hProp (ℓ-max (ℓ-max ℓ₀ ℓ₁) ℓ′)
isLeastSuch A u (U , U-kfin) =
  ((z : ∣A∣) → [ isUB A z (U , U-kfin) ] → [ u ⊑[ pos ] z ]) , nts
  where
    open JoinSemilatticeNotation A renaming (carrier to ∣A∣)

    nts : isProp ((z : ∣A∣) → [ isUB A z (U , U-kfin) ] → [ u ⊑[ pos ] z ])
    nts = isPropΠ λ x → isPropΠ λ _ → isProp[] (u ⊑[ pos ] x)

hasAJoin′ : (A : JoinSemilattice ℓ₀ ℓ₁)
          → ⟦ KFin ℓ′ (carrier-set A) ⟧ → Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) ℓ′)
hasAJoin′ {ℓ₀ = ℓ₀} {ℓ₁} A U =
  Σ[ u ∈ ∣A∣ ] [ (isUB A u U) ⊓ (isLeastSuch A u U) ]
  where
    open JoinSemilatticeNotation A renaming (carrier to ∣A∣)

hasAJoin-prop : (A : JoinSemilattice ℓ₀ ℓ₁)
              → (U : ⟦ KFin ℓ′ (carrier-set A) ⟧) → isProp (hasAJoin′ A U)
hasAJoin-prop A U (u , u-ub , u-least) (v , v-ub , v-least) =
  Σ≡Prop (λ u → isProp[] (isUB A u U ⊓ isLeastSuch A u U)) u=v
  where
    open JoinSemilatticeNotation A renaming (pos to pos-A)

    u⊑v : [ u ⊑[ pos-A ] v ]
    u⊑v = u-least v v-ub

    v⊑u : [ v ⊑[ pos-A ] u ]
    v⊑u = v-least u u-ub

    u=v : u ≡ v
    u=v = ⊑[ pos-A ]-antisym u v u⊑v v⊑u

hasAJoin : (A : JoinSemilattice ℓ₀ ℓ₁)
         → (⟦ KFin ℓ′ (carrier-set A) ⟧) → hProp (ℓ-max (ℓ-max ℓ₀ ℓ₁) ℓ′)
hasAJoin A U = (hasAJoin′ A U) , (hasAJoin-prop A U)
```

```agda
KFin-has-join : (A : JoinSemilattice ℓ₀ ℓ₁) → (U : ⟦ KFin ℓ₀ (carrier-set A) ⟧) → [ hasAJoin A U ]
KFin-has-join {ℓ₀ = ℓ₀} A = K-ind (carrier-set A) (hasAJoin A) ⋁∅ ⋁-singleton union-⋁
  where
    open JoinSemilatticeNotation A renaming (pos to pos-A; carrier to ∣A∣; 𝟎 to 𝟎-A; _∨_ to _∨A_)
    open PosetReasoning pos-A

    ⋁∅ : [ hasAJoin A (∅ (carrier-set A) ℓ₀) ]
    ⋁∅ = 𝟎-A , ((λ _ ()) , λ z _ → 𝟎-bottom z)

    ⋁-singleton : (x : ∣A∣) → [ hasAJoin A (η (carrier-set A) x) ]
    ⋁-singleton x = x , ub , least
      where
        abstract
          ub : [ isUB A x (η (carrier-set A) x) ]
          ub y p = subst (λ - → [ - ⊑[ pos-A ] x ]) p (⊑[ pos-A ]-refl x)

          least : [ isLeastSuch A x (η (carrier-set A) x) ]
          least z u-ub = u-ub x refl

    union-⋁ : [ ∀[ U ] ∀[ V ] hasAJoin A U ⇒ hasAJoin A V ⇒ hasAJoin A (_∪_ (carrier-set A) U V) ]
    union-⋁ U V (⋁U , ⋁U-ub , ⋁U-least) (⋁V , ⋁V-ub , ⋁V-least) =
      (⋁U ∨A ⋁V) , ub , least
      where
        abstract
          ub : [ isUB A (⋁U ∨A ⋁V) (_∪_ (carrier-set A) U V) ]
          ub x x∈U∪V = ∥∥-rec (isProp[] (x ⊑[ pos-A ] _)) nts x∈U∪V
            where
              nts : (x ∈ fst U) ⊎ (x ∈ fst V) → [ x ⊑[ pos-A ] (⋁U ∨A ⋁V) ]
              nts (inl x∈U) = x ⊑⟨ ⋁U-ub x x∈U ⟩ ⋁U ⊑⟨ fst (∨-upper ⋁U ⋁V) ⟩ (⋁U ∨A ⋁V) ■
              nts (inr x∈V) = x ⊑⟨ ⋁V-ub x x∈V ⟩ ⋁V ⊑⟨ snd (∨-upper ⋁U ⋁V) ⟩ (⋁U ∨A ⋁V) ■

          least : [ isLeastSuch A (⋁U ∨A ⋁V) (_∪_ (carrier-set A) U V) ]
          least z z-ub =
            ∨-least ⋁U ⋁V z (⋁U-least z z-ub-of-U , ⋁V-least z z-ub-of-V)
            where
              z-ub-of-U : [ isUB A z U ]
              z-ub-of-U w w∈U = z-ub w ∣ inl w∈U ∣

              z-ub-of-V : [ isUB A z V ]
              z-ub-of-V w w∈V = z-ub w ∣ inr w∈V ∣
```

```agda
open JoinSemilatticeNotation

⋁KF[_]_ : (A : JoinSemilattice ℓ₀ ℓ₁) → (U : ⟦ KFin ℓ₀ (carrier-set A) ⟧) → carrier A
⋁KF[ A ] U = fst (KFin-has-join A U)
```

```agda
module KFinImage (A : JoinSemilattice ℓ₀ ℓ₁) (X : JoinSemilattice ℓ₀′ ℓ₁′) where

  _⟨$⟩_ : (f : carrier A → carrier X) → ⟦ KFin ℓ′ (carrier-set A) ⟧ → ⟦ KFin (ℓ-max (ℓ-max ℓ₀ ℓ₀′) ℓ′) (carrier-set X) ⟧
  _⟨$⟩_ {ℓ′ = ℓ′} f (U , U-kfin) = V , V-kfin
    where
      V : ⟦ carrier-set X ⟧ → hProp (ℓ-max (ℓ-max ℓ₀ ℓ₀′) ℓ′)
      V y = ∥ (Σ[ x ∈ carrier A ] [ U x ] × (f x ≡ y)) ∥ , ∥∥-prop _

      V-kfin : [ isKFin (carrier-set X) V ]
      V-kfin = ∥∥-rec (isProp[] (isKFin (carrier-set X) V)) nts U-kfin
        where
          nts : Σ[ n ∈ ℕ ] ⟦ Fin n ↠ ((carrier-set A) restricted-to U) ⟧ → [ isKFin (carrier-set X) V ]
          nts (n , g , g-surj) = ∣ n , h , h-surj ∣
            where
              h : ⟦ Fin n ⟧ → ⟦ carrier-set X restricted-to V ⟧
              h i = f (fst (g i)) , ∣ fst (g i) , snd (g i) , refl ∣

              h-surj : [ isSurjective (Fin n) (carrier-set X restricted-to V) h ]
              h-surj (y , y∈V) = ∥∥-rec (∥∥-prop _) foo y∈V
                where
                  foo : Σ-syntax (carrier A) (λ x₁ → [ U x₁ ] × (f x₁ ≡ y)) → ∥ Σ-syntax ⟦ Fin n ⟧ (λ x₁ → h x₁ ≡ (y , y∈V)) ∥
                  foo (x , x∈U , fx=y) = ∥∥-rec (∥∥-prop _) bar (g-surj (x , x∈U))
                    where
                      abstract
                        bar : Σ-syntax ⟦ Fin n ⟧ (λ x₁ → g x₁ ≡ (x , x∈U)) → ∥ Σ-syntax ⟦ Fin n ⟧ (λ x₁ → h x₁ ≡ (y , y∈V)) ∥
                        bar (i , gi=x) = ∣ i , Σ≡Prop (isProp[] ∘ V) (subst (λ - → h i .fst ≡ -) fx=y (cong f λ j → fst (gi=x j))) ∣

  image-syntax : (f : carrier A → carrier X)
               → ⟦ KFin ℓ′ (carrier-set A) ⟧ → ⟦ KFin (ℓ-max (ℓ-max ℓ₀ ℓ₀′) ℓ′) (carrier-set X) ⟧
  image-syntax = _⟨$⟩_

  syntax image-syntax (λ x → e) U = ⁅ e ∣ x ∈ U ⁆
```

```agda
⋁-∅-lemma : (A : JoinSemilattice ℓ₀ ℓ₁) → fst (KFin-has-join A (∅ (carrier-set A) ℓ₀)) ≡ JoinSemilatticeNotation.𝟎 A
⋁-∅-lemma {ℓ₀ = ℓ₀} A = ⊑[ pos-A ]-antisym (fst (KFin-has-join A (∅ (carrier-set A) ℓ₀))) 𝟎-A down (𝟎-A-bottom _)
  where
    abstract
      open JoinSemilatticeNotation A using () renaming (𝟎 to 𝟎-A; pos to pos-A; carrier to carrier-A; 𝟎-bottom to 𝟎-A-bottom; _∨_ to _∨A_; ∨-least to ∨A-least)
      down : [ rel pos-A (fst (KFin-has-join A (∅ (carrier-set A) ℓ₀))) 𝟎-A ]
      down = snd (snd (KFin-has-join A (∅ (carrier-set A) ℓ₀))) 𝟎-A λ _ ()
```

```agda
⋁-η-lemma : (A : JoinSemilattice ℓ₀ ℓ₁) → (x : carrier A) → ⋁KF[ A ] (η (carrier-set A) x) ≡ x
⋁-η-lemma A x = ⊑[ pos A ]-antisym _ _ φ ψ
  where
    abstract
      φ : [ fst (KFin-has-join A (η (carrier-set A) x)) ⊑[ pos A ] x ]
      φ = snd (snd (KFin-has-join A (η (carrier-set A) x))) x (λ y y=x → subst (λ - → [ - ⊑[ pos A ] x ]) y=x (⊑[ pos A ]-refl x))

      ψ : [ x ⊑[ pos A ] (fst (KFin-has-join A (η (carrier-set A) x))) ]
      ψ = fst (snd (KFin-has-join A (η (carrier-set A) x))) x refl
```

```agda
⟨$⟩-∪-lemma : (A : JoinSemilattice ℓ₀ ℓ₁) (X : JoinSemilattice ℓ₀′ ℓ₁′)
            → (f : carrier A → carrier X)
            → (U V : ⟦ KFin ℓ₀ (carrier-set A) ⟧)
            → let open KFinImage A X
              in f ⟨$⟩ (_∪_ (carrier-set A) U V) ≡ _∪_ (carrier-set X) (f ⟨$⟩ U) (f ⟨$⟩ V)
⟨$⟩-∪-lemma A X f U V = Σ≡Prop (isProp[] ∘ isKFin (carrier-set X)) nts
  where
    open KFinImage A X

    nts₀ : ∀ x → [ fst (f ⟨$⟩ (_∪_ (carrier-set A) U V)) x ] → [ fst (_∪_ (carrier-set X) (f ⟨$⟩ U) (f ⟨$⟩ V)) x ]
    nts₀ x x-mem = ∥∥-rec (isProp[] (fst (_∪_ (carrier-set X) (f ⟨$⟩ U) (f ⟨$⟩ V)) x)) rem x-mem
      where
        rem : Σ-syntax (carrier A) (λ x₁ → [ fst ((carrier-set A ∪ U) V) x₁ ] × (f x₁ ≡ x)) → [ fst ((carrier-set X ∪ (f ⟨$⟩ U)) (f ⟨$⟩ V)) x ]
        rem (y , p , q) = ∥∥-rec (isProp[] (fst ((carrier-set X ∪ (f ⟨$⟩ U)) (f ⟨$⟩ V)) x)) rem₀ p
          where
            rem₀ : (y ∈ fst U) ⊎ (y ∈ fst V) → [ fst ((carrier-set X ∪ (f ⟨$⟩ U)) (f ⟨$⟩ V)) x ]
            rem₀ (inl y∈U) = ∣ inl (subst ([_] ∘ fst (f ⟨$⟩ U)) q ∣ y , y∈U , refl ∣) ∣
            rem₀ (inr y∈V) = ∣ inr (subst ([_] ∘ fst (f ⟨$⟩ V)) q ∣ y , y∈V , refl ∣) ∣

    nts₁ : ∀ x → [ fst ((carrier-set X ∪ (f ⟨$⟩ U)) (f ⟨$⟩ V)) x ] → [ fst (f ⟨$⟩ (carrier-set A ∪ U) V) x ]
    nts₁ x x-mem = ∥∥-rec (isProp[] (fst (f ⟨$⟩ (carrier-set A ∪ U) V) x)) rem x-mem
      where
        rem : [ fst (f ⟨$⟩ U) x ] ⊎ [ fst (f ⟨$⟩ V) x ] → [ fst (f ⟨$⟩ (carrier-set A ∪ U) V) x ]
        rem (inl x∈f⟨$⟩U) = ∥∥-rec (isProp[] (fst (f ⟨$⟩ (carrier-set A ∪ U) V) x)) foo x∈f⟨$⟩U
                            where
                              foo : Σ-syntax (carrier A) (λ x₁ → [ fst U x₁ ] × (f x₁ ≡ x)) → [ fst (f ⟨$⟩ (carrier-set A ∪ U) V) x ]
                              foo (y , y∈U , fy=x) = ∣ y , ∣ inl y∈U ∣ , fy=x ∣
        rem (inr x∈f⟨$⟩V) = ∥∥-rec (isProp[] ((fst (f ⟨$⟩ (carrier-set A ∪ U) V) x))) bar x∈f⟨$⟩V
                            where
                              bar : Σ-syntax (carrier A) (λ x₁ → [ fst V x₁ ] × (f x₁ ≡ x)) → [ fst (f ⟨$⟩ (carrier-set A ∪ U) V) x ]
                              bar (y , y∈V , fy=x) = ∣ y , ∣ inr y∈V ∣ , fy=x ∣

    abstract
      nts : fst (f ⟨$⟩ (_∪_ (carrier-set A) U V)) ≡ fst (_∪_ (carrier-set X) (f ⟨$⟩ U) (f ⟨$⟩ V))
      nts = funExt (λ x → ⇔toPath (nts₀ x) (nts₁ x))
```

```agda
η-⟨$⟩-lemma : (A X : JoinSemilattice ℓ₀ ℓ₁)
            → (f : carrier A → carrier X)
            → (x : carrier A)
            → let open KFinImage A X
              in f ⟨$⟩ (η (carrier-set A) x) ≡ η (carrier-set X) (f x)
η-⟨$⟩-lemma A X f x = Σ≡Prop (isProp[] ∘ isKFin (carrier-set X)) nts
  where
    open KFinImage A X

    abstract
      nts : fst (f ⟨$⟩ (η (carrier-set A) x)) ≡ fst (η (carrier-set X) (f x))
      nts = ⊆-extensionality _ _ (down , up)
        where
          down : fst (f ⟨$⟩ η (carrier-set A) x) ⊆ fst (η (carrier-set X) (f x))
          down y p = ∥∥-rec (isProp[] (fst (η (carrier-set X) (f x)) y)) rem p
            where
              rem : Σ-syntax (carrier A) (λ x₁ → [ fst (η (carrier-set A) x) x₁ ] × (f x₁ ≡ y)) → [ fst (η (carrier-set X) (f x)) y ]
              rem (z , x=z , fz=y) = subst (λ - → [ fst (η (carrier-set X) (f x)) - ]) fz=y (cong f x=z)

          up : fst (η (carrier-set X) (f x)) ⊆ fst (f ⟨$⟩ η (carrier-set A) x)
          up y fx=y = ∣ x , refl , fx=y ∣
```

```agda
module KFinSemilattice (A : JoinSemilattice ℓ₀ ℓ₁) where

  open JoinSemilatticeNotation A using    ()
                                 renaming (𝟎 to 𝟎-A; pos to pos-A; carrier to carrier-A; 𝟎-bottom to 𝟎-A-bottom; _∨_ to _∨A_; ∨-least to ∨A-least)

  ∣A∣ : Ψ ℓ₀
  ∣A∣ = carrier-A , carrier-is-set pos-A

  KFinPoset : PosetStr ℓ₀ ⟦ KFin ℓ₀ ∣A∣ ⟧
  KFinPoset = _⊑_ , isSet⟦⟧ (KFin ℓ₀ ∣A∣) , ⊑-refl , ⊑-trans , ⊑-antisym
    where
      _⊑_ : ⟦ KFin ℓ₀ ∣A∣ ⟧ → ⟦ KFin ℓ₀ ∣A∣ ⟧ → hProp ℓ₀
      U ⊑ V = (fst U ⊆ fst V) , ⊆-isProp (fst U) (fst V)

      abstract
        ⊑-refl : [ isReflexive _⊑_ ]
        ⊑-refl U x x∈U = x∈U

        ⊑-trans : [ isTransitive _⊑_ ]
        ⊑-trans U V W U⊑V V⊑W x x∈U = V⊑W x (U⊑V x x∈U)

        ⊑-antisym : [ isAntisym (isSet⟦⟧ (KFin ℓ₀ ∣A∣)) _⊑_ ]
        ⊑-antisym U V U⊑V V⊑U =
          Σ≡Prop
            (isProp[] ∘ isKFin ∣A∣)
            (⊆-extensionality (fst U) (fst V) (U⊑V , V⊑U))

  KFinJS : JoinSemilattice (ℓ-suc ℓ₀) ℓ₀
  KFinJS = ⟦ KFin ℓ₀ ∣A∣ ⟧ , (KFinPoset , ∅ ∣A∣ ℓ₀ , _∪_ ∣A∣) , ∅-bottom , ∪-join
    where
      abstract
        ∅-bottom : [ isBottom (⟦ KFin ℓ₀ ∣A∣ ⟧ , KFinPoset) (∅ ∣A∣ ℓ₀) ]
        ∅-bottom U x ()

        ∪-join : [ ∀[ U ∶ ⟦ KFin ℓ₀ ∣A∣ ⟧ ] ∀[ V ∶ ⟦ KFin ℓ₀ ∣A∣ ⟧ ] isJoinOf (_ , KFinPoset) (_∪_ ∣A∣ U V) U V ]
        ∪-join U V = (U⊆U∪V , V⊆U∪V) , least
          where
            U⊆U∪V : [ U ⊑[ (_ , KFinPoset) ] ((∣A∣ ∪ U) V) ]
            U⊆U∪V x x∈U = ∣ inl x∈U ∣

            V⊆U∪V : [ V ⊑[ (_ , KFinPoset) ] ((∣A∣ ∪ U) V) ]
            V⊆U∪V x x∈V = ∣ inr x∈V ∣

            least : _
            least W (U⊆W , V⊆W) x x∈U∪V = ∥∥-rec (isProp[] (fst W x)) nts x∈U∪V
              where
                nts : (x ∈ fst U) ⊎ (x ∈ fst V) → [ fst W x ]
                nts (inl x∈U) = U⊆W x x∈U
                nts (inr x∈V) = V⊆W x x∈V
```

```agda
⋁KF-upper : (A : JoinSemilattice ℓ₀ ℓ₁)
          → (U : ⟦ KFin ℓ₀ (carrier-set A) ⟧) → [ isUB A (⋁KF[ A ] U) U ]
⋁KF-upper A = fst ∘ snd ∘ KFin-has-join A
```

```agda
⋁KF-least : (A : JoinSemilattice ℓ₀ ℓ₁)
          → (U : ⟦ KFin ℓ₀ (carrier-set A) ⟧)
          → [ isLeastSuch A (⋁KF[ A ] U) U ]
⋁KF-least A = snd ∘ snd ∘ KFin-has-join A
```

```
⋁-∪-lemma : (A : JoinSemilattice ℓ₀ ℓ₁)
          → (U V : ⟦ KFin ℓ₀ (carrier-set A) ⟧)
          → let open JoinSemilatticeNotation A using () renaming (_∨_ to _∨A_)
            in ⋁KF[ A ] (_∪_ (carrier-set A) U V) ≡ (⋁KF[ A ] U) ∨A (⋁KF[ A ] V)
⋁-∪-lemma A U V =
  ⊑[ P ]-antisym _ _ down up
  where
    open JoinSemilatticeNotation A using () renaming (pos to P; _∨_ to _∨A_; ∨-upper to ∨A-upper; ∨-least to ∨A-least)

    down : [ (⋁KF[ A ] (_∪_ (carrier-set A) U) V) ⊑[ P ] ((⋁KF[ A ] U) ∨A (⋁KF[ A ] V)) ]
    down = ⋁KF-least A (_∪_ (carrier-set A) U V) ((⋁KF[ A ] U) ∨A (⋁KF[ A ] V)) nts
      where
        nts : [ isUB A ((⋁KF[ A ] U) ∨A (⋁KF[ A ] V)) (_∪_ (carrier-set A) U V) ]
        nts x x∈U∪V = ∥∥-rec (isProp[] (rel P x _)) rem x∈U∪V
          where
            open PosetReasoning (pos A)

            rem : (x ∈ fst U) ⊎ (x ∈ fst V) → [ x ⊑[ P ] ((⋁KF[ A ] U) ∨A (⋁KF[ A ] V)) ]
            rem (inl x∈U) = x ⊑⟨ ⋁KF-upper A U x x∈U ⟩ ⋁KF[ A ] U ⊑⟨ fst (∨A-upper _ _) ⟩ ((⋁KF[ A ] U) ∨A (⋁KF[ A ] V)) ■
            rem (inr x∈V) = x ⊑⟨ ⋁KF-upper A V x x∈V ⟩ ⋁KF[ A ] V ⊑⟨ snd (∨A-upper _ _) ⟩ ((⋁KF[ A ] U) ∨A (⋁KF[ A ] V)) ■

    up : [ ((⋁KF[ A ] U) ∨A (⋁KF[ A ] V)) ⊑[ P ] (⋁KF[ A ] (_∪_ (carrier-set A) U V)) ]
    up =
      ∨A-least _ _ (⋁KF[ A ] _∪_ (carrier-set A) U V) (nts₀ , nts₁)
      where
        open PosetReasoning (pos A)

        nts₀ : [ (⋁KF[ A ] U) ⊑[ P ] (⋁KF[ A ] _∪_ (carrier-set A) U V) ]
        nts₀ = ⋁KF-least A U (⋁KF[ A ] (carrier-set A ∪ U) V) rem
          where
            rem : [ isUB A (⋁KF[ A ] (carrier-set A ∪ U) V) (fst U , snd U) ]
            rem x x∈U = x ⊑⟨ ⋁KF-upper A U x x∈U ⟩ (⋁KF[ A ] U) ⊑⟨ rem₁ ⟩ (⋁KF[ A ] (carrier-set A ∪ U) V) ■
              where
                rem₀ : [ isUB A (⋁KF[ A ] (_∪_ (carrier-set A) U) V) U ]
                rem₀ y y∈U = ⋁KF-upper A (_∪_ (carrier-set A) U V) y ∣ inl y∈U ∣

                rem₁ : [ (⋁KF[ A ] U) ⊑[ P ] (⋁KF[ A ] (carrier-set A ∪ U) V) ]
                rem₁ = ⋁KF-least A U (⋁KF[ A ] (carrier-set A ∪ U) V) rem₀

        nts₁ : [ (⋁KF[ A ] V) ⊑[ P ] (⋁KF[ A ] _∪_ (carrier-set A) U V) ]
        nts₁ = ⋁KF-least A V (⋁KF[ A ] (carrier-set A ∪ U) V) rem
          where
            rem : [ isUB A (⋁KF[ A ] (carrier-set A ∪ U) V) V ]
            rem x x∈V = x ⊑⟨ ⋁KF-upper A V x x∈V ⟩ (⋁KF[ A ] V) ⊑⟨ rem₁ ⟩ (⋁KF[ A ] (carrier-set A ∪ U) V) ■
              where
                rem₀ : [ isUB A (⋁KF[ A ] (_∪_ (carrier-set A) U) V) V ]
                rem₀ y y∈V = ⋁KF-upper A (_∪_ (carrier-set A) U V) y ∣ inr y∈V ∣

                rem₁ : [ (⋁KF[ A ] V) ⊑[ P ] (⋁KF[ A ] (carrier-set A ∪ U) V) ]
                rem₁ = ⋁KF-least A V (⋁KF[ A ] (carrier-set A ∪ U) V) rem₀
```

```agda
open JSMap

resp-⋁ : (A X : JoinSemilattice ℓ₀ ℓ₁)
       → (f : carrier A → carrier X)
       → [ isJoinSemilatticeHomomorphism A X f ]
       → (U : ⟦ KFin ℓ₀ (carrier-set A) ⟧)
       → let open KFinImage A X
         in f (⋁KF[ A ] U) ≡ ⋁KF[ X ] (f ⟨$⟩ U)
resp-⋁ {ℓ₀ = ℓ₀} A X f f-hom = K-ind (carrier-set A) P φ ψ ϑ
  where
    open KFinImage A X
    open JoinSemilatticeNotation X using    ()
                                   renaming (𝟎 to 𝟎-X; _∨_ to _∨X_)
    open JoinSemilatticeNotation A using    ()
                                   renaming (carrier to ∣A∣; 𝟎 to 𝟎-A;
                                             _∨_ to _∨A_)

    P : ⟦ KFin ℓ₀ (carrier-set A) ⟧ → hProp _
    P U = (f (⋁KF[ A ] U) ≡ ⋁KF[ X ] (f ⟨$⟩ U)) , carrier-is-set (pos X) _ _

    abstract
      φ : [ P (∅ (carrier-set A) ℓ₀) ]
      φ = f (⋁KF[ A ] ∅ (carrier-set A) ℓ₀)     ≡⟨ cong f (⋁-∅-lemma A) ⟩
          f 𝟎-A                                 ≡⟨ fst f-hom            ⟩
          𝟎-X                                   ≡⟨ sym (⋁-∅-lemma X)    ⟩
          ⋁KF[ X ] (f ⟨$⟩ ∅ (carrier-set A) ℓ₀) ∎

      ψ : (x : ∣A∣) → [ P (η (carrier-set A) x) ]
      ψ x = f (⋁KF[ A ] η (carrier-set A) x)     ≡⟨ cong f (⋁-η-lemma A x)  ⟩
            f x                                  ≡⟨ sym (⋁-η-lemma X (f x)) ⟩
            ⋁KF[ X ] (f ⟨$⟩ η (carrier-set A) x) ∎

      ϑ : [ ∀[ U ] ∀[ V ] P U ⇒ P V ⇒ P (_∪_ (carrier-set A) U V) ]
      ϑ U V P-U P-V =
        f (⋁KF[ A ] _∪_ (carrier-set A) U V)               ≡⟨ cong f (⋁-∪-lemma A U V) ⟩
        f ((⋁KF[ A ] U) ∨A (⋁KF[ A ] V))                   ≡⟨ snd f-hom _ _ ⟩
        f (⋁KF[ A ] U)  ∨X f (⋁KF[ A ] V)                  ≡⟨ cong (λ - → - ∨X _) P-U ⟩
        (⋁KF[ X ] (f ⟨$⟩ U))  ∨X f (⋁KF[ A ] V)            ≡⟨ cong (λ - → _ ∨X -) P-V ⟩
        (⋁KF[ X ] (f ⟨$⟩ U))  ∨X (⋁KF[ X ] (f ⟨$⟩ V))      ≡⟨ sym (⋁-∪-lemma X (f ⟨$⟩ U) (f ⟨$⟩ V))  ⟩
        ⋁KF[ X ] (_∪_ (carrier-set X) (f ⟨$⟩ U)) (f ⟨$⟩ V) ≡⟨ sym (cong (λ - → ⋁KF[ X ] -) (⟨$⟩-∪-lemma A X f U V)) ⟩
        ⋁KF[ X ] (f ⟨$⟩ _∪_ (carrier-set A) U V)           ∎
```

```agda
module KFinFreeJoinSemilattice (A : JoinSemilattice ℓ₀ ℓ₁) where

  open JoinSemilatticeNotation A using    ()
                                 renaming (𝟎 to 𝟎-A;
                                           pos to pos-A;
                                           carrier to carrier-A;
                                           𝟎-bottom to 𝟎-A-bottom;
                                           _∨_ to _∨A_;
                                           ∨-least to ∨A-least)
  open KFinSemilattice A
  open KFinImage A KFinJS using () renaming (_⟨$⟩_ to _⟨K⟩_)

  open JoinSemilatticeNotation
  open JSMap

  main : (U : ⟦ KFin ℓ₀ (carrier-set A) ⟧) → U ≡ ⋁KF[ KFinJS ] (η ∣A∣ ⟨K⟩ U)
  main U = K-ind (carrier-set A) P ∅-case η-case ∪-case U
    where
      P : ⟦ KFin ℓ₀ (carrier-set A) ⟧ → hProp (ℓ-suc ℓ₀)
      P V = (V ≡ ⋁KF[ KFinJS ] (η ∣A∣ ⟨K⟩ V)) , carrier-is-set (pos KFinJS) V _

      ∅-case : [ P (∅ (carrier-set A) ℓ₀) ]
      ∅-case = sym (⋁-∅-lemma KFinJS)

      η-case : (x : carrier A) → [ P (η (carrier-set A) x) ]
      η-case = sym ∘ ⋁-η-lemma KFinJS ∘ η ∣A∣

      ∪-case : [ ∀[ U ] ∀[ V ] P U ⇒ P V ⇒ P (_∪_ (carrier-set A) U V) ]
      ∪-case U V P-U P-V = _∪_ (carrier-set A) U V ≡⟨ cong (λ - → _∪_ (carrier-set A) - V) P-U ⟩
                           _∪_ (carrier-set A) (⋁KF[ KFinJS ] (η ∣A∣ ⟨K⟩ U)) V ≡⟨ cong (λ - → _∪_ (carrier-set A) (⋁KF[ KFinJS ] (η ∣A∣ ⟨K⟩ U)) -) P-V ⟩
                           _∪_ (carrier-set A) (⋁KF[ KFinJS ] (η ∣A∣ ⟨K⟩ U)) (⋁KF[ KFinJS ] (η ∣A∣ ⟨K⟩ V))  ≡⟨ nts ⟩
                           (⋁KF[ KFinJS ] (η ∣A∣ ⟨K⟩ (_∪_ (carrier-set A) U) V)) ∎
        where
          nts :  _ ≡ ⋁KF[ KFinJS ] (η ∣A∣ ⟨K⟩ (_∪_ (carrier-set A) U) V) 
          nts = _ ≡⟨ sym (⋁-∪-lemma KFinJS (η ∣A∣ ⟨K⟩ U) (η ∣A∣ ⟨K⟩ V))  ⟩ ⋁KF[ KFinJS ] (carrier-set KFinJS ∪ (η ∣A∣ ⟨K⟩ U)) (η ∣A∣ ⟨K⟩ V) ≡⟨ sym (cong (λ - → ⋁KF[ KFinJS ] -) (⟨$⟩-∪-lemma A KFinJS (η ∣A∣) U V)) ⟩ _ ∎

  isFree : (X : JoinSemilattice ℓ₀ ℓ₁)
         → (f : carrier A → carrier X)
         → [ isJoinSemilatticeHomomorphism A X f ]
         → isContr
             (Σ[ f⁻ ∈ (⟦ KFin {!!} ∣A∣ ⟧ → carrier X) ]
                [ isJoinSemilatticeHomomorphism KFinJS X f⁻ ] × (f ≡ f⁻ ∘ η ∣A∣))
  isFree X f f-hom = (f⁻ , f⁻-hom , f=f⁻∘η) , shrink
    where
      open JoinSemilatticeNotation X renaming (pos to P; 𝟎 to 𝟎-X; _∨_ to _∨X_; ∨-least to ∨X-least; ∨-upper to ∨X-upper)
      open JoinSemilatticeNotation KFinJS using () renaming (𝟎 to ∅KF; _∨_ to _∨K_)
      open KFinImage A X

      ∣X∣ = carrier-set X

      ⋁_ : ⟦ KFin ℓ₀ (carrier-set A) ⟧ → ⟦ ∣A∣ ⟧
      ⋁_ V = fst (KFin-has-join A V)

      ⋁X_ : ⟦ KFin ℓ₀ (carrier-set X) ⟧ → ⟦ ∣X∣ ⟧
      ⋁X_ V = fst (KFin-has-join X V)

      f⁻ : ⟦ KFin ℓ₀ ∣A∣ ⟧ → ⟦ ∣X∣ ⟧
      f⁻ U = ⋁X (f ⟨$⟩ U)

      f⁻-hom : [ isJoinSemilatticeHomomorphism KFinJS X f⁻ ]
      f⁻-hom = resp-⊥ , resp-∨
        where
          resp-⊥ : [ respects-⊥ KFinJS X f⁻ ]
          resp-⊥ = ⋁-∅-lemma X

          resp-∨ : [ respects-∨ KFinJS X f⁻ ]
          resp-∨ U V =
            f⁻ (U ∨K V)                                   ≡⟨ refl ⟩
            ⋁X (f ⟨$⟩ (_∪_ (carrier-set A) U V))          ≡⟨ cong ⋁X_ (⟨$⟩-∪-lemma A X f U V) ⟩
            ⋁X (_∪_ (carrier-set X) (f ⟨$⟩ U) (f ⟨$⟩ V))  ≡⟨ ⋁-∪-lemma X (f ⟨$⟩ U) (f ⟨$⟩ V) ⟩
            ((⋁X (f ⟨$⟩ U)) ∨X (⋁X (f ⟨$⟩ V)))            ≡⟨ refl ⟩
            (f⁻ U ∨X f⁻ V)                                ∎

      f~f⁻∘η : (x : carrier-A) → f x ≡ f⁻ (η ∣A∣ x)
      f~f⁻∘η x = f x                  ≡⟨ sym (⋁-η-lemma X (f x)) ⟩
                 ⋁X η ∣X∣ (f x)       ≡⟨ cong ⋁X_ (sym (η-⟨$⟩-lemma A X f x)) ⟩
                 ⋁X (f ⟨$⟩ (η ∣A∣ x)) ≡⟨ refl ⟩
                 f⁻ (η ∣A∣ x)         ∎

      f=f⁻∘η : f ≡ f⁻ ∘ η ∣A∣
      f=f⁻∘η = funExt f~f⁻∘η

      shrink : ((g⁻ , g⁻-hom , f=g⁻∘η) : Σ[ g⁻ ∈ (⟦ KFin ℓ₀ ∣A∣ ⟧ → ⟦ ∣X∣ ⟧) ] [ isJoinSemilatticeHomomorphism KFinJS X g⁻ ] × (f ≡ g⁻ ∘ η ∣A∣)) → (f⁻ , f⁻-hom , f=f⁻∘η) ≡ (g⁻ , g⁻-hom , f=g⁻∘η)
      shrink (g⁻ , g⁻-hom , f=g⁻∘η) =
        Σ≡Prop (λ p → isPropΣ (isProp[] (isJoinSemilatticeHomomorphism KFinJS X p)) λ _ → isSetΠ (λ _ → carrier-is-set P) f (p ∘ η ∣A∣)) (funExt ext-eq)
        where
          ext-eq : (U : ⟦ KFin ℓ₀ ∣A∣ ⟧) → f⁻ U ≡ g⁻ U
          ext-eq U = f⁻ U                                          ≡⟨ refl                             ⟩
                     ⋁X (f ⟨$⟩ U)                                  ≡⟨ cong (λ - → ⋁X (- ⟨$⟩ U)) f=g⁻∘η ⟩
                     ⋁X ((g⁻ ∘ η (carrier-set A)) ⟨$⟩ U)           ≡⟨ {!!} ⟩
                     {!!}                                          ≡⟨ sym (resp-⋁ {!!} X {!g⁻!} {!g⁻-hom!} {!(η (carrier-set A) ⟨K⟩ U)!}) ⟩
                     g⁻ (⋁KF[ KFinJS ] (η (carrier-set A) ⟨K⟩ U))  ≡⟨ cong g⁻ (sym (main U)) ⟩
                     g⁻ U                                          ∎
            where
              open KFinImage KFinJS X using () renaming (_⟨$⟩_ to _⟨X⟩_)

              nts : [ isUB X (g⁻ (⋁KF[ KFinJS ] (η (carrier-set A) ⟨K⟩ U))) ((g⁻ ∘ (η (carrier-set A))) ⟨$⟩ U) ]
              nts x x-mem = ∥∥-rec (isProp[] (rel P x _)) rem x-mem
                where
                  rem : Σ-syntax carrier-A (λ x₁ → [ fst U x₁ ] × ((g⁻ ∘ η (carrier-set A)) x₁ ≡ x)) → [ rel P x (g⁻ (⋁KF[ KFinJS ] (η (carrier-set A) ⟨K⟩ U))) ]
                  rem (y , y∈U , p) = {!!}

              below : [ (⋁X ((λ x → g⁻ (η (carrier-set A) x)) ⟨$⟩ U)) ⊑[ P ] (g⁻ (⋁KF[ KFinJS ] (η (carrier-set A) ⟨K⟩ U))) ]
              below = ⋁KF-least X ((λ x → g⁻ (η (carrier-set A) x)) ⟨$⟩ U) (g⁻ (⋁KF[ KFinJS ] (η (carrier-set A) ⟨K⟩ U))) nts

              above : [ (g⁻ (⋁KF[ KFinJS ] (η (carrier-set A) ⟨K⟩ U))) ⊑[ P ] (⋁X ((λ x → g⁻ (η (carrier-set A) x)) ⟨$⟩ U))  ]
              above = {!!}

-- --}
```

# Acknowledgements #

I have benefitted from some discussions at the [Birmingham Agda Club][1],
particularly, some comments by Tom de Jong ([`@tomdjong`][2]).

[0]: https://ncatlab.org/nlab/show/finite+set#Constructivist
[1]: https://github.com/ayberkt/birmingham-agda-club
[2]: https://github.com/tomdjong
