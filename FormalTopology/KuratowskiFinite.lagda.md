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
open import Cubical.Foundations.Logic hiding (inl; inr) renaming (ℙ to ℙ′; powersets-are-sets to isSetℙ′)
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Basis using (bot; ∥_∥; ∥∥-rec; ∥∥-prop; ∣_∣; ∥∥-×)

private
  variable
    ℓ ℓ₀ ℓ₁ : Level
```
-->

## Definition ##

`ψ ℓ` denotes the type of h-set at level `ℓ`.

```agda
Ψ : (ℓ : Level) → Type (ℓ-suc ℓ)
Ψ ℓ = Σ[ A ∈ Type ℓ ] isSet A

⟦_⟧ : Ψ ℓ → Type ℓ
⟦ A , _ ⟧ = A

isSurjective : (A : Ψ ℓ₀) (B : Ψ ℓ₁) → (⟦ A ⟧ → ⟦ B ⟧) → Type (ℓ-max ℓ₀ ℓ₁)
isSurjective A B f = (y : ⟦ B ⟧) → ∥ Σ[ x ∈ ⟦ A ⟧ ] f x ≡ y ∥

isSet⟦⟧ : (A : Ψ ℓ) → isSet (fst A)
isSet⟦⟧ (_ , A-set) = A-set

isSurjective-set : {A : Ψ ℓ₀} {B : Ψ ℓ₁}
                 → (f : ⟦ A ⟧ → ⟦ B ⟧) → isSet (isSurjective A B f)
isSurjective-set {A = A} {B} f =
  isSetΠ (λ y → isProp→isSet (∥∥-prop (Σ[ x ∈ ⟦ A ⟧ ] f x ≡ y)))

ℙ : Ψ ℓ → Type (ℓ-suc ℓ)
ℙ (A , A-set) = ℙ′ A

_restricted-to_ : (A : Ψ ℓ) → ℙ A → Ψ ℓ
_restricted-to_ {ℓ} (A , A-set) U = (Σ[ x ∈ A ] [ U x ]) , is-set where
    is-set : isSet (Σ[ x ∈ A ] [ U x ])
    is-set = isSetΣ A-set (isProp→isSet ∘ isProp[] ∘ U)

Fin : ℕ → Ψ ℓ-zero
Fin n = Fin′ n , isSetFin

𝟎 : ⟦ Fin 1 ⟧
𝟎 = 0 , (0 , refl)
```

`A ↠ B` denotes the type of surjections from `A` to `B`.

```agda
_↠_ : Ψ ℓ₀ → Ψ ℓ₁ → Ψ (ℓ-max ℓ₀ ℓ₁)
A ↠ B = (Σ[ f ∈ (⟦ A ⟧ → ⟦ B ⟧) ] isSurjective A B f) , ↠-set
  where
    ↠-set : isSet (Σ[ f ∈ (⟦ A ⟧ → ⟦ B ⟧) ] isSurjective A B f)
    ↠-set = isSetΣ (isSetΠ (λ _ → isSet⟦⟧ B)) (isSurjective-set {A = A} {B})

_$_ = fst
```

```agda
isKFin : (A : Ψ ℓ) → ℙ A → hProp ℓ
isKFin A U =
  ∥ Σ[ n ∈ ℕ ] ⟦ Fin n ↠ (A restricted-to U) ⟧ ∥ , ∥∥-prop _

isKFin-set : (A : Ψ ℓ) → (U : ℙ A) → isSet [ isKFin A U ]
isKFin-set A U = isProp→isSet (isProp[] (isKFin A U))
```

```agda
KFin : Ψ ℓ → Ψ (ℓ-suc ℓ)
KFin A = (Σ[ U ∈ ℙ A ] [ isKFin A U ]) , is-set
  where
    is-set : isSet (Σ[ U ∈ ℙ A ] [ isKFin A U ])
    is-set = isSetΣ isSetℙ′ (isKFin-set A)

KFin-eq : (A : Ψ ℓ) → (U V : ⟦ KFin A ⟧) → fst U ≡ fst V → U ≡ V
KFin-eq A U V U=V =
  Σ≡Prop (isProp[] ∘ isKFin A) U=V

+-lemma : {m n : ℕ} → m + suc (suc n) ≡ 1 → [ ⊥ ]
+-lemma {m} {n} p = snotz (injSuc q)
  where
    q : suc (suc n) + m ≡ 1
    q = subst (λ - → - ≡ 1) (+-comm m (suc (suc n))) p

module _ (A : Ψ ℓ) where

  ∅ : ⟦ KFin A ⟧
  ∅ = (λ x → bot ℓ) , ∣ 0 , f ∣
    where
      f : ⟦ Fin 0 ↠ (A restricted-to (λ x → bot ℓ)) ⟧
      f  = (λ { (_ , n<0) → rec (¬-<-zero n<0) }) , λ ()

  ∅-uninhabited : ⟦ A restricted-to fst ∅ ⟧ → [ ⊥ ]
  ∅-uninhabited (_ , ())

  single : ⟦ A ⟧ → ℙ A
  single x = λ y → (x ≡ y) , isSet⟦⟧ A x y

  η : ⟦ A ⟧ → ⟦ KFin A ⟧
  η x =  single x , singleton-kfin
    where
      singleton-kfin : [ isKFin A (single x) ]
      singleton-kfin = ∣ 1 , f ∣
        where
          f : ⟦ Fin 1 ↠ (A restricted-to (single x)) ⟧
          f = (λ _ → x , refl) , surj
            where
              surj : isSurjective (Fin 1) (A restricted-to single x) (λ _ → x , refl)
              surj (y , p) = ∣ 𝟎 , Σ≡Prop (isProp[] ∘ single x) p ∣

module Union (A : Ψ ℓ) where

  _∪ℙ_ : ℙ A → ℙ A → ℙ A
  _∪ℙ_ U V = λ x → ∥ (x ∈ U) ⊎ (x ∈ V) ∥ , ∥∥-prop _

  +<-lemma : (m n o : ℕ) → o < m → o < (m + n)
  +<-lemma m n o (k , p) =
    (n + k) , (n + k + suc o    ≡⟨ sym (+-assoc n k _)  ⟩
               n + (k + suc o)  ≡⟨ cong (λ - → n + -) p ⟩
               n + m            ≡⟨ +-comm n m           ⟩
               m + n            ∎)

  finj+₀ : (m n : ℕ) → ⟦ Fin m ⟧ → ⟦ Fin (m + n) ⟧
  finj+₀ m n (k , k<m) = k , +<-lemma m n k k<m

  finj+₁ : (m n : ℕ) → ⟦ Fin n ⟧ → ⟦ Fin (m + n) ⟧
  finj+₁ m n (k , k<n) =
    k , subst (λ - → k < -) (+-comm n m) (+<-lemma n m k k<n)

  <-lemma : (m n o : ℕ) → o < m → (o ∸ n) < m
  <-lemma m zero o o<m = o<m
  <-lemma m (suc n) zero o<m = o<m
  <-lemma zero (suc n) (suc o) o<m = rec (¬-<-zero o<m)
  <-lemma (suc m) (suc n) (suc o) o<m =
    subst (λ - → o ∸ n < -) (+-comm m 1) (+<-lemma m 1 (o ∸ n) (<-lemma m n o (pred-≤-pred o<m)))

  ∸-lemma : (m n o : ℕ) → o < (m + n) → (o ∸ n) < (m + n)
  ∸-lemma m zero o p = p
  ∸-lemma m (suc n) o p = <-lemma (m + suc n) (suc n) o p

  split₁-lemma : (m n o : ℕ) → o < m + n → m ≤ n → m ≤ o → (o ∸ m) < n
  split₁-lemma zero    n o       o<m+n m≤n m<o = o<m+n
  split₁-lemma (suc m) n zero    o<m+n m≤n m<o = rec (¬-<-zero m<o)
  split₁-lemma (suc m) n (suc o) o<m+n m≤n m<o =
    split₁-lemma m n o (pred-≤-pred o<m+n) (<-weaken m≤n) (pred-≤-pred m<o)

  ζ : (m n o : ℕ) → o < m + n → m ≤ n → m ≤ o → ⟦ Fin n ⟧
  ζ m n o o<m+n m≤n m<o = o ∸ m , split₁-lemma m n o o<m+n m≤n m<o

  υ : (m n : ℕ) → m < m + n → 0 < n
  υ zero    zero    m<m+n = rec (¬-<-zero m<m+n)
  υ zero    (suc n) m<m+n = m<m+n
  υ (suc m) n       m<m+n = υ m n (pred-≤-pred m<m+n)

  ξ : (m n : ℕ) → m ≤ n → ⟦ Fin (m + n) ⟧ → ⟦ Fin m ⟧ ⊎ ⟦ Fin n ⟧
  ξ m n m≤n (o , p) with o ≟ m
  ξ m n m≤n (o , p) | lt o<m = inl (o , o<m)
  ξ m n m≤n (o , p) | eq o=m = inr (ζ m n o p m≤n (subst (λ - → - ≤ o) o=m ≤-refl))
  ξ m n m≤n (o , p) | gt m<o = inr (ζ m n o p m≤n (<-weaken m<o))

  isLeft : {A : Type ℓ₀} {B : Type ℓ₁} → A ⊎ B → hProp ℓ-zero
  isLeft (inl _) = ⊤
  isLeft (inr _) = ⊥

  isRight : {A : Type ℓ₀} {B : Type ℓ₁} → A ⊎ B → hProp ℓ-zero
  isRight (inr _) = ⊤
  isRight (inl _) = ⊥

  finj+₀-lemma : (m n : ℕ) → (p : m ≤ n) → (o : ⟦ Fin m ⟧) → ξ m n p (finj+₀ m n o) ≡ inl o
  finj+₀-lemma m n m≤n o = {!!}

  _∪_ : ⟦ KFin A ⟧ → ⟦ KFin A ⟧ → ⟦ KFin A ⟧
  _∪_ (U , U-kfin) (V , V-kfin) =
    (U ∪ℙ V) , ∥∥-rec (isProp[] (isKFin A (U ∪ℙ V))) NTS (∥∥-× U-kfin V-kfin)
    where
      NTS : (Σ[ m ∈ ℕ ] ⟦ Fin m ↠ (A restricted-to U) ⟧) ×
            (Σ[ n ∈ ℕ ] ⟦ Fin n ↠ (A restricted-to V) ⟧)
          → [ isKFin A (U ∪ℙ V) ]
      NTS ((m , f) , (n , g)) with m ≟ n
      NTS ((m , f) , (n , g)) | lt m<n = ∣ (m + n) , h , h-surj ∣
        where
          h : ⟦ Fin (m + n) ⟧ → ⟦ A restricted-to (U ∪ℙ V) ⟧
          h o with ξ m n (<-weaken m<n) o
          h o | inl k = (fst (f $ k)) , ∣ inl (snd (f $ k)) ∣
          h o | inr k = (fst (g $ k)) , ∣ inr (snd (g $ k)) ∣

          h-surj : isSurjective (Fin (m + n)) (A restricted-to (U ∪ℙ V)) h
          h-surj (y , ∣y∈U∪V∣) = ∥∥-rec (∥∥-prop _) NTS′ ∣y∈U∪V∣
            where
              NTS′ : (y ∈ U) ⊎ (y ∈ V) → ∥ Σ[ o ∈ ⟦ Fin (m + n) ⟧ ] h o ≡ (y , ∣y∈U∪V∣) ∥
              NTS′ (inl y∈U) = ∥∥-rec (∥∥-prop _) NTS′′ (snd f (y , y∈U))
                where
                  NTS′′ : (Σ[ z ∈ ⟦ Fin m ⟧ ] fst f z ≡ (y , y∈U))
                        → ∥ Σ[ o ∈ ⟦ Fin (m + n) ⟧ ] h o ≡ (y , ∣y∈U∪V∣) ∥
                  NTS′′ (z , fz=y) = ∣ (finj+₀ m n z) , (λ i → {!!}) ∣
              NTS′ (inr y∈V) = ∥∥-rec (∥∥-prop _) {!!} (snd g (y , y∈V))
      NTS ((m , f) , (n , g)) | eq m=n = ∣ (m + n) , {!!} ∣
      NTS ((m , f) , (n , g)) | gt m>n = ∣ (m + n) , h , h-surj ∣
        where
          h : ⟦ Fin (m + n) ⟧ → ⟦ A restricted-to (U ∪ℙ V) ⟧
          h x = {!!}

          h-surj : isSurjective (Fin (m + n)) (A restricted-to (U ∪ℙ V)) h
          h-surj = {!!}

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
```
