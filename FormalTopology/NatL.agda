{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Function using (_∘_)

private
  variable
    ℓ ℓ₀ ℓ₁ : Level

data ℕ (ℓ : Level) : Type ℓ where
  zero : ℕ ℓ
  suc  : ℕ ℓ → ℕ ℓ

_+_ : ℕ ℓ → ℕ ℓ → ℕ ℓ
zero  + n = n
suc m + n = suc (m + n)

_≤_ : ℕ ℓ → ℕ ℓ → Type ℓ
_≤_ {ℓ = ℓ} m n = Σ[ k ∈ ℕ ℓ ] (k + m) ≡ n

≤-refl : {n : ℕ ℓ} → n ≤ n
≤-refl = zero , refl

_<_ : ℕ ℓ → ℕ ℓ → Type ℓ
m < n = suc m ≤ n

Fin′ : {ℓ : Level} → ℕ ℓ →  Type ℓ
Fin′ {ℓ = ℓ} n = Σ[ k ∈ ℕ ℓ ] (k < n)

predℕ : ℕ ℓ → ℕ ℓ
predℕ zero    = zero
predℕ (suc n) = n

injSuc : {m n : ℕ ℓ} → suc m ≡ suc n → m ≡ n
injSuc = cong predℕ

ifZero : {A : Type ℓ₀} → A → A → ℕ ℓ → A
ifZero z s zero    = z
ifZero z s (suc _) = s

znots : {n : ℕ ℓ} → ¬ (zero ≡ suc n)
znots {n = n} p = subst (ifZero Unit ⊥) p tt

snotz : {n : ℕ ℓ} → ¬ (suc n ≡ zero)
snotz p = subst (ifZero ⊥ Unit) p tt

discreteℕ : Discrete (ℕ ℓ)
discreteℕ zero    zero    = yes refl
discreteℕ zero    (suc n) = no znots
discreteℕ (suc m) zero    = no snotz
discreteℕ (suc m) (suc n) with discreteℕ m n
discreteℕ (suc m) (suc n) | yes p = yes (cong suc p)
discreteℕ (suc m) (suc n) | no  p = no (p ∘ injSuc)

isSetℕ : isSet (ℕ ℓ)
isSetℕ = Discrete→isSet discreteℕ

+-zero : (m : ℕ ℓ) → m + zero ≡ m
+-zero zero    = refl
+-zero (suc m) = cong suc (+-zero m)

+-suc : (m n : ℕ ℓ) → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : (m n : ℕ ℓ) → m + n ≡ n + m
+-comm m zero    = +-zero m
+-comm m (suc n) = (+-suc m n) ∙ (cong suc (+-comm m n))

inj-m+ : {m n l : ℕ ℓ} → m + l ≡ m + n → l ≡ n
inj-m+ {m = zero}  p = p
inj-m+ {m = suc m} p = inj-m+ (injSuc p)

inj-+m : {m n l : ℕ ℓ} → l + m ≡ n + m → l ≡ n
inj-+m {m = m} {n} {l} eq = inj-m+ ((+-comm m l) ∙ (eq ∙ (+-comm n m)))

isProp≤ : {m n : ℕ ℓ} → isProp (m ≤ n)
isProp≤ {m = m} {n} (k , p) (l , q) = Σ≡Prop witness-prop nts where

  witness-prop : (x : ℕ _) → isProp ((x + m) ≡ n)
  witness-prop x = isSetℕ (x + m) n

  nts : k ≡ l
  nts = inj-+m (k + m ≡⟨ p ⟩ n ≡⟨ sym q ⟩ l + m ∎)


isSetFin : (n : ℕ ℓ) → isSet (Fin′ n)
isSetFin n = isSetΣ isSetℕ λ m → isProp→isSet isProp≤

¬-<-zero : {m : ℕ ℓ} → ¬ m < zero
¬-<-zero (k , p) = snotz ((sym (+-suc k _)) ∙ p)

+-assoc : (m n o : ℕ ℓ) → m + (n + o) ≡ (m + n) + o
+-assoc zero    _ _ = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

_∸_ : ℕ ℓ → ℕ ℓ → ℕ ℓ
n     ∸ zero  = n
zero  ∸ suc m = zero
suc n ∸ suc m = n ∸ m

pred-≤-pred : {m n : ℕ ℓ} → suc m ≤ suc n → m ≤ n
pred-≤-pred (k , p) = k , injSuc ((sym (+-suc k _)) ∙ p)

data Trichotomy (m n : ℕ ℓ) : Type ℓ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

suc-≤-suc : {m n : ℕ ℓ} → m ≤ n → suc m ≤ suc n
suc-≤-suc (k , p) = k , (+-suc k _) ∙ cong suc p

Trichotomy-suc : {m n : ℕ ℓ} → Trichotomy m n → Trichotomy (suc m) (suc n)
Trichotomy-suc (lt m<n) = lt (suc-≤-suc m<n)
Trichotomy-suc (eq m=n) = eq (cong suc m=n)
Trichotomy-suc (gt n<m) = gt (suc-≤-suc n<m)

<-weaken : {m n : ℕ ℓ} → m < n → m ≤ n
<-weaken (k , p) = (suc k) , (sym (+-suc k _) ∙ p)

zero-≤ : {n : ℕ ℓ} → zero ≤ n
zero-≤ {n = n} = n , +-zero n

_≟_ : (m n : ℕ ℓ) → Trichotomy m n
zero  ≟ zero  = eq refl
zero  ≟ suc n = lt (n , +-comm n (suc zero))
suc m ≟ zero  = gt (m , +-comm m (suc zero))
suc m ≟ suc n = Trichotomy-suc (m ≟ n)

≤-+k : {m n k : ℕ ℓ} → m ≤ n → (m + k) ≤ (n + k)
≤-+k {m = m} {k = k} (i , p)
  = i , (+-assoc i m k) ∙ cong (_+ k) p

≤-k+ : {m n k : ℕ ℓ} → m ≤ n → (k + m) ≤ (k + n)
≤-k+ {m = m} {n} {k}
  = subst (_≤ (k + n)) (+-comm m k)
  ∘ subst ((m + k) ≤_) (+-comm n k)
  ∘ ≤-+k

<-k+ : {m n k : ℕ ℓ} → m < n → (k + m) < (k + n)
<-k+ {m = m} {n} {k} p = subst (λ km → km ≤ (k + n)) (+-suc k m) (≤-k+ p)

≤-k+-cancel : {k m n : ℕ ℓ} → (k + m) ≤ (k + n) → m ≤ n
≤-k+-cancel {k = k} {m} (l , p) = l , inj-m+ (sub k m ∙ p)
 where
 sub : ∀ k m → k + (l + m) ≡ l + (k + m)
 sub k m = +-assoc k l m ∙ cong (_+ m) (+-comm k l) ∙ sym (+-assoc l k m)

<-k+-cancel : {k m n : ℕ ℓ} → (k + m) < (k + n) → m < n
<-k+-cancel {k = k} {m} {n} = ≤-k+-cancel ∘ subst (_≤ (k + n)) (sym (+-suc k m))

¬m+n<m : {m n : ℕ ℓ} → ¬ (m + n) < m
¬m+n<m {m = m} {n} = ¬-<-zero ∘ <-k+-cancel ∘ subst ((m + n) <_) (sym (+-zero m))

isContrFin1 : {ℓ : Level} → isContr (Fin′ {ℓ} (suc zero))
isContrFin1 = (zero , (zero , refl)) , p
  where
    p : (y : Fin′ (suc zero)) → (zero , zero , (λ _ → zero + suc zero)) ≡ y
    p (zero  , _) = Σ≡Prop (λ n → isProp≤) refl
    p (suc k , sk<1) = rec (¬-<-zero (pred-≤-pred sk<1))

¬Fin0 : {ℓ : Level} → ¬ (Fin′ {ℓ} zero)
¬Fin0 {ℓ} (k , k<0) = ¬-<-zero k<0

chlevel : (ℓ′ : Level) → ℕ ℓ → ℕ ℓ′
chlevel ℓ′ zero    = zero
chlevel ℓ′ (suc n) = suc (chlevel ℓ′ n)
