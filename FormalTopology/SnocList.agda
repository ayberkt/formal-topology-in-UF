{-# OPTIONS --cubical --safe #-}

open import Basis
open import Cubical.Data.Empty.Base using (⊥; rec)
open import Cubical.Relation.Nullary.DecidableEq using (Discrete→isSet)
open import Cubical.Relation.Nullary using (Discrete; yes; no; Dec; ¬_)

module SnocList (Z : Type zero) (_≟_ : Discrete Z) where

data SnocList : Type zero where
  []  : SnocList
  _⌢_ : SnocList → Z → SnocList

infixl 5 _⌢_

⌢-eq-left : {xs ys : SnocList} {x y : Z} → xs ⌢ x ≡ ys ⌢ y → xs ≡ ys
⌢-eq-left {ys = ys} p = subst (λ { (zs ⌢ _) → zs ≡ ys ; [] → Z }) (sym p) refl

⌢-eq-right : {xs ys : SnocList} {x y : Z} → xs ⌢ x ≡ ys ⌢ y → x ≡ y
⌢-eq-right {x = x} {y = y} p with x ≟ y
⌢-eq-right {x = x} {y = y} p | yes q = q
⌢-eq-right {x = x} {y = y} p | no ¬q = sym (subst P p refl)
  where
    P : SnocList → Type zero
    P []      = ⊥
    P (_ ⌢ z) = z ≡ x

⌢≠[] : {xs : SnocList} {x : Z} → ¬ (xs ⌢ x ≡ [])
⌢≠[] p = subst P p tt
  where
    P : SnocList → Type zero
    P []      = ⊥
    P (_ ⌢ _) = Unit zero


SnocList-discrete : Discrete SnocList
SnocList-discrete [] [] = yes refl
SnocList-discrete [] (ys ⌢ y) = no λ p → ⌢≠[] (sym p)
SnocList-discrete (xs ⌢ x) [] = no λ p → ⌢≠[] p
SnocList-discrete (xs ⌢ x) (ys ⌢ y)
  with x ≟ y | SnocList-discrete xs ys
...  | _     | no ¬q = no λ q → ¬q (⌢-eq-left  q)
...  | no ¬p | _     = no λ p → ¬p (⌢-eq-right p)
...  | yes p | yes q = subst P (sym q) (subst Q (sym p) (yes refl))
                       where
                         P = λ xs′ → Dec (xs′ ⌢ x  ≡ ys ⌢ y)
                         Q = λ x′  → Dec (ys  ⌢ x′ ≡ ys ⌢ y)

SnocList-set : isSet SnocList
SnocList-set = Discrete→isSet SnocList-discrete

_++_ : SnocList → SnocList → SnocList
xs ++ []       = xs
xs ++ (ys ⌢ y) = (xs ++ ys) ⌢ y

[]≠⌢++ : (xs ys : SnocList) (x : Z) → ¬ ([] ≡ ((xs ⌢ x) ++ ys))
[]≠⌢++ xs []        x p = ⌢≠[] (sym p)
[]≠⌢++ xs (ys ⌢ y)  x p = ⌢≠[] (sym p)

snoc-lemma : (xs ys : SnocList) (x : Z) → (xs ⌢ x) ++ ys ≡ xs ++ (([] ⌢ x) ++ ys)
snoc-lemma xs [] x = refl
snoc-lemma xs (ys ⌢ y) x = cong (λ - → - ⌢ y) (snoc-lemma xs ys x)

++-left-id : (xs : SnocList) → [] ++ xs ≡ xs
++-left-id [] = refl
++-left-id (xs ⌢ x) = cong (λ - → - ⌢ x) (++-left-id xs)

assoc : (xs ys zs : SnocList) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc xs ys []       = refl
assoc xs ys (zs ⌢ z) = cong (λ - → - ⌢ z) (assoc xs ys zs)

xs≠xs⌢y : {xs : SnocList} {y : Z} → ¬ (xs ≡ xs ⌢ y)
xs≠xs⌢y {[]}     p = subst (λ { [] → Unit zero ; (_ ⌢ _) → ⊥ }) p tt
xs≠xs⌢y {xs ⌢ x} p = rec (xs≠xs⌢y (⌢-eq-left p))

xs≰xs⌢y : {xs ys : SnocList} {x : Z} → ¬ (xs ≡ (xs ⌢ x) ++ ys)
xs≰xs⌢y {[]} {[]} {y} p = subst (λ { (_ ⌢ _) → ⊥ ; [] → Unit zero }) p tt
xs≰xs⌢y {[]} {ys ⌢ _} {y} p = subst (λ { (_ ⌢ _) → ⊥ ; [] → Unit zero }) p tt
xs≰xs⌢y {xs ⌢ x} {[]} {y} p = rec (xs≠xs⌢y (⌢-eq-left p))
xs≰xs⌢y {xs ⌢ x} {ys ⌢ y} {y′} p = rec (xs≰xs⌢y NTS)
  where
    NTS : xs ≡ (xs ⌢ x) ++ (([] ⌢ y′) ++ ys)
    NTS = xs                            ≡⟨ ⌢-eq-left p                       ⟩
          (xs ⌢ x ⌢ y′) ++ ys           ≡⟨ snoc-lemma ((xs ⌢ x) ++ []) ys y′ ⟩
          (xs ⌢ x) ++ (([] ⌢ y′) ++ ys) ∎

lemma3 : {xs : SnocList} {ys : SnocList} {y : Z} → ¬ (xs ≡ xs ++ (ys ⌢ y))
lemma3 {[]}     {ys}     {y}  p = rec (⌢≠[] NTS)
  where
    NTS : ys ⌢ y ≡ []
    NTS = (ys ⌢ y)       ≡⟨ sym (cong (λ - → - ⌢ y) (++-left-id ys)) ⟩
          ([] ++ ys) ⌢ y ≡⟨ sym p ⟩
          []             ∎
lemma3 {xs ⌢ x} {[]}     {y}  p = rec (lemma3 (⌢-eq-left p))
lemma3 {xs ⌢ x} {ys ⌢ y} {y′} p = rec (lemma3 NTS)
  where
    NTS : xs ≡ (xs ++ (([] ⌢ x) ++ ys)) ⌢ y
    NTS = xs                         ≡⟨ ⌢-eq-left p              ⟩
          ((xs ⌢ x) ++ ys) ⌢ y       ≡⟨ snoc-lemma xs (ys ⌢ y) x ⟩
          xs ++ (([] ⌢ x) ++ ys) ⌢ y ∎


++-lemma : {xs ys zs₀ zs₁ : SnocList} → xs ≡ ys ++ zs₀ → xs ≡ ys ++ zs₁ → zs₀ ≡ zs₁
++-lemma {[]} {[]} {zs₀} {zs₁} p q = zs₀       ≡⟨ sym (++-left-id zs₀) ⟩
                                     [] ++ zs₀ ≡⟨ sym p ⟩
                                     []        ≡⟨ q ⟩
                                     [] ++ zs₁ ≡⟨ ++-left-id zs₁ ⟩
                                     zs₁       ∎
++-lemma {[]} {ys ⌢ y} {[]} {[]} p q = refl
++-lemma {[]} {ys ⌢ y} {[]} {zs₁ ⌢ x} p q = rec (⌢≠[] (sym p))
++-lemma {[]} {ys ⌢ y} {zs₀ ⌢ x} {[]} p q = rec (⌢≠[] (sym q))
++-lemma {[]} {ys ⌢ y} {zs₀ ⌢ x} {zs₁ ⌢ x₁} p q = rec (⌢≠[] (sym p))
++-lemma {xs ⌢ x} {[]} {[]} {zs₁} p q = rec (⌢≠[] p)
++-lemma {xs ⌢ x} {[]} {zs₀ ⌢ z₀} {[]} p q = rec (⌢≠[] q)
++-lemma {xs ⌢ x} {[]} {zs₀ ⌢ z₀} {zs₁ ⌢ z₁} p q =
  zs₀ ⌢ z₀         ≡⟨ cong (λ - → - ⌢ z₀) (sym (++-left-id zs₀)) ⟩
  ([] ++ zs₀) ⌢ z₀ ≡⟨ sym p ⟩
  xs ⌢ x           ≡⟨ q ⟩
  ([] ++ zs₁) ⌢ z₁ ≡⟨ cong (λ - → - ⌢ z₁) (++-left-id zs₁) ⟩
  zs₁ ⌢ z₁         ∎
++-lemma {xs ⌢ x} {ys ⌢ y} {[]} {[]} p q = refl
++-lemma {xs ⌢ x} {ys ⌢ y} {[]} {zs₁ ⌢ z₁} p q = rec (xs≰xs⌢y (⌢-eq-left NTS))
  where
    NTS : ys ⌢ y ≡ ((ys ⌢ y) ++ zs₁) ⌢ z₁
    NTS = ys ⌢ y ≡⟨ sym p ⟩ xs ⌢ x ≡⟨ q ⟩ ((ys ⌢ y) ++ zs₁) ⌢ z₁ ∎
++-lemma {xs ⌢ x} {ys ⌢ y} {zs₀ ⌢ z₀} {[]} p q = rec (xs≰xs⌢y (⌢-eq-left NTS))
  where
    NTS : ys ⌢ y ≡ ((ys ⌢ y) ++ zs₀) ⌢ z₀
    NTS = ys ⌢ y ≡⟨ sym q ⟩ xs ⌢ x ≡⟨ p ⟩ ((ys ⌢ y) ++ (zs₀ ⌢ z₀)) ∎
++-lemma {xs ⌢ x} {ys ⌢ y} {zs₀ ⌢ z₀} {zs₁ ⌢ z₁} p q with z₀ ≟ z₁
... | yes z₀=z₁ = zs₀ ⌢ z₀ ≡⟨ cong (λ - → - ⌢ z₀) IH ⟩
                  zs₁ ⌢ z₀ ≡⟨ cong (_⌢_ zs₁) z₀=z₁   ⟩
                  zs₁ ⌢ z₁ ∎
                  where
                    IH : zs₀ ≡ zs₁
                    IH = ++-lemma (⌢-eq-left p) (⌢-eq-left q)
... | no ¬p = rec (¬p (⌢-eq-right NTS))
              where
                NTS : ((ys ⌢ y) ++ zs₀) ⌢ z₀ ≡ ((ys ⌢ y) ++ zs₁) ⌢ z₁
                NTS = (ys ⌢ y) ++ zs₀ ⌢ z₀ ≡⟨ sym p ⟩ xs ⌢ x ≡⟨ q ⟩ (ys ⌢ y) ++ zs₁ ⌢ z₁ ∎

nonempty : SnocList → Type zero
nonempty []       = ⊥
nonempty (xs ⌢ x) = Unit zero

head : (xs : SnocList) → nonempty xs → Z
head ([] ⌢ x) p = x
head ((xs ⌢ x′) ⌢ x) p = head (xs ⌢ x′) tt

tail : (xs : SnocList) → nonempty xs → SnocList
tail ([] ⌢ x) tt = []
tail (xs ⌢ x₀ ⌢ x₁) p = (tail (xs ⌢ x₀) tt) ⌢ x₁

hd-tl-lemma : (xs : SnocList) (ne : nonempty xs) → ([] ⌢ head xs ne) ++ tail xs ne ≡ xs
hd-tl-lemma ([] ⌢ x) tt = refl
hd-tl-lemma (xs ⌢ x₀ ⌢ x₁) tt = cong (λ - → - ⌢ x₁) (hd-tl-lemma (xs ⌢ x₀) tt)
