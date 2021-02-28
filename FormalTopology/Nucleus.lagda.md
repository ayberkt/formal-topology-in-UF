---
title: Nucleus
---

```agda
{-# OPTIONS --cubical --safe #-}

module Nucleus where

open import Basis
open import Poset
open import Frame
open import Prenucleus
open import Cubical.Foundations.HLevels using (isProp×; isProp×2; isProp×3)

-- A predicate expressing whether a function is a nucleus.
isNuclear : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (∣ L ∣F → ∣ L ∣F) → Type (ℓ-max ℓ₀ ℓ₁)
isNuclear L j = N₀ × N₁ × N₂
  where
    N₀ = (x y : ∣ L ∣F) → j (x ⊓[ L ] y) ≡ (j x) ⊓[ L ] (j y)
    N₁ = (x   : ∣ L ∣F) → [ x ⊑[ pos L ] (j x) ]
    N₂ = (x   : ∣ L ∣F) → [ j (j x) ⊑[ pos L ] j x ]

-- The type of nuclei.
Nucleus : Frame ℓ₀ ℓ₁ ℓ₂ → Type (ℓ-max ℓ₀ ℓ₁)
Nucleus L = Σ (∣ L ∣F → ∣ L ∣F) (isNuclear L)

𝓃₀ : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ((j , _) : Nucleus F)
   → (x y : ∣ F ∣F) → j (x ⊓[ F ] y) ≡ (j x) ⊓[ F ] (j y)
𝓃₀ F (_ , n₀ , _) = n₀

𝓃₁ : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ((j , _) : Nucleus F)
   → (x : ∣ F ∣F) → [ x ⊑[ pos F ] j x ]
𝓃₁ F (_ , _ , n₁ , _) = n₁

𝓃₂ : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ((j , _) : Nucleus F)
   → (x : ∣ F ∣F) → [ j (j x) ⊑[ pos F ] j x ]
𝓃₂ F (_ , _ , _ , n₂) = n₂

isNuclear-prop : (L : Frame ℓ₀ ℓ₁ ℓ₂) (j : ∣ L ∣F → ∣ L ∣F)
               → isProp (isNuclear L j)
isNuclear-prop L j = isProp×2 N₀-prop N₁-prop N₂-prop
  where
    N₀-prop : isProp _
    N₀-prop = isPropΠ2 (λ _ _ → carrier-is-set (pos L) _ _)

    N₁-prop : isProp _
    N₁-prop = isPropΠ λ x → isProp[] (x ⊑[ pos L ] j x)

    N₂-prop : isProp _
    N₂-prop = isPropΠ λ x → isProp[] (j (j x) ⊑[ pos L ] j x)

Nucleus-set : (F : Frame ℓ₀ ℓ₁ ℓ₂) → isSet (Nucleus F)
Nucleus-set F = isSetΣ
                  (isSetΠ (λ _ → carrier-is-set (pos F))) λ j →
                  isProp→isSet (isNuclear-prop F j)

record Nucleusᵣ (F : Frame 𝓤 𝓥 𝓦) : (𝓤 ∨ 𝓥) ̇ where
  constructor nucl
  field
    j : ∣ F ∣F → ∣ F ∣F

    meet-preservation : (x y : ∣ F ∣F) → j (x ⊓[ F ] y) ≡ j x ⊓[ F ] j y
    inflationarity    : (x   : ∣ F ∣F) → [ x ⊑[ pos F ] j x ]
    idempotency       : (x   : ∣ F ∣F) → [ j (j x) ⊑[ pos F ] j x ]

Nucleus≃Nucleusᵣ : (F : Frame 𝓤 𝓥 𝓦) → Nucleus F ≃ Nucleusᵣ F
Nucleus≃Nucleusᵣ F = isoToEquiv (iso to from sec ret)
  where
  to : Nucleus F → Nucleusᵣ F
  to (j , mp , inf , i) = nucl j mp inf i

  from : Nucleusᵣ F → Nucleus F
  from (nucl j mp inf i) = j , mp , inf , i

  sec : section to from
  sec (nucl _ _ _ _) = refl

  ret : retract to from
  ret (_ , _ , _ , _) = refl

-- The top element is fixed point for every nucleus.
nuclei-resp-⊤ : (L : Frame ℓ₀ ℓ₁ ℓ₂) ((j , _) : Nucleus L) → j ⊤[ L ] ≡ ⊤[ L ]
nuclei-resp-⊤ L (j , N₀ , N₁ , N₂) = ⊑[ pos L ]-antisym _ _ (⊤[ L ]-top _) (N₁ _)

-- Every nucleus is idempotent.
idem : (L : Frame ℓ₀ ℓ₁ ℓ₂) → ((j , _) : Nucleus L) → (x : ∣ L ∣F) → j (j x) ≡ j x
idem L (j , N₀ , N₁ , N₂) x = ⊑[ pos L ]-antisym _ _ (N₂ x) (N₁ (j x))

-- Every nucleus is monotonic.
mono : (L : Frame ℓ₀ ℓ₁ ℓ₂) ((j , _) : Nucleus L)
     → (x y : ∣ L ∣F) → [ x ⊑[ pos L ] y ] → [ (j x) ⊑[ pos L ] (j y) ]
mono L (j , N₀ , N₁ , N₂) x y x⊑y =
  j x             ⊑⟨ ≡⇒⊑ (pos L) (cong j (x⊑y⇒x=x∧y L x⊑y)) ⟩
  j (x ⊓[ L ] y)  ⊑⟨ ≡⇒⊑ (pos L) (N₀ x y)                   ⟩
  j x ⊓[ L ] j y  ⊑⟨ ⊓[ L ]-lower₁ (j x) (j y)              ⟩
  j y             ■
  where
    open PosetReasoning (pos L)

module Nucleus-∨-Lemmata (L : Frame ℓ₀ ℓ₁ ℓ₂) (𝒿 : Nucleus L) where

  open PosetReasoning (pos L)

  j = π₀ 𝒿
  n₁ = π₀ (π₁ (π₁ 𝒿))
  n₂ = π₁ (π₁ (π₁ 𝒿))

  nucleus-∨-lemma₀ : (x y : ∣ L ∣F)
                   → [ j (x ∨[ L ] y) ⊑[ pos L ] j (x ∨[ L ] j y) ]
  nucleus-∨-lemma₀ x y =
    mono L 𝒿 _ _ (⊔[ L ]-least x y (x ∨[ L ] (j y)) (⊔[ L ]-upper₀ _ _) α)
    where
      α : [ y ⊑[ pos L ] x ∨[ L ] (j y) ]
      α = y ⊑⟨ n₁ y ⟩ j y ⊑⟨ ⊔[ L ]-upper₁ _ _ ⟩ x ∨[ L ] j y ■

  nucleus-∨-lemma₁ : (x y : ∣ L ∣F)
                   → [ j (x ∨[ L ] j y) ⊑[ pos L ] j (j x ∨[ L ] j y) ]
  nucleus-∨-lemma₁ x y = mono L 𝒿 _ _ (⊔[ L ]-least _ _ _ (x ⊑⟨ n₁ x ⟩ j x ⊑⟨ ⊔[ L ]-upper₀ _ _ ⟩ _ ■) (⊔[ L ]-upper₁ _ _))

  nucleus-∨-lemma₂ : (x y : ∣ L ∣F)
                   → [ j (j x ∨[ L ] j y) ⊑[ pos L ] j (j (x ∨[ L ] y)) ]
  nucleus-∨-lemma₂ x y = mono L 𝒿 _ _ (⊔[ L ]-least _ _ _ (mono L 𝒿 _ _ (⊔[ L ]-upper₀ x y)) (mono L 𝒿 _ _ (⊔[ L ]-upper₁ x y)))

  nucleus-∨-thm₀ : (x y : ∣ L ∣F)
                 → j (x ∨[ L ] y) ≡ j (j x ∨[ L ] j y)
  nucleus-∨-thm₀ x y = ⊑[ pos L ]-antisym _ _ nts₀ nts₁
    where
      nts₀ : _
      nts₀ = j (x ∨[ L ] y)     ⊑⟨ nucleus-∨-lemma₀ x y ⟩
             j (x ∨[ L ] j y)   ⊑⟨ nucleus-∨-lemma₁ x y ⟩
             j (j x ∨[ L ] j y) ■

      nts₁ : _
      nts₁ = j (j x ∨[ L ] j y) ⊑⟨ nucleus-∨-lemma₂ x y ⟩
             j (j (x ∨[ L ] y)) ⊑⟨ n₂ (x ∨[ L ] y)      ⟩
             j (x ∨[ L ] y)     ■

-- The set of fixed points for nucleus `j` is equivalent hence equal to its image.
-- This is essentially due to the fact that j (j ())
nuclear-image : (L : Frame ℓ₀ ℓ₁ ℓ₂)
              → let ∣L∣ = ∣ L ∣F in (j : ∣L∣ → ∣L∣)
              → isNuclear L j
              → (Σ[ b ∈ ∣L∣ ] ∥ Σ[ a ∈ ∣L∣ ] (b ≡ j a) ∥) ≡ (Σ[ a ∈ ∣L∣ ] (j a ≡ a))
nuclear-image L j N@(n₀ , n₁ , n₂) = isoToPath (iso f g sec-f-g ret-f-g)
  where
    A-set = carrier-is-set (pos L)

    f : (Σ[ b ∈ ∣ L ∣F ] ∥ Σ[ a ∈ ∣ L ∣F ] (b ≡ j a) ∥) → Σ[ a ∈ ∣ L ∣F ] (j a ≡ a)
    f (b , img) = b , ∥∥-rec (A-set (j b) b) ind img
      where
        ind : Σ[ a ∈ ∣ L ∣F ](b ≡ j a) → j b ≡ b
        ind (a , img) =
          j b     ≡⟨ cong j img ⟩
          j (j a) ≡⟨ idem L (j , N) a ⟩
          j a     ≡⟨ sym img ⟩
          b       ∎

    g : (Σ[ a ∈ ∣ L ∣F ] (j a ≡ a)) → (Σ[ b ∈ ∣ L ∣F ] ∥ Σ[ a ∈ ∣ L ∣F ] (b ≡ j a) ∥)
    g (a , a-fix) = a , ∣ a , (sym a-fix) ∣

    sec-f-g : section f g
    sec-f-g (x , jx=x) = Σ≡Prop (λ y → A-set (j y) y) refl

    ret-f-g : retract f g
    ret-f-g (x , p) = Σ≡Prop (λ y → ∥∥-prop (Σ[ a ∈ ∣ L ∣F ] y ≡ j a)) refl

-- The set of fixed points for a nucleus `j` forms a poset.
𝔣𝔦𝔵-pos : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L) → Poset ℓ₀ ℓ₁
𝔣𝔦𝔵-pos {ℓ₀ = ℓ₀} {ℓ₁} L (j , N₀ , N₁ , N₂) =
  𝔽 , _≤_ , 𝔽-set , ≤-refl , ≤-trans , ≤-antisym
  where
    P = pos L
    A-set = carrier-is-set (pos L)

    𝔽 : Type ℓ₀
    𝔽 = Σ[ a ∈ ∣ L ∣F ] j a ≡ a

    𝔽-set : isSet 𝔽
    𝔽-set = isSetΣ A-set (λ a → isProp→isSet (A-set (j a) a))

    _≤_ : 𝔽 → 𝔽 → hProp ℓ₁
    (a , _) ≤ (b , _) = [ a ⊑[ P ] b ] , is-true-prop (a ⊑[ P ] b)

    ≤-refl : [ isReflexive _≤_ ]
    ≤-refl (x , _) = ⊑[ P ]-refl x

    ≤-trans : [ isTransitive _≤_ ]
    ≤-trans (x , _) (y , _) (z , _) x≤y y≤x = ⊑[ P ]-trans x y z x≤y y≤x

    ≤-antisym : [ isAntisym 𝔽-set _≤_ ]
    ≤-antisym (x , _) (y , _) x≤y y≤x =
      Σ≡Prop (λ z → A-set (j z) z) (⊑[ P ]-antisym x y x≤y y≤x)

-- The set of fixed points of a nucleus `j` forms a frame.
-- The join of this frame is define as ⊔ᵢ Uᵢ := j (⊔′ᵢ Uᵢ) where ⊔′ denotes the join of L.
𝔣𝔦𝔵 : (L : Frame ℓ₀ ℓ₁ ℓ₂) → (N : Nucleus L) → Frame ℓ₀ ℓ₁ ℓ₂
𝔣𝔦𝔵 {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} L N@(j , N₀ , N₁ , N₂) =
                          ∣ 𝔣𝔦𝔵-pos L N ∣ₚ
  , (strₚ (𝔣𝔦𝔵-pos L N) , (⊤[ L ] , nuclei-resp-⊤ L N) , _∧_ , ⋁_)
  , top
  , ( (λ x y → ⊓-lower₀ x y , ⊓-lower₁ x y)
    , λ { x y z (z⊑x , x⊑y) → ⊓-greatest x y z z⊑x x⊑y })
  , ((⊔-upper , ⊔-least) , distr)
  where
    𝒜 = π₀ (𝔣𝔦𝔵-pos L N)

    _⊑_ : ∣ pos L ∣ₚ → ∣ pos L ∣ₚ → hProp ℓ₁
    _⊑_        = λ x y → x ⊑[ pos L ] y

    _⊑N_ : 𝒜 → 𝒜 → hProp ℓ₁
    _⊑N_  = λ x y → x ⊑[ 𝔣𝔦𝔵-pos L N ] y

    ⋁L_ : Fam ℓ₂ ∣ L ∣F → ∣ L ∣F
    ⋁L x = ⋁[ L ] x

    ⊑N-antisym = ⊑[ 𝔣𝔦𝔵-pos L N ]-antisym
    A-set      = carrier-is-set (𝔣𝔦𝔵-pos L N)

    open PosetReasoning (pos L)

    _∧_ : 𝒜 → 𝒜 → 𝒜
    _∧_ (x , x-f) (y , y-f) =
      x ⊓[ L ] y , NTS
      where
        NTS : j (x ⊓[ L ] y) ≡ x ⊓[ L ] y
        NTS = j (x ⊓[ L ] y)    ≡⟨ N₀ x y                      ⟩
              j x ⊓[ L ] j y    ≡⟨ cong (λ - → - ⊓[ L ] _) x-f ⟩
                x ⊓[ L ] j y    ≡⟨ cong (λ - → _ ⊓[ L ] -) y-f ⟩
                x ⊓[ L ] y      ∎

    ⋁_ : Fam ℓ₂ 𝒜 → 𝒜
    ⋁ (I , F) = j (⋁[ L ] 𝒢) , j⊔L-fixed
      where
        𝒢 = I , π₀ ∘ F
        j⊔L-fixed : j (j (⋁[ L ] 𝒢)) ≡ j (⋁[ L ] 𝒢)
        j⊔L-fixed = ⊑[ pos L ]-antisym _ _ (N₂ (⋁[ L ] 𝒢)) (N₁ (j (⋁[ L ] 𝒢)))

    open JoinSyntax 𝒜 ⋁_

    top : (o : 𝒜) → [ o ⊑N (⊤[ L ] , nuclei-resp-⊤ L N) ]
    top = ⊤[ L ]-top ∘ π₀

    ⊓-lower₀ : (o p : 𝒜) → [ (o ∧ p) ⊑N o ]
    ⊓-lower₀ (o , _) (p , _) = ⊓[ L ]-lower₀ o p

    ⊓-lower₁ : (o p : 𝒜) → [ (o ∧ p) ⊑N p ]
    ⊓-lower₁ (o , _) (p , _) = ⊓[ L ]-lower₁ o p

    ⊓-greatest : (o p q : 𝒜) → [ q ⊑N o ] → [ q ⊑N p ] → [ q ⊑N (o ∧ p) ]
    ⊓-greatest (o , _) (p , _) (q , _) q⊑o q⊑p = ⊓[ L ]-greatest o p q q⊑o q⊑p

    ⊔-least : (U : Fam ℓ₂ 𝒜) (u : 𝒜) → [ ∀[ x ε U ] (x ⊑N u) ] → [ (⋁ U) ⊑N u ]
    ⊔-least U (u , fix) U⊑u = subst (λ - → [ j (⋁[ L ] 𝒢) ⊑ - ]) fix NTS₀
      where
        𝒢 : Fam ℓ₂ ∣ pos L ∣ₚ
        𝒢 = π₀ ⟨$⟩ U

        𝒢⊑u : [ ∀[ o ε 𝒢 ] (o ⊑ u) ]
        𝒢⊑u o (i , eq′) = o     ⊑⟨ ≡⇒⊑ (pos L) (sym eq′)               ⟩
                          𝒢 $ i ⊑⟨ U⊑u (𝒢 $ i , π₁ (U $ i)) (i , refl) ⟩
                          u     ■

        NTS₀ : [ j (⋁[ L ] 𝒢) ⊑ j u ]
        NTS₀ = mono L N (⋁[ L ] 𝒢) u (⋁[ L ]-least 𝒢 u 𝒢⊑u)

    ⊔-upper : (U : Fam ℓ₂ 𝒜) (x : 𝒜) → x ε U → [ x ⊑N (⋁ U) ]
    ⊔-upper U (x , _) o∈U@(i , eq) =
      x                   ⊑⟨ NTS                  ⟩
      ⋁[ L ] (π₀ ⟨$⟩ U)     ⊑⟨ N₁ (⋁[ L ] (π₀ ⟨$⟩ U)) ⟩
      j (⋁[ L ] (π₀ ⟨$⟩ U)) ■
      where
        NTS : [ x ⊑ (⋁[ L ] (π₀ ⟨$⟩ U)) ]
        NTS = ⋁[ L ]-upper (π₀ ⟨$⟩ U) x (i , λ j → π₀ (eq j))

    distr : (x : Σ[ x ∈ ∣ L ∣F ] j x ≡ x) (U@(I , _) : Fam ℓ₂ 𝒜)
          → x ∧ (⋁ U) ≡ ⋁⟨ i ⟩ (x ∧ (U $ i))
    distr 𝓍@(x , jx=x) U@(I , F) = Σ≡Prop (λ x → carrier-is-set (pos L) (j x) x) NTS
      where
        -- U is a family of inhabitants of ∣ L ∣F paired with proofs that they are fixed
        -- points for j. U₀ is the family obtained by discarding the proofs
        U₀ : Fam ℓ₂ ∣ L ∣F
        U₀ = ⁅ π₀ x ∣ x ε U ⁆

        x=jx = sym jx=x

        NTS :  π₀ (𝓍 ∧ (⋁ U)) ≡ π₀ (⋁⟨ i ⟩ (𝓍 ∧ (U $ i)))
        NTS =
          π₀ (𝓍 ∧ (⋁ U))                     ≡⟨ refl                                 ⟩
          x ⊓[ L ] j (⋁L U₀)                 ≡⟨ cong (λ - → - ⊓[ L ] j (⋁L U₀)) x=jx ⟩
          j x ⊓[ L ] j (⋁L U₀)               ≡⟨ sym (N₀ x (⋁[ L ] U₀))               ⟩
          j (x ⊓[ L ] (⋁L U₀))               ≡⟨ cong j (dist L x U₀)                 ⟩
          j (⋁L ⁅ x ⊓[ L ] yᵢ ∣ yᵢ ε U₀ ⁆)   ≡⟨ refl                                 ⟩
          π₀ (⋁⟨ i ⟩ (𝓍 ∧ (U $ i)))          ∎
```

```agda
nucleus⇒prenucleus : (F : Frame ℓ₀ ℓ₁ ℓ₂) → Nucleus F → Prenucleus F
nucleus⇒prenucleus F (j , n₀ , n₁ , _)= j , n₀ , n₁
```

```agda
isASublocaleOf : (S : Frame ℓ₀ ℓ₁ ℓ₂) (F : Frame ℓ₀ ℓ₁ ℓ₂) → Type _
isASublocaleOf S F = Σ[ j ∈ Nucleus F ] S ≡ 𝔣𝔦𝔵 F j
```

## The identity nucleus

```agda
idn : (F : Frame 𝓤 𝓥 𝓦) → Nucleus F
π₀ (idn F)           = id ∣ F ∣F
π₀ (π₁ (idn F)) _ _  = refl
π₀ (π₁ (π₁ (idn F))) = ⊑[ pos F ]-refl
π₁ (π₁ (π₁ (idn F))) = ⊑[ pos F ]-refl
```
