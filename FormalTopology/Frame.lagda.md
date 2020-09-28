---
title: Frame
---

```agda
{-# OPTIONS --without-K --cubical --safe #-}

module Frame where

open import Basis                        hiding (A)
open import Cubical.Foundations.Function using (uncurry)
open import Cubical.Foundations.SIP
open import Cubical.Structures.Axioms
open import Cubical.Foundations.Equiv    using (_≃⟨_⟩_)   renaming (_■ to _𝔔𝔈𝔇)
open import Poset

module JoinSyntax (A : Type ℓ₀) {ℓ₂ : Level} (join : Fam ℓ₂ A → A) where

  join-of : {I : Type ℓ₂} → (I → A) → A
  join-of {I = I} f = join (I , f)

  syntax join-of (λ i → e) = ⋁⟨ i ⟩ e


RawFrameStr : (ℓ₁ ℓ₂ : Level) → Type ℓ₀ → Type _
RawFrameStr ℓ₁ ℓ₂ A = PosetStr ℓ₁ A × A × (A → A → A) × (Fam ℓ₂ A → A)

pos-of-raw-frame : (Σ[ A ∈ Type ℓ₀ ] RawFrameStr ℓ₁ ℓ₂ A) → Poset ℓ₀ ℓ₁
pos-of-raw-frame (A , ps , _) = A , ps

RawFrameStr-set : (ℓ₁ ℓ₂ : Level) (A : Type ℓ₀)
                → isSet (RawFrameStr ℓ₁ ℓ₂ A)
RawFrameStr-set ℓ₁ ℓ₂ A = isSetΣ (PosetStr-set ℓ₁ A) NTS
  where
    NTS : _
    NTS pos = isSetΣ A-set λ _ →
              isSetΣ (isSetΠ2 λ _ _ → A-set) λ _ →
              isSetΠ λ _ → A-set
      where
        A-set : isSet A
        A-set = carrier-is-set (A , pos)

isTop : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → hProp _
isTop P x = ((y : ∣ P ∣ₚ) → [ y ⊑[ P ] x ]) , isPropΠ λ y → is-true-prop (y ⊑[ P ] x)

isGLB : (P : Poset ℓ₀ ℓ₁) → (∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ) → hProp _
isGLB P _∧_ = ∧-GLB , ∧-GLB-prop
  where
    ∧-GLB = -- x ∧ y is a lower bound of {x, y}.
        ((x y    : ∣ P ∣ₚ) → [ (x ∧ y) ⊑[ P ] x ⊓ (x ∧ y) ⊑[ P ] y ])
        -- Given any other lower bound z of {x, y}, x ∧ y is _greater_ than that.
      × ((x y z  : ∣ P ∣ₚ) → [ (z ⊑[ P ] x ⊓ z ⊑[ P ] y) ⇒  z ⊑[ P ] (x ∧ y) ])

    ∧-GLB-prop : isProp ∧-GLB
    ∧-GLB-prop =
      isPropΣ
        (isPropΠ2 λ x y → is-true-prop ((x ∧ y) ⊑[ P ] x ⊓ (x ∧ y) ⊑[ P ] y)) λ _ →
        isPropΠ3 λ x y z → is-true-prop (z ⊑[ P ] x ⊓ z ⊑[ P ] y ⇒ z ⊑[ P ] (x ∧ y))

isLUB : (P : Poset ℓ₀ ℓ₁) → (Fam ℓ₂ ∣ P ∣ₚ → ∣ P ∣ₚ) → hProp _
isLUB {ℓ₂ = ℓ₂} P ⋁_ = ⋁-LUB , ⋁-LUB-prop
  where
    ⋁-LUB = ((U : Fam ℓ₂ ∣ P ∣ₚ) → [ ∀[ x ε U ] (x ⊑[ P ] ⋁ U) ])
          × ((U : Fam ℓ₂ ∣ P ∣ₚ) (x : _) → [ (∀[ y ε U ] (y ⊑[ P ] x)) ⇒ ⋁ U ⊑[ P ] x ])

    ⋁-LUB-prop : isProp ⋁-LUB
    ⋁-LUB-prop = isPropΣ
                   (λ ψ ϑ → funExt λ U →
                     is-true-prop (∀[ y ε U ] (y ⊑[ P ] ⋁ U)) (ψ U) (ϑ U)) λ _ →
                   isPropΠ λ U → isPropΠ λ x →
                     is-true-prop (∀[ y ε U ] (y ⊑[ P ] x) ⇒ (⋁ U) ⊑[ P ] x)

isDist : (P : Poset ℓ₀ ℓ₁)
       → (∣ P ∣ₚ → ∣ P ∣ₚ → ∣ P ∣ₚ)
       → (Fam ℓ₂ ∣ P ∣ₚ → ∣ P ∣ₚ)
       → hProp _
isDist {ℓ₂ = ℓ₂} P _⊓_ ⋁_ = ∧-dist-over-⋁ , ∧-dist-over-⋁-prop
  where
    open JoinSyntax ∣ P ∣ₚ ⋁_

    ∧-dist-over-⋁ = (x : ∣ P ∣ₚ) (U : Fam ℓ₂ ∣ P ∣ₚ) → x ⊓ (⋁ U) ≡ ⋁⟨ i ⟩ (x ⊓ (U $ i))

    ∧-dist-over-⋁-prop : isProp ∧-dist-over-⋁
    ∧-dist-over-⋁-prop p q = funExt₂ λ x U → carrier-is-set P _ _ (p x U) (q x U)

FrameAx : {A : Type ℓ₀} → RawFrameStr ℓ₁ ℓ₂ A → hProp _
FrameAx {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = A} (s@(_⊑_ , _) , ⊤ , _∧_ , ⋁_) =
  isTop P ⊤ ⊓ isGLB P _∧_ ⊓ isLUB P ⋁_ ⊓ isDist P _∧_ ⋁_
  where
    P : Poset ℓ₀ ℓ₁
    P = A , s

FrameStr : (ℓ₁ ℓ₂ : Level) → Type ℓ₀ → Type _
FrameStr ℓ₁ ℓ₂ A  = Σ[ s ∈ RawFrameStr ℓ₁ ℓ₂ A ] [ FrameAx s ]

Frame : (ℓ₀ ℓ₁ ℓ₂ : Level) → Type _
Frame ℓ₀ ℓ₁ ℓ₂ = Σ[ A ∈ Type ℓ₀ ] FrameStr ℓ₁ ℓ₂ A

-- Projection for the carrier set of a frame
-- i.e., the carrier set of the underlying poset.
∣_∣F : Frame ℓ₀ ℓ₁ ℓ₂ → Type ℓ₀
∣ A , _ ∣F = A

-- The underlying poset of a frame.
pos : Frame ℓ₀ ℓ₁ ℓ₂ → Poset ℓ₀ ℓ₁
pos (A , (P , _) , _) = A , P

-- Projections for the top element, meet, and join of a frame.

⊤[_] : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F
⊤[ _ , (_ , (⊤ , _)) , _ ] = ⊤

glb-of : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
glb-of (_ , (_ , _ , _⊓_ , _) , _) = _⊓_

syntax glb-of F x y = x ⊓[ F ] y

⋁[_]_ : (F : Frame ℓ₀ ℓ₁ ℓ₂) → Fam ℓ₂ ∣ F ∣F → ∣ F ∣F
⋁[ (_ , (_ , (_ , _ , ⋁_)) , _) ] U = ⋁ U

⊥[_] : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F
⊥[ F ] = ⋁[ F ] (𝟘 _ , λ ())

bin-join : (F : Frame ℓ₀ ℓ₁ ℓ₂) → ∣ F ∣F → ∣ F ∣F → ∣ F ∣F
bin-join {ℓ₂ = ℓ₂} F x y = ⋁[ F ] (Bool ℓ₂ , λ p → if p then x else y)

syntax bin-join F x y = x ∨[ F ] y

-- Projections for frame laws.

module _ (F : Frame ℓ₀ ℓ₁ ℓ₂) where
  private
    P = pos F

    _⊑_ : ∣ F ∣F → ∣ F ∣F → hProp ℓ₁
    x ⊑ y = x ⊑[ P ] y

    open JoinSyntax ∣ F ∣F (λ - → ⋁[ F ] -)

  ⊤[_]-top : (x : ∣ F ∣F) → [ x ⊑ ⊤[ F ] ]
  ⊤[_]-top = let (_ , _ , frame-str) = F in π₀ frame-str

  ⊓[_]-lower₀ : (x y : ∣ F ∣F) → [ (x ⊓[ F ] y) ⊑ x ]
  ⊓[_]-lower₀ = let (_ , _ , str) = F in λ x y → π₀ (π₀ (π₀ (π₁ str)) x y)


  ⊓[_]-lower₁ : (x y : ∣ F ∣F) → [ (x ⊓[ F ] y) ⊑ y ]
  ⊓[_]-lower₁ = let (_ , _ , str) = F in λ x y → π₁ (π₀ (π₀ (π₁ str)) x y)

  ⊓[_]-greatest : (x y z : ∣ F ∣F) → [ z ⊑ x ] → [ z ⊑ y ] → [ z ⊑ (x ⊓[ F ] y) ]
  ⊓[_]-greatest =
    let (_ , _ , str) = F in λ x y z z⊑x z⊑y → π₁ (π₀ (π₁ str)) x y z (z⊑x , z⊑y)

  ⋁[_]-upper : (U : Fam ℓ₂ ∣ F ∣F) (o : ∣ F ∣F) → o ε U → [ o ⊑ (⋁[ F ] U) ]
  ⋁[_]-upper = let (_ , _ , str) = F in π₀ (π₀ (π₁ (π₁ str)))

  ⋁[_]-least : (U : Fam ℓ₂ ∣ F ∣F) (x : ∣ F ∣F)
             → [ ∀[ y ε U ] (y ⊑ x) ] → [ (⋁[ F ] U) ⊑ x ]
  ⋁[_]-least = let (_ , _ , str) = F in π₁ (π₀ (π₁ (π₁ str)))

  ⊥[_]-bottom : (x : ∣ F ∣F) → [ ⊥[ F ] ⊑ x ]
  ⊥[_]-bottom x = ⋁[ _ ]-least x (λ a ())

  dist : (x : ∣ F ∣F) (U : Fam ℓ₂ ∣ F ∣F)
       → x ⊓[ F ] (⋁⟨ i ⟩ (U $ i)) ≡ ⋁⟨ i ⟩ (x ⊓[ F ] (U $ i))
  dist = let (_ , _ , str) = F in π₁ (π₁ (π₁ str))

  top-unique : (y : ∣ F ∣F) → ((x : ∣ F ∣F) → [ x ⊑ y ]) → y ≡ ⊤[ F ]
  top-unique y y-top = ⊑[ pos F ]-antisym y ⊤[ F ] (⊤[_]-top y) (y-top ⊤[ F ])

  ⊓-unique : (x y z : ∣ F ∣F)
           → [ z ⊑ x ] → [ z ⊑ y ] → ((w : ∣ F ∣F) → [ w ⊑ x ] → [ w ⊑ y ] → [ w ⊑ z ])
           → z ≡ x ⊓[ F ] y
  ⊓-unique x y z z⊑x z⊑y greatest =
    ⊑[ P ]-antisym z (x ⊓[ F ] y) (⊓[_]-greatest x y z z⊑x z⊑y) NTS
    where
      NTS : [ (x ⊓[ F ] y) ⊑ z ]
      NTS = greatest (x ⊓[ F ] y) (⊓[_]-lower₀ x y) (⊓[_]-lower₁ x y)

  ⋁-unique : (U : Fam ℓ₂ ∣ F ∣F) (z : ∣ F ∣F)
           → ((x : ∣ F ∣F) → x ε U → [ x ⊑ z ])
           → ((w : ∣ F ∣F) → ((o : ∣ F ∣F) → o ε U → [ o ⊑ w ]) → [ z ⊑ w ])
           → z ≡ ⋁[ F ] U
  ⋁-unique U z upper least =
    ⊑[ P ]-antisym z (⋁[ F ] U) (least (⋁[ F ] U) (⋁[_]-upper U)) NTS
    where
      NTS : [ (⋁[ F ] U) ⊑ z ]
      NTS = ⋁[_]-least U z upper

  x⊑y⇒x=x∧y : {x y : ∣ F ∣F}
            → [ x ⊑ y ] → x ≡ x ⊓[ F ] y
  x⊑y⇒x=x∧y {x} {y} x⊑y = ⊑[ pos F ]-antisym _ _ down up
    where
      down : [ x ⊑ (x ⊓[ F ] y) ]
      down = ⊓[_]-greatest x y x (⊑[_]-refl P x) x⊑y

      up : [ (x ⊓[ F ] y) ⊑ x ]
      up = ⊓[_]-lower₀ x y

  x⊑y⇒y=x∨y : {x y : ∣ F ∣F} → [ x ⊑ y ] → y ≡ x ∨[ F ] y
  x⊑y⇒y=x∨y {x} {y} x⊑y = ⊑[ pos F ]-antisym _ _ (⋁[_]-upper _ y (false , refl)) NTS
    where
      NTS : [ (x ∨[ F ] y) ⊑[ pos F ] y ]
      NTS = ⋁[_]-least _ y NTS₁
        where
          NTS₁ : [ ∀[ z ε _ ] (z ⊑[ pos F ] y) ]
          NTS₁ z (true  , p) = subst (λ - → [ - ⊑[ pos F ] y ]) p x⊑y 
          NTS₁ z (false , p) = subst (λ - → [ - ⊑[ pos F ] y ]) p (⊑[ pos F ]-refl y)


  x=x∧y⇒x⊑y : {x y : ∣ F ∣F}
            → x ≡ x ⊓[ F ] y → [ x ⊑ y ]
  x=x∧y⇒x⊑y {x} {y} eq = x ⊑⟨ ≡⇒⊑ P eq ⟩ x ⊓[ F ] y ⊑⟨ ⊓[_]-lower₁ x y ⟩ y ■
    where
      open PosetReasoning (pos F)

  x∧⊤=x : (x : ∣ F ∣F) → x ⊓[ F ] ⊤[ F ] ≡ x
  x∧⊤=x = sym ∘ x⊑y⇒x=x∧y ∘ ⊤[_]-top

  x∨⊥=x : (x : ∣ F ∣F) → ⊥[ F ] ∨[ F ] x ≡ x
  x∨⊥=x = sym ∘ x⊑y⇒y=x∨y ∘ ⊥[_]-bottom

  ∨-comm : (x y : ∣ F ∣F) → x ∨[ F ] y ≡ y ∨[ F ] x
  ∨-comm x y = ⊑[ pos F ]-antisym _ _ (Ψ x y) (Ψ y x) 
    where
      Ψ : (a b : ∣ F ∣F) → [ a ∨[ F ] b ⊑[ pos F ] b ∨[ F ] a ]
      Ψ a b = ⋁[_]-least _ (b ∨[ F ] a) NTS
        where
          NTS : [ ∀[ k ε (Bool ℓ₂ , (λ p → if p then a else b)) ] (k ⊑ (b ∨[ F ] a)) ]
          NTS z (true  , p) = subst (λ - → [ - ⊑ _ ]) p (⋁[_]-upper _ _ (false , refl))
          NTS z (false , p) = subst (λ - → [ - ⊑ _ ]) p (⋁[_]-upper _ _ (true  , refl))

  bin-dist : (x y z : ∣ F ∣F) → x ⊓[ F ] (y ∨[ F ] z) ≡ (x ⊓[ F ] y) ∨[ F ] (x ⊓[ F ] z)
  bin-dist x y z =
    x ⊓[ F ] (y ∨[ F ] z)               ≡⟨ dist x 𝒰  ⟩
    join-of (λ i → glb-of F x (𝒰 $ i))  ≡⟨ NTS       ⟩
    (x ⊓[ F ] y) ∨[ F ] (x ⊓[ F ] z)    ∎
    where
      𝒰 : Fam ℓ₂ ∣ F ∣F
      𝒰 = Bool ℓ₂ , λ p → if p then y else z

      NTS : ⋁⟨ b ⟩ (x ⊓[ F ] (𝒰 $ b)) ≡ (x ⊓[ F ] y) ∨[ F ] (x ⊓[ F ] z)
      NTS = cong (λ - → ⋁[ F ] (Bool ℓ₂ , -)) (funExt λ { true → refl ; false → refl })

  comm : (x y : ∣ F ∣F) → x ⊓[ F ] y ≡ y ⊓[ F ] x
  comm x y = ⊓-unique y x _ (⊓[_]-lower₁ x y) (⊓[_]-lower₀ x y) NTS
    where
      NTS = λ w w⊑y w⊑x → ⊓[_]-greatest x y w w⊑x w⊑y

  family-iff : {U V : Fam ℓ₂ ∣ F ∣F}
             → ((x : ∣ F ∣F) → (x ε U → x ε V) × (x ε V → x ε U))
             → ⋁[ F ] U ≡ ⋁[ F ] V
  family-iff {U = U} {V = V} h = ⋁-unique _ _ ub least
    where
      ub : (o : ∣ F ∣F) → o ε V → [ o ⊑ (⋁[ F ] U) ]
      ub o (i , p) =
        subst (λ - → [ - ⊑ _ ]) p (⋁[ _ ]-upper _ (π₁ (h (V $ i)) (i , refl)))

      least : (w : ∣ F ∣F)
            → ((o : ∣ F ∣F) → o ε V → [ o ⊑ w ])
            → [ (⋁[ F ] U) ⊑ w ]
      least w f = ⋁[ _ ]-least _ λ o oεU → f o (π₀ (h o) oεU)

  flatten : (I : Type ℓ₂) (J : I → Type ℓ₂) (f : (i : I) → J i → ∣ F ∣F)
          → ⋁[ F ] (Σ I J , uncurry f) ≡ ⋁[ F ] ⁅ ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ∣ i ∶ I ⁆
  flatten I J f = ⊑[ pos F ]-antisym _ _ down up
    where
      open PosetReasoning (pos F)

      LHS = ⋁[ F ] (Σ I J , uncurry f)
      RHS = ⋁[ F ] (I , (λ i → ⋁[ F ] (J i , f i)))

      down : [ LHS ⊑ RHS ]
      down = ⋁[_]-least _ _ isUB
        where
          isUB : (x : ∣ F ∣F) → x ε (Σ I J , uncurry f) → [ x ⊑ RHS ]
          isUB x ((i , j) , eq) =
              x                          ⊑⟨ ≡⇒⊑ (pos F) (sym eq)      ⟩
              f i j                      ⊑⟨ ⋁[_]-upper _ _ (j , refl) ⟩
              ⋁[ F ] (J i , λ - → f i -) ⊑⟨ ⋁[_]-upper _ _ (i , refl) ⟩
              RHS                        ■

      up : [ RHS ⊑ LHS ]
      up = ⋁[_]-least _ _ isUB
        where
          isUB : (x : ∣ F ∣F)
               → x ε ⁅ ⋁[ F ] (J i , f i) ∣ i ∶ I ⁆ → [ x ⊑ (⋁[ F ] (Σ I J , uncurry f)) ]
          isUB x (i , p) =
            x                          ⊑⟨ ≡⇒⊑ (pos F) (sym p)  ⟩
            ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ⊑⟨ ⋁[_]-least _ _ isUB′ ⟩
            ⋁[ F ] (Σ I J , uncurry f) ■
            where
              isUB′ : (z : ∣ F ∣F) → z ε ⁅ f i j ∣ j ∶ J i ⁆ → [ z ⊑ LHS ]
              isUB′ z (j , q) = ⋁[_]-upper _ _ ((i , j) , q)

  sym-distr : (U@(I , _) V@(J , _) : Fam ℓ₂ ∣ F ∣F)
            → (⋁⟨ i ⟩ (U $ i)) ⊓[ F ] (⋁⟨ i ⟩ (V $ i))
            ≡ ⋁[ F ] ⁅ (U $ i) ⊓[ F ] (V $ j) ∣ (i , j) ∶ (I × J) ⁆
  sym-distr U@(I , _) V@(J , _) =
    (⋁[ F ] U) ⊓[ F ] (⋁[ F ] V)
      ≡⟨ dist (⋁[ F ] U) V ⟩
    ⋁[ F ] ((λ - → (⋁[ F ] U) ⊓[ F ] -) ⟨$⟩ V)
      ≡⟨ cong (λ - → ⋁[ F ] (- ⟨$⟩ V)) NTS₀ ⟩
    ⋁[ F ] ((λ x → x ⊓[ F ] (⋁[ F ] U)) ⟨$⟩ V)
      ≡⟨ cong (λ - → ⋁[ F ] (- ⟨$⟩ V)) NTS₁ ⟩
    ⋁[ F ] ((λ x → ⋁[ F ] ((λ y → x ⊓[ F ] y) ⟨$⟩ U)) ⟨$⟩ V)
      ≡⟨ sym (flatten (index V) (λ _ → index U) λ j i →  (V $ j) ⊓[ F ] (U $ i))  ⟩
    ⋁[ F ] ⁅ (V $ j) ⊓[ F ] (U $ i) ∣ (j , i) ∶ (J × I) ⁆
      ≡⟨ family-iff NTS₂  ⟩
    ⋁[ F ] ⁅ (U $ i) ⊓[ F ] (V $ j) ∣ (i , j) ∶ (I × J) ⁆
      ∎
    where
      open PosetReasoning (pos F)

      NTS₀ : (λ - → (⋁[ F ] U) ⊓[ F ] -) ≡ (λ - → - ⊓[ F ] (⋁[ F ] U))
      NTS₀ = funExt λ x → comm (⋁[ F ] U) x

      NTS₁ : (λ - → - ⊓[ F ] (⋁[ F ] U)) ≡ (λ - → ⋁[ F ] ((λ y → - ⊓[ F ] y) ⟨$⟩ U))
      NTS₁ = funExt λ x → dist x U

      NTS₂ : _
      NTS₂ x = down , up
        where
          down : _
          down ((j , i) , eq) =
            subst
              (λ - → x ε (_ , -))
              (funExt (λ { (i′ , j′) → comm (V $ j′) (U $ i′) })) ((i , j) , eq)

          up : _
          up ((i , j) , eq) =
            subst
              (λ - → x ε (_ , -))
              (funExt (λ { (j′ , i′) → comm (U $ i′) (V $ j′) })) ((j , i) , eq)

isRawFrameHomo : (M : Σ[ A ∈ Type ℓ₀  ] RawFrameStr ℓ₁  ℓ₂ A)
                 (N : Σ[ B ∈ Type ℓ₀′ ] RawFrameStr ℓ₁′ ℓ₂ B)
               → let M-pos = pos-of-raw-frame M ; N-pos = pos-of-raw-frame N in
                 (M-pos ─m→ N-pos) → Type _
isRawFrameHomo M@(A , ps₀ , ⊤₀ , _∧₀_ , ⋁₀_) N@(B , ps₁ , ⊤₁ , _∧₁_ , ⋁₁_) (f , f-mono) =
  resp-⊤ × resp-∧ × resp-⋁
  where
    resp-⊤ : Type _
    resp-⊤ = f ⊤₀ ≡ ⊤₁

    resp-∧ : Type _
    resp-∧ = (x y : A) → f (x ∧₀ y) ≡ (f x) ∧₁ (f y)

    resp-⋁ : Type _
    resp-⋁ = (U : Fam _ A) → f (⋁₀ U) ≡ ⋁₁ ⁅ f x ∣ x ε U ⁆

isRawFrameHomo-prop : (M : Σ[ A ∈ Type ℓ₀  ] RawFrameStr ℓ₁  ℓ₂ A)
                      (N : Σ[ B ∈ Type ℓ₀′ ] RawFrameStr ℓ₁′ ℓ₂ B)
                    → let M-pos = pos-of-raw-frame M ; N-pos = pos-of-raw-frame N in
                      (f : M-pos ─m→ N-pos) → isProp (isRawFrameHomo M N f)
isRawFrameHomo-prop M N (f , f-mono) =
  isPropΣ (B-set _ _) λ _ →
  isPropΣ (λ x y → funExt₂ λ a b → B-set _ _ (x a b) (y a b) ) λ _ →
          λ _ _ → funExt λ x → B-set _ _ _ _
  where
    M-pos = pos-of-raw-frame M
    N-pos = pos-of-raw-frame N
    A-set = carrier-is-set M-pos
    B-set = carrier-is-set N-pos

-- Frame homomorphisms.
isFrameHomomorphism : (F : Frame ℓ₀ ℓ₁ ℓ₂) (G : Frame ℓ₀′ ℓ₁′ ℓ₂)
                    → (pos F ─m→ pos G) → Type _
isFrameHomomorphism (A , rs , _) (B , rs′ , _) = isRawFrameHomo (A , rs) (B , rs′)

isFrameHomomorphism-prop : (F : Frame ℓ₀ ℓ₁ ℓ₂) (G : Frame ℓ₀′ ℓ₁′ ℓ₂)
                         → (f : pos F ─m→ pos G) → isProp (isFrameHomomorphism F G f)
isFrameHomomorphism-prop (A , s , _) (B , s′ , _) = isRawFrameHomo-prop (A , s) (B , s′)

_─f→_ : Frame ℓ₀ ℓ₁ ℓ₂ → Frame ℓ₀′ ℓ₁′ ℓ₂ → Type _
_─f→_ {ℓ₂ = ℓ₂} F G = Σ[ f ∈ (pos F ─m→ pos G) ] (isFrameHomomorphism F G f)

_$f_ : {F : Frame ℓ₀ ℓ₁ ℓ₂} {G : Frame ℓ₀′ ℓ₁′ ℓ₂} → F ─f→ G → ∣ F ∣F → ∣ G ∣F
(f , _) $f x = f $ₘ x

isFrameIso : {F : Frame ℓ₀ ℓ₁ ℓ₂} {G : Frame ℓ₀′ ℓ₁′ ℓ₂} → (F ─f→ G) → Type _
isFrameIso {F = F} {G} ((f , _) , _) =
  Σ[ ((g , _) , _) ∈ (G ─f→ F) ] section f g × retract f g

isFrameIso-prop : {F : Frame ℓ₀ ℓ₁ ℓ₂} {G : Frame ℓ₀′ ℓ₁′ ℓ₂}
                → (f : F ─f→ G) → isProp (isFrameIso {F = F} {G} f)
isFrameIso-prop {F = F} {G} ((f , _) , _) (g₀h , sec₀ , ret₀) (g₁h , sec₁ , ret₁) =
  Σ≡Prop NTS₀ NTS₁
  where
    g₀ = _$f_ {F = G} {F} g₀h
    g₁ = _$f_ {F = G} {F} g₁h

    NTS₀ : (((g , _) , _) : G ─f→ F) → isProp (section f g × retract f g)
    NTS₀ ((g , _) , g-homo) =
      isPropΣ (λ s s′ → funExt λ x → carrier-is-set (pos G) _ _ (s x) (s′ x)) λ _ r r′ →
      funExt λ y → carrier-is-set (pos F) _ _ (r y) (r′ y)

    g₀~g₁ : g₀ ~ g₁
    g₀~g₁ x = g₀ x          ≡⟨ cong g₀ (sym (sec₁ x)) ⟩
              g₀ (f (g₁ x)) ≡⟨ ret₀ (g₁ x)            ⟩
              g₁ x          ∎

    NTS₁ : g₀h ≡ g₁h
    NTS₁ = Σ≡Prop
             (isFrameHomomorphism-prop G F)
             (forget-mono (pos G) (pos F) (π₀ g₀h) (π₀ g₁h) (funExt g₀~g₁))

_≅f_ : (F : Frame ℓ₀ ℓ₁ ℓ₂) (G : Frame ℓ₀′ ℓ₁′ ℓ₂) → Type _
F ≅f G = Σ[ f ∈ F ─f→ G ] isFrameIso {F = F} {G} f

-- An element of the poset is like a finite observation whereas an element of the
-- frame of downward closed posets is like a general observation.

-- The set of downward-closed subsets of a poset forms a frame.
DCPoset : (P : Poset ℓ₀ ℓ₁) → Poset (ℓ-max (ℓ-suc ℓ₀) ℓ₁) ℓ₀
DCPoset {ℓ₀ = ℓ₀} P = 𝔻 , _<<_ , 𝔻-set , <<-refl , <<-trans  , <<-antisym
  where
    𝔻     = DCSubset     P
    𝔻-set = DCSubset-set P

    _<<_ : 𝔻 → 𝔻 → hProp ℓ₀
    _<<_ (S , _) (T , _) = S ⊆ T

    abstract
      <<-refl : [ isReflexive _<<_ ]
      <<-refl (U , U-down) x xεU = xεU

      <<-trans : [ isTransitive _<<_ ]
      <<-trans _ _ _ S<<T T<<U x xεS = T<<U x (S<<T x xεS)

      <<-antisym : [ isAntisym 𝔻-set _<<_ ]
      <<-antisym X Y S⊆T T⊆S =
        Σ≡Prop (is-true-prop ∘ isDownwardsClosed P) (⊆-antisym S⊆T T⊆S)

-- The set of downward-closed subsets of a poset forms a frame.
DCFrame : (P : Poset ℓ₀ ℓ₁) → Frame (ℓ-max (ℓ-suc ℓ₀) ℓ₁) ℓ₀ ℓ₀
DCFrame {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} (X , P) =
    𝔻
  , (strₚ 𝔻ₚ , ⊤ , (_∧_ , ⋁_))
  , ⊤-top
  , ( (λ x y → ⊓-lower₀ x y , ⊓-lower₁ x y)
    , λ { x y z (z⊑x , z⊑y) → ⊓-greatest x y z z⊑x z⊑y })
  , (⊔-upper , ⊔-least)
  , distr
  where
    𝔻ₚ = DCPoset (X , P)
    𝔻  = ∣ 𝔻ₚ ∣ₚ

    -- Function that forget the downwards-closure information.
    ∣_∣𝔻 : 𝔻 → 𝒫 X
    ∣ S , _ ∣𝔻 = S

    ⊤ = (λ _ → Unit ℓ₀ , Unit-prop) , λ _ _ _ _ → tt

    ∩-down : (S T : 𝒫 X)
           → [ isDownwardsClosed (X , P) S ]
           → [ isDownwardsClosed (X , P) T ]
           → [ isDownwardsClosed (X , P) (S ∩ T) ]
    ∩-down S T S↓ T↓ x y x∈S∩T y⊑x = S↓ x y (π₀ x∈S∩T) y⊑x , T↓ x y (π₁ x∈S∩T) y⊑x

    _∧_ : 𝔻 → 𝔻 → 𝔻
    (S , S-dc) ∧ (T , T-dc) = (S ∩ T) , ∩-down S T S-dc T-dc

    ⊤-top : (D : 𝔻) → [ D ⊑[ 𝔻ₚ ] ⊤ ]
    ⊤-top D _ _ = tt

    -- Given a family U over 𝔻 and some x : X, `in-some-set U x` holds iff there is some
    -- set S among U such that x ∈ S.
    in-some-set-of : (U : Fam ℓ₀ 𝔻) → X → Type ℓ₀
    in-some-set-of U x = Σ[ i ∈ index U ] [ x ∈ ∣ U $ i ∣𝔻 ]

    ⋁_ : Fam ℓ₀ 𝔻 → 𝔻
    ⋁ U = (λ x → ∥ in-some-set-of U x ∥ , ∥∥-prop _) , ⊔U↓
      where
        NTS : (x y : X)
            → [ y ⊑[ (X , P) ] x ] → in-some-set-of U x → ∥ in-some-set-of U y ∥
        NTS x y y⊑x (i , x∈Uᵢ) = ∣ i , π₁ (U $ i) x y x∈Uᵢ y⊑x ∣

        ⊔U↓ : [ isDownwardsClosed (X , P) (λ x → ∥ in-some-set-of U x ∥ , ∥∥-prop _) ]
        ⊔U↓ x y ∣p∣ y⊑x = ∥∥-rec (∥∥-prop _) (NTS x y y⊑x) ∣p∣

    open JoinSyntax 𝔻 ⋁_

    ⊔-upper : (U : Fam ℓ₀ 𝔻) (D : 𝔻) → D ε U → [ D ⊑[ 𝔻ₚ ] (⋁ U) ]
    ⊔-upper U D DεS@(i , p) x x∈D = ∣ i , subst (λ V → [ ∣ V ∣𝔻 x ]) (sym p) x∈D ∣

    ⊔-least : (U : Fam ℓ₀ 𝔻) (z : 𝔻) → [ ∀[ x ε U ] (x ⊑[ 𝔻ₚ ] z) ] → [ (⋁ U) ⊑[ 𝔻ₚ ] z ]
    ⊔-least U D φ x x∈⊔S = ∥∥-rec (∈-prop ∣ D ∣𝔻) NTS x∈⊔S
      where
        NTS : in-some-set-of U x → [ x ∈ ∣ D ∣𝔻 ]
        NTS (i , x∈Uᵢ) = φ (U $ i) (i , refl) x x∈Uᵢ

    ⊓-lower₀ : (U V : 𝔻) → [ (U ∧ V) ⊑[ 𝔻ₚ ] U ]
    ⊓-lower₀ _ _ _ (x∈U , _) = x∈U

    ⊓-lower₁ : (U V : 𝔻) → [ (U ∧ V) ⊑[ 𝔻ₚ ] V ]
    ⊓-lower₁ _ _ _ (_ , x∈V) = x∈V

    ⊓-greatest : (U V W : 𝔻) → [ W ⊑[ 𝔻ₚ ] U ] → [ W ⊑[ 𝔻ₚ ] V ] → [ W ⊑[ 𝔻ₚ ] (U ∧ V) ]
    ⊓-greatest U V W W<<U W<<V x x∈W = (W<<U x x∈W) , (W<<V x x∈W)

    distr : (U : 𝔻) (V : Fam ℓ₀ 𝔻) → U ∧ (⋁ V) ≡ ⋁⟨ i ⟩ (U ∧ (V $ i))
    distr U V@(I , _) = ⊑[ 𝔻ₚ ]-antisym _ _ down up
      where
        LHS = ∣ U ∧ (⋁ V) ∣𝔻
        RHS = ∣ ⋁⟨ i ⟩ (U ∧ (V $ i)) ∣𝔻

        down : [ LHS ⊆ RHS ]
        down x (x∈D , x∈⊔U) =
          ∥∥-rec (∥∥-prop _) (λ { (i , x∈Uᵢ) → ∣ i , x∈D , x∈Uᵢ ∣ }) x∈⊔U

        up : [ RHS ⊆ LHS ]
        up x = ∥∥-rec (is-true-prop (x ∈ LHS)) φ
          where
            φ : in-some-set-of ⁅ U ∧ (V $ i) ∣ i ∶ I ⁆ x → [ ∣ U ∣𝔻 x ] × [ ∣ ⋁ V ∣𝔻 x ]
            φ (i , x∈D , x∈Uᵢ) = x∈D , ∣ i , x∈Uᵢ ∣

-- Frames form an SNS.

-- Similar to the poset case, we start by expressing what it means for an equivalence to
-- preserve the structure of a frame
isARawHomoEqv : {ℓ₁ ℓ₂ : Level} (M N : Σ (Type ℓ₀) (RawFrameStr ℓ₁ ℓ₂))
              → π₀ M ≃ π₀ N
              → Type _
isARawHomoEqv {ℓ₂ = ℓ₂} M N e@(f , _) =
  Σ[ f-mono ∈ isMonotonic M-pos N-pos f ]
  Σ[ g-mono ∈ isMonotonic N-pos M-pos g ]
   isRawFrameHomo M N (f , f-mono) × isRawFrameHomo N M (g , g-mono)
  where
    M-pos = pos-of-raw-frame M
    N-pos = pos-of-raw-frame N
    g     = equivFun (invEquiv e)

pos-of : Σ (Type ℓ₀) (RawFrameStr ℓ₁ ℓ₂) → Σ (Type ℓ₀) (Order ℓ₁)
pos-of (A , ((RPS , _) , _)) = (A , RPS)

top-of : (F : Σ (Type ℓ₀) (RawFrameStr ℓ₁ ℓ₂)) → π₀ F
top-of (_ , _ , ⊤ , _) = ⊤

-- Frame univalence

RF-is-SNS : SNS {ℓ₀} (RawFrameStr ℓ₁ ℓ₂) isARawHomoEqv
RF-is-SNS {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {X = A}
          F@(s@(_⊑₀_ , _) , ⊤₀ , _⊓₀_ , ⋁₀)
          G@(t@(_⊑₁_ , _) , ⊤₁ , _⊓₁_ , ⋁₁) =
  isoToEquiv (iso f g sec-f-g ret-f-g)
  where
    C = RawFrameStr ℓ₁ ℓ₂ A

    A-set₀ = carrier-is-set (A , s)

    PS-A = π₀ s
    PS-B = π₀ t

    F-pos = pos-of-raw-frame (A , F)
    G-pos = pos-of-raw-frame (A , G)

    f : isARawHomoEqv (A , F) (A , G) (idEquiv A) → F ≡ G
    f (mono , mono′ , (eq-⊤ , ⊓₀~⊓₁ , ⋁₀~⋁₁) , k , h) =
      s , ⊤₀ , _⊓₀_ , ⋁₀   ≡⟨ cong (λ - → (s , - , _⊓₀_ , ⋁₀))           eq-⊤ ⟩
      s , ⊤₁ , _⊓₀_ , ⋁₀   ≡⟨ cong {B = λ _ → C} (λ - → s , ⊤₁ , - , ⋁₀) ⊓-eq ⟩
      s , ⊤₁ , _⊓₁_ , ⋁₀   ≡⟨ cong {B = λ _ → C} (λ - → s , _ , _ , -)   ⋁-eq ⟩
      s , ⊤₁ , _⊓₁_ , ⋁₁   ≡⟨ cong {B = λ _ → C} (λ - → - , _ , _ , _)   eq   ⟩
      t , ⊤₁ , _⊓₁_ , ⋁₁   ∎
      where
        eq : s ≡ t
        eq = Σ≡Prop
               (is-true-prop ∘ PosetAx A)
               (funExt₂ λ x y → ⇔toPath (mono x y) (mono′ x y))

        ⊓-eq : _⊓₀_ ≡ _⊓₁_
        ⊓-eq = funExt₂ ⊓₀~⊓₁

        ⋁-eq : ⋁₀ ≡ ⋁₁
        ⋁-eq = funExt ⋁₀~⋁₁

    g : F ≡ G → isARawHomoEqv (A , F) (A , G) (idEquiv A)
    g p = subst (λ - → isARawHomoEqv (A , F) (A , -) (idEquiv A)) p id-iso
      where
        id-iso : isARawHomoEqv (A , F) (A , F) (idEquiv A)
        id-iso = (λ x y x⊑y → x⊑y)
               , (λ x y p → p)
               , (refl , ((λ _ _ → refl) , λ U → refl))
               , refl , (λ _ _ → refl) , λ _ → refl

    sec-f-g : section f g
    sec-f-g p = RawFrameStr-set ℓ₁ ℓ₂ A F G (f (g p)) p

    ret-f-g : retract f g
    ret-f-g a@(mono , mono′ , q , r) = Σ≡Prop NTS₀ NTS₁
      where
        NTS₀ : _
        NTS₀ _ = isPropΣ (isMonotonic-prop G-pos F-pos (id A)) λ _ →
                 isPropΣ NTS₀′ λ _ → NTS₀′′
          where
            NTS₀′ : _
            NTS₀′ = isRawFrameHomo-prop (A , F) (A , G) (id A , λ x y x⊑y → mono x y x⊑y)
            NTS₀′′ : _
            NTS₀′′ = isRawFrameHomo-prop (A , G) (A , F) (id A , mono′)

        NTS₁ : g (f (mono , mono′ , q , r)) .π₀ ≡ mono
        NTS₁ = isMonotonic-prop F-pos G-pos (id A) _ _

-- A predicate expressing that an equivalence between the underlying types of two frames
-- is frame-homomorphic.
isHomoEqv : (F G : Frame ℓ₀ ℓ₁ ℓ₂) → π₀ F ≃ π₀ G → Type _
isHomoEqv {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} (A , (s , _)) (B , (t , _)) = isARawHomoEqv (A , s) (B , t)

-- We collect all frame-homomorphic equivalences between two frames in the following type.
_≃f_ : (F G : Frame ℓ₀ ℓ₁ ℓ₂) → Type _
F ≃f G = Σ[ e ∈ ∣ F ∣F ≃ ∣ G ∣F ] isHomoEqv F G e

isHomoEqv-prop : (F G : Frame ℓ₀ ℓ₁ ℓ₂) → (e : ∣ F ∣F ≃ ∣ G ∣F) → isProp (isHomoEqv F G e)
isHomoEqv-prop F G e@(f , _) =
  isPropΣ (isMonotonic-prop (pos F) (pos G) f) λ f-mono →
  isPropΣ (isMonotonic-prop (pos G) (pos F) g) λ g-mono →
  isPropΣ (isRawFrameHomo-prop (∣ F ∣F , F-rs) (∣ G ∣F , G-rs) (f , f-mono)) λ _ →
  isPropΣ (carrier-is-set (pos F) _ _) λ _ →
  isPropΣ (λ p q → funExt₂ λ x y → carrier-is-set (pos F) _ _ (p x y) (q x y)) λ _ →
          λ p q → funExt λ U → carrier-is-set (pos F) _ _ (p U) (q U)
  where
    F-rs : RawFrameStr _ _ ∣ F ∣F
    F-rs = π₀ (π₁ F)
    G-rs : RawFrameStr _ _ ∣ G ∣F
    G-rs = π₀ (π₁ G)
    g = equivFun (invEquiv e)

-- Notice that ≃f is equivalent to ≅f.
≃f≃≅f : (F G : Frame ℓ₀ ℓ₁ ℓ₂) → (F ≃f G) ≃ (F ≅f G)
≃f≃≅f F G = isoToEquiv (iso to from sec ret)
  where
    to : F ≃f G → F ≅f G
    to (e@(f , _) , (f-mono , g-mono , f-homo , g-homo)) = f₀ , f₀-frame-iso
      where
        g = equivFun (invEquiv e)

        f₀ : F ─f→ G
        f₀ = (f , f-mono) , f-homo

        g₀ : G ─f→ F
        g₀ = (g , g-mono) , g-homo

        f₀-frame-iso : isFrameIso {F = F} {G} f₀
        f₀-frame-iso = g₀ , Iso.rightInv (equivToIso e) , Iso.leftInv (equivToIso e)

    from : F ≅f G → F ≃f G
    from (((f , f-mono) , f-homo) , ((g , g-mono) , g-homo) , sec , ret) =
      isoToEquiv (iso f g sec ret) , f-mono , g-mono , f-homo , g-homo

    sec : section to from
    sec (f , g , sec , ret) = Σ≡Prop (isFrameIso-prop {F = F} {G = G}) refl

    ret : retract to from
    ret (e , f-homo , g-homo) = Σ≡Prop (isHomoEqv-prop F G) (Σ≡Prop isPropIsEquiv refl)

FrameAx-props : (A : Type ℓ₀) (str : RawFrameStr ℓ₁ ℓ₂ A)
                   → isProp [ FrameAx str ]
FrameAx-props A str = is-true-prop (FrameAx str)

frame-is-SNS : SNS {ℓ₀} (FrameStr ℓ₁ ℓ₂) isHomoEqv
frame-is-SNS {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} =
  UnivalentStr→SNS (FrameStr ℓ₁ ℓ₂) isHomoEqv frame-forms-univ-str
  where
    NTS : (A : Type ℓ) (rs : RawFrameStr ℓ₁ ℓ₂ A) → isProp [ FrameAx rs ]
    NTS _ rs = isProp[] (FrameAx rs)

    frame-forms-univ-str : UnivalentStr (FrameStr ℓ₁ ℓ₂) isHomoEqv
    frame-forms-univ-str =
      axiomsUnivalentStr _ NTS (SNS→UnivalentStr isARawHomoEqv RF-is-SNS)

frame-is-univ-str : UnivalentStr {ℓ₀} (FrameStr ℓ₁ ℓ₂) isHomoEqv
frame-is-univ-str = SNS→UnivalentStr isHomoEqv frame-is-SNS

-- Similar to the poset case, this is sufficient to establish that the category of frames
-- is univalent

≃f≃≡ : (F G : Frame ℓ₀ ℓ₁ ℓ₂) → (F ≃f G) ≃ (F ≡ G)
≃f≃≡ = SIP frame-is-univ-str

-- However, there are two minor issues with this.
--
--   1. We do not have to talk about equivalences as we are talking about sets;
--      isomorphisms are well-behaved in our case as we are dealing with sets.
--
--  2. We do not have to require the frame data to be preserved. We can show that any
--     poset isomorphism preserves the frame operators.
--
-- We will therefore strengthen our result to work with the notion of poset isomorphism.

-- We start by showing the equivalence between ≃f and ≅ₚ.

≃f≃≅ₚ : (F G : Frame ℓ₀ ℓ₁ ℓ₂) → (pos F ≅ₚ pos G) ≃ (F ≃f G)
≃f≃≅ₚ F G = isoToEquiv (iso from to ret-to-from sec-to-from)
  where
    to : F ≃f G → pos F ≅ₚ pos G
    to (e@(f , _) , f-mono , g-mono , _) =
      (f , f-mono) , (g , g-mono) , retEq e , secEq e
      where
        g = equivFun (invEquiv e)

    from : pos F ≅ₚ pos G → F ≃f G
    from ((f , f-mono) , (g , g-mono) , sec , ret) =
        isoToEquiv (iso f g sec ret)
      , f-mono , g-mono , (resp-⊤ , resp-∧ , resp-⋁) , (g-resp-⊤ , g-resp-∧ , g-resp-⋁)
      where
        open PosetReasoning (pos G)

        resp-⊤ : f ⊤[ F ] ≡ ⊤[ G ]
        resp-⊤ = top-unique G (f ⊤[ F ]) NTS
          where
            NTS : (x : ∣ G ∣F) → [ x ⊑[ pos G ] (f ⊤[ F ]) ]
            NTS x = x        ⊑⟨ ≡⇒⊑ (pos G) (sym (sec x))              ⟩
                    f (g x)  ⊑⟨ f-mono (g x) ⊤[ F ] (⊤[ F ]-top (g x)) ⟩
                    f ⊤[ F ] ■

        g-resp-⊤ : g ⊤[ G ] ≡ ⊤[ F ]
        g-resp-⊤ = g ⊤[ G ] ≡⟨ cong g (sym resp-⊤) ⟩ g (f ⊤[ F ]) ≡⟨ ret ⊤[ F ] ⟩ ⊤[ F ] ∎

        resp-∧ : (x y : ∣ F ∣F) → f (x ⊓[ F ] y) ≡ (f x) ⊓[ G ] (f y)
        resp-∧ x y = ⊓-unique G (f x) (f y) (f (x ⊓[ F ] y)) NTS₀ NTS₁ NTS₂
          where
            NTS₀ : [ f (x ⊓[ F ] y) ⊑[ pos G ] (f x) ]
            NTS₀ = f-mono (x ⊓[ F ] y) x (⊓[ F ]-lower₀ x y)

            NTS₁ : [ f (x ⊓[ F ] y) ⊑[ pos G ] (f y) ]
            NTS₁ = f-mono (x ⊓[ F ] y) y (⊓[ F ]-lower₁ x y)

            NTS₂ : (w : ∣ G ∣F)
                 → [ w ⊑[ pos G ] f x ]
                 → [ w ⊑[ pos G ] f y ]
                 → [ w ⊑[ pos G ] f (x ⊓[ F ] y) ]
            NTS₂ w w⊑fx w⊑fy = w              ⊑⟨ ≡⇒⊑ (pos G) (sym (sec w)) ⟩
                               f (g w)        ⊑⟨ f-mono _ _ gw⊑x∧y         ⟩
                               f (x ⊓[ F ] y) ■
              where
                gw⊑x : [ g w ⊑[ pos F ] x ]
                gw⊑x = subst (λ - → [ g w ⊑[ pos F ] - ]) (ret x) (g-mono w (f x) w⊑fx)

                gw⊑y : [ g w ⊑[ pos F ] y ]
                gw⊑y = subst (λ - → [ g w ⊑[ pos F ] - ]) (ret y) (g-mono w (f y) w⊑fy)

                gw⊑x∧y : [ g w ⊑[ pos F ] (x ⊓[ F ] y) ]
                gw⊑x∧y = ⊓[ F ]-greatest x y (g w) gw⊑x gw⊑y

        g-resp-∧ : (x y : ∣ G ∣F) → g (x ⊓[ G ] y) ≡ (g x) ⊓[ F ] (g y)
        g-resp-∧ x y =
          g (x ⊓[ G ] y)             ≡⟨ cong (λ - → g (- ⊓[ G ] y)) (sym (sec x)) ⟩
          g (f (g x) ⊓[ G ] y)       ≡⟨ cong (λ - → g (_ ⊓[ G ] -)) (sym (sec y)) ⟩
          g (f (g x) ⊓[ G ] f (g y)) ≡⟨ cong g (sym (resp-∧ (g x) (g y)))         ⟩
          g (f (g x ⊓[ F ] g y))     ≡⟨ ret (g x ⊓[ F ] g y)                      ⟩
          g x ⊓[ F ] g y             ∎

        resp-⋁ : (U : Fam _ ∣ F ∣F) → f (⋁[ F ] U) ≡ (⋁[ G ] ⁅ f x ∣ x ε U ⁆)
        resp-⋁ U = ⋁-unique G ⁅ f x ∣ x ε U ⁆ (f (⋁[ F ] U)) NTS₀ NTS₁
          where
            NTS₀ : (x : ∣ G ∣F) → x ε ⁅ f y ∣ y ε U ⁆ → [ x ⊑[ pos G ] f (⋁[ F ] U) ]
            NTS₀ x (i , p) = x                    ⊑⟨ ≡⇒⊑ (pos G) (sym (sec _)) ⟩
                             f (g x)              ⊑⟨ f-mono _ _ gx⊑f⋁U         ⟩
                             f (g (f (⋁[ F ] U))) ⊑⟨ ≡⇒⊑ (pos G) (sec _)       ⟩
                             f (⋁[ F ] U)         ■
              where
                gx⊑f⋁U : [ g x ⊑[ pos F ] (g (f (⋁[ F ] U))) ]
                gx⊑f⋁U =
                  subst
                    (λ - → [ rel (pos F) (g x) - ])
                    (sym (ret (⋁[ F ] U)))
                    (⋁[ F ]-upper U (g x) (subst (λ - → g - ε U) p (i , (sym (ret _)))))

            NTS₁ : (w : ∣ G ∣F)
                 → ((o : ∣ G ∣F) → o ε ⁅ f x ∣ x ε U ⁆ → [ o ⊑[ pos G ] w ])
                 → [ f (⋁[ F ] U) ⊑[ pos G ] w ]
            NTS₁ w h = f (⋁[ F ] U) ⊑⟨ f⋁U⊑fgw ⟩ f (g w) ⊑⟨ ≡⇒⊑ (pos G) (sec _) ⟩ w ■
              where
                gf⋁U⊑gw : [ g (f (⋁[ F ] U)) ⊑[ pos F ] g w ]
                gf⋁U⊑gw = subst
                            (λ - → [ - ⊑[ pos F ] g w ])
                            (sym (ret _))
                            (⋁[ F ]-least U (g w) NTS′)
                  where
                    NTS′ : [ ∀[ u ε U ] (u ⊑[ pos F ] (g w)) ]
                    NTS′ u (i , p) =
                      subst (λ - → [ - ⊑[ pos F ] (g w) ]) p
                        (subst
                           (λ - → [ - ⊑[ pos F ] g w ])
                           (ret _)
                           (g-mono _ _ (h (f (π₁ U i)) (i , refl))))

                f⋁U⊑fgw : [ f (⋁[ F ] U) ⊑[ pos G ] f (g w) ]
                f⋁U⊑fgw = f-mono _ _ (subst (λ - → [ - ⊑[ pos F ] g w ]) (ret _) gf⋁U⊑gw)

        g-resp-⋁ : (U : Fam _ ∣ G ∣F) → g (⋁[ G ] U) ≡ ⋁[ F ] ⁅ g x ∣ x ε U ⁆
        g-resp-⋁ U =
          g (⋁[ G ] U)                   ≡⟨ cong (λ - → g (⋁[ G ] (π₀ U , -))) NTS ⟩
          g (⋁[ G ] ⁅ f (g x) ∣ x ε U ⁆) ≡⟨ cong g (sym (resp-⋁ ⁅ g x ∣ x ε U ⁆))  ⟩
          g (f (⋁[ F ] ⁅ g x ∣ x ε U ⁆)) ≡⟨ ret (⋁[ F ] ⁅ g x ∣ x ε U ⁆)           ⟩
          ⋁[ F ] ⁅ g x ∣ x ε U ⁆         ∎
          where
            NTS : π₁ U ≡ f ∘ g ∘ π₁ U
            NTS = funExt λ x → sym (sec (π₁ U x))

    sec-to-from : section to from
    sec-to-from is@((f , f-mono) , ((g , g-mono) , sec , ret)) =
      Σ≡Prop
        (isPosetIso-prop (pos F) (pos G))
        (forget-mono (pos F) (pos G) (f , f-mono) (π₀ (to (from is))) refl)

    ret-to-from : retract to from
    ret-to-from (eqv , eqv-homo) =
      Σ≡Prop (isHomoEqv-prop F G ) (Σ≡Prop isPropIsEquiv refl)

-- Now that we have this result, we can move on to show that given two frames F and G,
-- (pos F) ≅ₚ (pos G) is equivalent to F ≡ G.

≅ₚ≃≡ : (F G : Frame ℓ₀ ℓ₁ ℓ₂) → (pos F ≅ₚ pos G) ≃ (F ≡ G)
≅ₚ≃≡ F G = pos F ≅ₚ pos G ≃⟨ ≃f≃≅ₚ F G ⟩ F ≃f G ≃⟨ ≃f≃≡ F G ⟩ F ≡ G 𝔔𝔈𝔇

≅ₚ≃≅f : (F G : Frame ℓ₀ ℓ₁ ℓ₂) → (pos F ≅ₚ pos G) ≃ (F ≅f G)
≅ₚ≃≅f F G = pos F ≅ₚ pos G ≃⟨ ≃f≃≅ₚ F G ⟩ F ≃f G ≃⟨ ≃f≃≅f F G ⟩ F ≅f G 𝔔𝔈𝔇
