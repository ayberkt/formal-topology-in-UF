```
{-# OPTIONS --cubical --safe #-}

module UniversalProperty where

open import Basis
open import Frame
open import Poset
open import FormalTopology    renaming (pos to pos′)
open import CoverFormsNucleus

compr : {X : Type ℓ₀} {Y : Type ℓ₁} → (g : X → Y) → 𝒫 X → Fam ℓ₀ Y
compr g U = (index ⟪ U ⟫) , g ∘ (_$_ ⟪ U ⟫)

syntax compr (λ x → e) ℱ = ⁅ e ∣ x ∈ ℱ ⁆

module _ (F : FormalTopology ℓ₀ ℓ₀) where

  P       = pos′ F
  F↓      = DCFrame P
  P↓      = pos F↓
  _⊑_     = λ (x y : stage F) → x ⊑[ P ] y

  open NucleusFrom F
```

## Representation

```
  represents : (R : Frame (suc ℓ₀) ℓ₀ ℓ₀) → (P ─m→ pos R) → Type ℓ₀
  represents R (f , _) =
    (a : ∣ P ∣ₚ) (b : exp F a) →
      [ f a ⊑[ pos R ] ⋁[ R ] ⁅ f (next F c) ∣ c ∶ outcome F b ⁆ ]
```

By the way, note that the converse is always true.

```
  represents⁻¹ : (R : Frame (suc ℓ₀) ℓ₀ ℓ₀) → (m : P ─m→ pos R)
                  → Type ℓ₀
  represents⁻¹ R (f , _) =
    (a : ∣ P ∣ₚ) (b : exp F a) →
      [ (⋁[ R ] ⁅ f (next F c) ∣ c ∶ outcome F b ⁆) ⊑[ pos R ] (f a) ]

  conv : (R : Frame (suc ℓ₀) ℓ₀ ℓ₀) (f : P ─m→ pos R) → represents⁻¹ R f
  conv R (f , f-mono) a b =
    ⋁[ R ]-least (⁅ f (next F c) ∣ c ∶ outcome F b ⁆) (f a) NTS
    where
      NTS : [ ∀[ a′ ε ⁅ f (next F c) ∣ c ∶ outcome F b ⁆ ] (a′ ⊑[ pos R ] f a) ]
      NTS a′ (i , eq) = subst (λ - → [ rel (pos R) - (f a) ]) eq NTS′
        where
          NTS′ : [ f (next F i) ⊑[ pos R ] f a ]
          NTS′ = f-mono (next F i) a (mono F a b i)
```

## Flatness

```
  _↓_↓ : ∣ P ∣ₚ → ∣ P ∣ₚ → 𝒫 ∣ P ∣ₚ
  _↓_↓ a b = λ - → - ⊑[ P ] a ⊓ - ⊑[ P ] b

  isFlat : (F : Frame (suc ℓ₀) ℓ₀ ℓ₀) → (m : P ─m→ pos F) → Type (suc ℓ₀)
  isFlat F (f , _) = (⊤[ F ] ≡ ⋁[ F ] ⁅ f a ∣ a ∶ ∣ P ∣ₚ ⁆)
                   × ((a b : ∣ P ∣ₚ) → f a ⊓[ F ] f b ≡ ⋁[ F ] (f ⟨$⟩ ⟪ a ↓ b ↓ ⟫))
```

## The universal property

Statement.

```
  universal-prop : Type (suc (suc ℓ₀))
  universal-prop =
    (R : Frame (suc ℓ₀) ℓ₀ ℓ₀) (f : P ─m→ pos R) → isFlat R f → represents R f →
      isContr (Σ[ g ∈ (L ─f→ R) ] (_∘m_ {P = P} {Q = pos L} {R = pos R} (π₀ g) ηm) ≡ f)
```

Before the proof we will need some lemmas.

```
  cover+ : {x y : ∣ P ∣ₚ} ((U , _) : ∣ F↓ ∣F) → [ x ∈ ⦅ η y ⦆ ] → [ y ∈ U ] → x ◀ U
  cover+ {y = y} (_ , U-dc) x∈ηy y∈U = lem₄ _ _ (λ z z⊑y → dir (U-dc y z y∈U z⊑y)) _ x∈ηy
```

```
  main-lemma : (𝔘 : ∣ L ∣F) → 𝔘 ≡ ⋁[ L ] ⁅ η u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆
  main-lemma 𝔘@((U , U-dc) , U-fix) = ⊑[ pos L ]-antisym _ _ down up
    where
      down : [ 𝔘 ⊑[ pos L ] (⋁[ L ] ⁅ η x ∣ x ∈ U ⁆) ]
      down x xεU = dir ∣ (x , xεU) , dir (⊑[ P ]-refl x) ∣

      up : [ (⋁[ L ] ⁅ η x ∣ x ∈ U ⁆) ⊑[ pos L ] 𝔘 ]
      up x (dir xε⋁) = ∥∥-rec (is-true-prop (U x)) NTS xε⋁
        where
          NTS : Σ[ y ∈ _ ] [ x ∈ ⦅ η (π₀ y) ⦆ ] → [ x ∈ U ]
          NTS ((y , yεU) , x◀y↓) =
            subst (λ V → [ π₀ V x ]) U-fix  (cover+ (U , U-dc) x◀y↓ yεU)
      up x (branch b f) = subst (λ V → [ π₀ V x ]) U-fix (branch b (dir ∘ IH))
        where
          IH : (c : outcome F b) → [ next F c ∈ U ]
          IH c = up (next F c) (f c)
      up x (squash x◀⋁₀ x◀⋁₁ i) = is-true-prop (U x) (up x x◀⋁₀) (up x x◀⋁₁) i
```

Proof.

```
  module MainProof (R      : Frame (suc ℓ₀) ℓ₀ ℓ₀)
                   (fm     : P ─m→ pos R)
                   (f-flat : isFlat R fm)
                   (rep    : represents R fm) where
    f      = _$ₘ_ fm
    f-mono = π₁ fm

    _⊑R_ : ∣ R ∣F → ∣ R ∣F → hProp ℓ₀
    x ⊑R y = x ⊑[ pos R ] y

    infix 9 _⊑R_
```

```
    g : ∣ L ∣F → ∣ R ∣F
    g 𝔘 = ⋁[ R ] ⁅ f u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆
```

```
    g-mono : isMonotonic (pos L) (pos R) g
    g-mono ((U , _) , _) ((V , _) , _) U⊆V =
      ⋁[ R ]-least _ _ (λ o oεfU → ⋁[ R ]-upper _ _ (NTS o oεfU ))
      where
        NTS : (x : ∣ R ∣F) → x ε (∃ U , f ∘ π₀) → x ε (∃ V , f ∘ π₀)
        NTS x ((x′ , x′εfU) , fUεi=x) = (x′ , U⊆V x′ x′εfU) , fUεi=x

    gm : pos L ─m→ pos R
    gm = g , g-mono
```

### `g` respects the top element

```
    g-resp-𝟏 : g ⊤[ L ] ≡ ⊤[ R ]
    g-resp-𝟏 = g ⊤[ L ]                            ≡⟨ refl             ⟩
               ⋁[ R ] (f ⟨$⟩ (∃ ⦅ ⊤[ L ] ⦆ , π₀))  ≡⟨ family-iff R NTS ⟩
               ⋁[ R ] (∣ P ∣ₚ , f)                 ≡⟨ sym (π₀ f-flat)  ⟩
               ⊤[ R ]                              ∎
      where
        NTS : (x : ∣ R ∣F)
            → (x ε (f ⟨$⟩ (∃ ⦅ ⊤[ L ] ⦆ , π₀)) → x ε (∣ P ∣ₚ , f))
            × (x ε (∣ P ∣ₚ , f) → x ε (f ⟨$⟩ (∃ ⦅ ⊤[ L ] ⦆ , π₀)))
        NTS x = (λ { ((y , _) , eq) → y , eq }) , (λ { (y , eq) → (y , tt) , eq })
```

### `g` respects the binary meets

```
    g-resp-⊓ : (𝔘 𝔙 : ∣ L ∣F) → g (𝔘 ⊓[ L ] 𝔙) ≡ g 𝔘 ⊓[ R ] g 𝔙
    g-resp-⊓ 𝔘 𝔙 =
      g (𝔘 ⊓[ L ] 𝔙)
        ≡⟨ refl ⟩
      ⋁[ R ] ⁅ f a ∣ a ∈ ⦅ 𝔘 ⊓[ L ] 𝔙 ⦆ ⁆
        ≡⟨ I ⟩
      ⋁[ R ] ((∃ ⦅ 𝔘 ⦆ × ∃ ⦅ 𝔙 ⦆) , λ { ((u , _) , v , _) → ⋁[ R ] (f ⟨$⟩ ⟪ u ↓ v ↓ ⟫) })
        ≡⟨ cong (λ - → (⋁[ R ] ((∃ ⦅ 𝔘 ⦆ × ∃ ⦅ 𝔙 ⦆) , -))) II ⟩
      ⋁[ R ] (((∃ ⦅ 𝔘 ⦆) × (∃ ⦅ 𝔙 ⦆)) , λ { ((u , _) , (v , _)) → f u ⊓[ R ] f v })
        ≡⟨ sym (sym-distr R (⁅ f u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆) (⁅ f v ∣ v ∈ ⦅ 𝔙 ⦆ ⁆)) ⟩
      (⋁[ R ] ⁅ f u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆) ⊓[ R ] (⋁[ R ] ⁅ f v ∣ v ∈ ⦅ 𝔙 ⦆ ⁆)
        ≡⟨ refl ⟩
      g 𝔘 ⊓[ R ] g 𝔙
        ∎
      where
        II : (λ { ((u , _) , (v , _)) → ⋁[ R ] (f ⟨$⟩ ⟪ u ↓ v ↓ ⟫) })
           ≡ (λ { ((u , _) , (v , _)) → (f u) ⊓[ R ] (f v) })
        II = sym (funExt λ { ((u , _) , (v , _)) → π₁ f-flat u v })
        I  : _
        I  = ⊑[ pos R ]-antisym _ _ down up
          where
            LHS = ⋁[ R ] ⁅ f a ∣ a ∈ ⦅ 𝔘 ⊓[ L ] 𝔙 ⦆ ⁆
            RHS = ⋁[ R ] (∃ ⦅ 𝔘 ⦆ × ∃ ⦅ 𝔙 ⦆ , λ { ((u , _) , v , _) → ⋁[ R ] (f ⟨$⟩ ⟪ u ↓ v ↓ ⟫) })

            down : [ LHS ⊑[ pos R ] RHS ]
            down = ⋁[ R ]-least _ _ isUB
              where
                isUB : _
                isUB o ((a , (a∈U , a∈V)) , eq) =
                  ⋁[ R ]-upper _ _ NTS
                  where
                    u : ∃ ⦅ 𝔘 ⦆
                    u = a , a∈U

                    v : ∃ ⦅ 𝔙 ⦆
                    v = a , a∈V

                    NTS : o ε (∃ ⦅ 𝔘 ⦆ × ∃ ⦅ 𝔙 ⦆ , (λ { ((u , _) , v , _) → ⋁[ R ] (f ⟨$⟩ ⟪ u ↓ v ↓ ⟫) }))
                    NTS = (u , v) , subst (λ o′ → _ ≡ o′) eq NTS′
                      where
                        down′ : [ ⋁[ R ] (f ⟨$⟩ ⟪ a ↓ a ↓ ⟫) ⊑[ pos R ] f a ]
                        down′ =
                          ⋁[ R ]-least _ _ λ { z ((_ , (k , _)) , eq′) →
                            subst (λ - → [ - ⊑[ pos R ] _ ]) eq′ (f-mono _ _ k) }
                        up′ : [ f a ⊑[ pos R ] ⋁[ R ] (f ⟨$⟩ ⟪ a ↓ a ↓ ⟫) ]
                        up′ = ⋁[ R ]-upper _ _ ((a , (⊑[ P ]-refl a , ⊑[ P ]-refl a)) , refl)

                        NTS′ : ⋁[ R ] (f ⟨$⟩ ⟪ a ↓ a ↓ ⟫) ≡ f a
                        NTS′ = ⊑[ pos R ]-antisym _ _ down′ up′

            up : [ LHS ⊒[ pos R ] RHS ]
            up = ⋁[ R ]-least _ _ isUB
              where
                isUB : _
                isUB o (i@((x , xε𝔙) , (y , yε𝔘)) , eq) =
                  subst (λ o′ → [ o′ ⊑[ pos R ] _ ]) eq (⋁[ R ]-least _ _ NTS)
                  where
                    NTS : _
                    NTS w (j@(z , (z⊑x , z⊑y)) , eq′) = ⋁[ R ]-upper _ _ ((z , φ) ,  eq′)
                      where
                        φ : [ z ∈ (⦅ 𝔘 ⦆ ∩ ⦅ 𝔙 ⦆) ]
                        φ = (π₁ (π₀ 𝔘) x z xε𝔙 z⊑x) , (π₁ (π₀ 𝔙) y z yε𝔘 z⊑y)
```

### `g` respects the joins

```
    open PosetReasoning (pos R)

    resp-⋁-lem : (U@(I , _) : Fam ℓ₀ ∣ L ∣F)
               → ⋁[ R ] ⁅ f a ∣ a ∈ ⦅ ⋁[ L ] U ⦆ ⁆
               ≡ (⋁[ R ] ⁅ f a ∣ (_ , a , _) ∶ (Σ[ i ∈ I ] ∃ ⦅ U $ i ⦆) ⁆)
    resp-⋁-lem U@(I , _) = ⊑[ pos R ]-antisym _ _ down up
      where
        LHS = ⋁[ R ] ⁅ f a ∣ a ∈ ⦅ ⋁[ L ] U ⦆ ⁆
        RHS = ⋁[ R ] ⁅ f a ∣ (_ , a , _) ∶ (Σ[ i ∈ I ] ∃ ⦅ U $ i ⦆) ⁆

        ϑ : (x : ∣ P ∣ₚ) → [ x ∈ ⦅ ⋁[ L ] U ⦆ ] → [ f x ⊑R RHS ]
        ϑ x (squash p q i) = is-true-prop (f x ⊑R _) (ϑ x p) (ϑ x q) i
        ϑ x (dir    xε⋁U)  = ∥∥-rec (is-true-prop (f x ⊑R _)) NTS xε⋁U
                             where
                               NTS : _
                               NTS (j , cov) = ⋁[ R ]-upper _ _ ((j , x , cov) , refl)
        ϑ x (branch b h)   =
          f x                      ⊑⟨ rep x b              ⟩
          ⋁[ R ] (_ , f ∘ next F)  ⊑⟨ ⋁[ R ]-least _ _ NTS ⟩
          RHS                      ■
          where
            NTS : (r : ∣ R ∣F) → r ε (_ , f ∘ next F) → [ r ⊑R _ ]
            NTS r (c , p) = subst (λ - → [ - ⊑R _ ]) p (ϑ (next F c) (h c))

        down : [ LHS ⊑R RHS ]
        down =
          ⋁[ R ]-least _ _ λ r ((x , cov) , p) → subst (λ - → [ - ⊑R _ ]) p (ϑ x cov)

        up : [ LHS ⊒[ pos R ] RHS ]
        up = ⋁[ R ]-least _ _ NTS
          where
            NTS : _
            NTS r ((i , (x , xεU)) , p) = ⋁[ R ]-upper _ _ ((x , dir ∣ i , xεU ∣) , p)
```

```
    g-resp-⊔ : (U : Fam ℓ₀ ∣ L ∣F) → g (⋁[ L ] U) ≡ ⋁[ R ] (g ⟨$⟩ U)
    g-resp-⊔ U@(I , h) =
      ⋁[ R ] ⁅ f a ∣ a ∈ ⦅ ⋁[ L ] U ⦆ ⁆
        ≡⟨ resp-⋁-lem U  ⟩
      ⋁[ R ] ⁅ f a ∣ (_ , (a , _)) ∶ Σ[ i ∈ I ] Σ[ x ∈ ∣ P ∣ₚ ] [ x ∈ ⦅ U $ i ⦆ ] ⁆
        ≡⟨ flatten R I (λ i → Σ[ x ∈ ∣ P ∣ₚ ] [ x ∈ ⦅ U $ i ⦆ ]) (λ { _ (a , _) → f a }) ⟩
      ⋁[ R ] ⁅ ⋁[ R ] ⁅ f a ∣ a ∈ ⦅ U $ i ⦆ ⁆ ∣ i ∶ I ⁆
        ≡⟨ refl ⟩
      ⋁[ R ] ⁅ g (U $ i) ∣ i ∶ I ⁆
        ∎
```

### `g` is a frame homomorphism

```
    g-frame-homo : isFrameHomomorphism L R gm
    g-frame-homo = g-resp-𝟏 , (g-resp-⊓ , g-resp-⊔)
```

### `g` makes the diagram commute

```
    lem : (a a′ : ∣ P ∣ₚ) → a′ ◀ π₀ (↓-clos a) → [ f a′ ⊑[ pos R ] f a ]
    lem a a′ (squash p q i) = is-true-prop (f a′ ⊑[ pos R ] f a) (lem _ _ p) (lem _ _ q) i
    lem a a′ (dir    a′⊑a)  = f-mono a′ a a′⊑a
    lem a a′ (branch b h)   =
      f a′                              ⊑⟨ rep a′ b              ⟩
      ⋁[ R ] (outcome F b , f ∘ next F) ⊑⟨ ⋁[ R ]-least _ _ isUB ⟩
      f a                               ■
      where
        isUB : ∀ a₀ → a₀ ε (outcome F b , f ∘ next F) → [ a₀ ⊑[ pos R ] f a ]
        isUB a₀ (c , p) = a₀           ⊑⟨ ≡⇒⊑ (pos R) (sym p)    ⟩
                          f (next F c) ⊑⟨ lem a (next F c) (h c) ⟩
                          f a          ■

    gm∘ηm = _∘m_ {P = P} {Q = pos L} {R = pos R} gm ηm

    gm∘ηm~f : (x : ∣ P ∣ₚ) → gm $ₘ (ηm $ₘ x) ≡ fm $ₘ x
    gm∘ηm~f x = ⊑[ pos R ]-antisym _ _ down (⋁[ R ]-upper _ _ ((x , x◀x↓ x) , refl))
      where
        down : [ (⋁[ R ] (∃ π₀ (e x) , f ∘ π₀)) ⊑[ pos R ] f x ]
        down = ⋁[ R ]-least _ _ λ { o ((y , φ) , eq) → subst (λ _ → _) eq (lem x y φ) }

    g∘η=f : gm∘ηm ≡ fm
    g∘η=f = forget-mono P (pos R) gm∘ηm fm (funExt gm∘ηm~f)

    g∘η=f′ : g ∘ η ≡ f
    g∘η=f′ = subst (λ { (h , _) → h ≡ f }) (sym g∘η=f) refl
```

### `g` is uniquely determined

```
    g-unique : (y : Σ[ g′ ∈ (L ─f→ R) ]
                     (_∘m_ {P = P} {Q = pos L} {R = pos R} (π₀ g′) ηm ≡ fm))
            → ((gm , g-frame-homo) , g∘η=f) ≡ y
    g-unique ((g′m , g′-frame-homo) , φ) = ΣProp≡ I II
      where
        g′ = _$ₘ_ g′m

        f=g′∘η : f ≡ g′ ∘ η
        f=g′∘η = subst (λ { (f′ , _) → f′ ≡ g′ ∘ η }) φ refl

        NTS₀ : (y : Σ (∣ pos L ∣ₚ → ∣ pos R ∣ₚ) (isMonotonic (pos L) (pos R)))
             → isProp ((_∘m_ {P = P} {Q = pos L} {R = pos R} y ηm) ≡ fm)
        NTS₀ y = isSetΣ
                   (isSetΠ λ _ → carrier-is-set (pos R))
                   (λ h → isProp→isSet (isMonotonic-prop P (pos R) h))
                   (_∘m_ {P = P} {Q = pos L} {R = pos R} y ηm) fm

        I : (h : L ─f→ R) → isProp (_∘m_ {P = P} {Q = pos L} {R = pos R} (π₀ h) ηm ≡ fm)
        I h = isSetΣ
                (isSetΠ λ _ → carrier-is-set (pos R))
                (λ h → isProp→isSet (isMonotonic-prop P (pos R) h))
                (_∘m_ {P = P} {Q = pos L} {R = pos R} (π₀ h) ηm) fm

        g~g′ : (𝔘 : ∣ L ∣F) → g 𝔘 ≡ g′ 𝔘
        g~g′ 𝔘 =
          g 𝔘                             ≡⟨ refl ⟩
          ⋁[ R ] ⁅ f u     ∣ u ∈ ⦅ 𝔘 ⦆ ⁆  ≡⟨ eq₀  ⟩
          ⋁[ R ] ⁅ g′(η u) ∣ u ∈ ⦅ 𝔘 ⦆ ⁆  ≡⟨ eq₁  ⟩
          g′ (⋁[ L ] ⁅ η u ∣ u ∈ ⦅ 𝔘 ⦆ ⁆) ≡⟨ cong g′ (sym (main-lemma 𝔘))  ⟩
          g′ 𝔘 ∎
          where
            eq₀ : ⋁[ R ] (f ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫) ≡ ⋁[ R ] ((g′ ∘ η) ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫)
            eq₀ = cong (λ - → ⋁[ R ] (- ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫)) f=g′∘η
            eq₁ : ⋁[ R ] ((g′ ∘ η) ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫) ≡ g′ (⋁[ L ] (η ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫))
            eq₁ = sym (π₁ (π₁ g′-frame-homo) (η ⟨$⟩ ⟪ ⦅ 𝔘 ⦆ ⟫))

        II : (gm , g-frame-homo) ≡ (g′m , g′-frame-homo)
        II = ΣProp≡
               (isFrameHomomorphism-prop L R)
               (ΣProp≡ (isMonotonic-prop (pos L) (pos R)) (funExt g~g′))
```

### The final proof

```
  main : universal-prop
  main R fm@(f , f-mono) f-flat rep =
    (((g , g-mono) , g-resp-𝟏 , g-resp-⊓ , g-resp-⊔) , g∘η=f) , g-unique
    where
      open MainProof R fm f-flat rep
```
