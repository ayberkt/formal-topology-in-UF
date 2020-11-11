```agda
{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything

open import Poset
open import Frame
open import Nucleus
open import Cubical.Functions.Logic      hiding (_⊓_)
open import Cubical.Foundations.Prelude  using (sym; cong; _≡⟨_⟩_; _∎)
open import Cubical.Data.Sigma           using (Σ≡Prop)
open import Cubical.Foundations.Function using (const)
open import Basis                        using ([_]; funExt)

module FrameOfNuclei where

private
  variable
    ℓ₀ ℓ₁ ℓ₂ : Level
```

```agda
module FrameOfNuclei (F : Frame ℓ₀ ℓ₁ ℓ₂) where

  open PosetReasoning (pos F) using (_⊑⟨_⟩_; _■)

  poset-of-nuclei-str : PosetStr (ℓ-max ℓ₀ ℓ₁) (Nucleus F)
  poset-of-nuclei-str = _⊑_ , Nucleus-set F , ⊑-refl , ⊑-trans , ⊑-antisym
    where
      _⊑_ : Order (ℓ-max ℓ₀ ℓ₁) (Nucleus F)
      (j , _) ⊑ (k , _) = ∀[ x ∶ ∣ F ∣F ] j x ⊑[ pos F ] k x

      ⊑-refl : [ isReflexive _⊑_ ]
      ⊑-refl (j , _) x = ⊑[ pos F ]-refl (j x)

      ⊑-trans : [ isTransitive _⊑_ ]
      ⊑-trans (j , _) (k , _) (l , _) j⊑k k⊑l x =
        j x ⊑⟨ j⊑k x ⟩ k x ⊑⟨ k⊑l x ⟩ l x ■

      ⊑-antisym : [ isAntisym (Nucleus-set F)  _⊑_ ]
      ⊑-antisym (j , _) (k , _) j⊑k k⊑j =
        Σ≡Prop
          (isNuclear-prop F)
          (funExt λ x → ⊑[ pos F ]-antisym (j x) (k x) (j⊑k x) (k⊑j x))

  poset-of-nuclei : Poset (ℓ-max ℓ₀ ℓ₁) (ℓ-max ℓ₀ ℓ₁)
  poset-of-nuclei = (Nucleus F) , poset-of-nuclei-str

  frame-of-nuclei : Frame (ℓ-max ℓ₀ ℓ₁) (ℓ-max ℓ₀ ℓ₁) {!!}
  frame-of-nuclei =
    Nucleus F , ((poset-of-nuclei-str , 𝟏 , _⊓_ , {!!}) , {!!})
    where
      𝟏 : Nucleus F
      𝟏 = const ⊤[ F ] , 𝟎-N₀ , 𝟎-N₁ , 𝟎-N₂
        where
          𝟎-N₀ : _
          𝟎-N₀ _ _ = sym (x∧⊤=x F ⊤[ F ])

          𝟎-N₁ : _
          𝟎-N₁ = ⊤[ F ]-top

          𝟎-N₂ : _
          𝟎-N₂ _ = ⊑[ pos F ]-refl ⊤[ F ]

      _⊓_ : Nucleus F → Nucleus F → Nucleus F
      𝒿@(j , j-n₀ , j-n₁ , j-n₂) ⊓ 𝓀@(k , k-n₀ , k-n₁ , k-n₂) =
        (λ x → j x ⊓[ F ] k x) , ⊓-N₀ , ⊓-N₁ , ⊓-N₂
        where
          ⊓-N₀ : _
          ⊓-N₀ x y =
            j (x ⊓[ F ] y) ⊓[ F ] k (x ⊓[ F ] y) ≡⟨ {!!} ⟩
            j (x ⊓[ F ] y) ⊓[ F ] (k x ⊓[ F ] k y) ≡⟨ {!!} ⟩
            (j (x ⊓[ F ] y) ⊓[ F ] k x) ⊓[ F ] k y ≡⟨ {!!} ⟩
            (k x ⊓[ F ] j (x ⊓[ F ] y)) ⊓[ F ] k y ≡⟨ {!!} ⟩
            (k x ⊓[ F ] (j x ⊓[ F ] j y)) ⊓[ F ] k y ≡⟨ {!!} ⟩
            ((k x ⊓[ F ] j x) ⊓[ F ] j y) ⊓[ F ] k y ≡⟨ {!!} ⟩
            ((j x ⊓[ F ] k x) ⊓[ F ] j y) ⊓[ F ] k y ≡⟨ {!!} ⟩
            (j x ⊓[ F ] k x) ⊓[ F ] (j y ⊓[ F ] k y) ∎

          ⊓-N₁ : _
          ⊓-N₁ x = ⊓[ F ]-greatest (j x) (k x) x (j-n₁ x) (k-n₁ x)

          ⊓-N₂ : _
          ⊓-N₂ x =
            j (j x ⊓[ F ] k x) ⊓[ F ] k (j x ⊓[ F ] k x)       ⊑⟨ ⦅𝟏⦆ ⟩
            (j (j x) ⊓[ F ] j (k x)) ⊓[ F ] k (j x ⊓[ F ] k x) ⊑⟨ ⦅𝟐⦆ ⟩
            (j (j x)) ⊓[ F ] (k (j x) ⊓[ F ] k (k x))          ⊑⟨ ⦅𝟑⦆ ⟩
            (j (j x)) ⊓[ F ] (k (k x))                         ⊑⟨ ⦅𝟒⦆ ⟩
            (j x) ⊓[ F ] (k (k x))                             ⊑⟨ ⦅𝟓⦆ ⟩
            (j x) ⊓[ F ] (k x) ■
            where
              ⦅𝟏⦆ = {!!}
              ⦅𝟐⦆ = {!!}
              ⦅𝟑⦆ = {!!}
              ⦅𝟒⦆ = ≡⇒⊑ (pos F) (cong (λ - → - ⊓[ F ] _) (idem F 𝒿 x))
              ⦅𝟓⦆ = ≡⇒⊑ (pos F) (cong (λ - → _ ⊓[ F ] -) (idem F 𝓀 x ))
```
