```agda
{-# OPTIONS --cubical --safe #-}

open import Basis
open import Poset
open import Frame

module Cofinality (F : Frame ℓ₀ ℓ₁ ℓ₂) where
```

Definition
==========

```agda
_cofinal-in_ : Fam ℓ₂ ∣ F ∣F → Fam ℓ₂ ∣ F ∣F → Type (ℓ-max ℓ₁ ℓ₂)
_cofinal-in_ U V =
  (i : index U) → Σ[ j ∈ index V ] [ (U $ i) ⊑[ pos F ] (V $ j) ] 
```

Bi-cofinality
=============

```agda
bicofinal : Fam ℓ₂ ∣ F ∣F → Fam ℓ₂ ∣ F ∣F → Type (ℓ-max ℓ₁ ℓ₂)
bicofinal U V = (U cofinal-in V) × (V cofinal-in U)
```

Joins of bi-cofinal families are equal
======================================

```agda
bicofinal→same-join-lemma : (U V : Fam ℓ₂ ∣ F ∣F)
                          → U cofinal-in V → [ ⋁[ F ] U ⊑[ pos F ] ⋁[ F ] V ]
bicofinal→same-join-lemma U V U-cf-V = ⋁[ F ]-least U (⋁[ F ] V) nts where

  open PosetReasoning (pos F)

  nts : [ ∀[ u ε U ] (u ⊑[ pos F ] (⋁[ F ] V)) ]
  nts u (i , eq) = subst (λ - → [ - ⊑[ pos F ] _ ]) eq nts₀ where

    j = π₀ (U-cf-V i)

    nts₀ : [ (U $ i) ⊑[ pos F ] (⋁[ F ] V) ]
    nts₀ = U $ i    ⊑⟨ π₁ (U-cf-V i)               ⟩
           V $ j    ⊑⟨ ⋁[ F ]-upper _ _ (j , refl) ⟩
           ⋁[ F ] V ■

bicofinal→same-join : (U V : Fam ℓ₂ ∣ F ∣F)
                    → bicofinal U V → ⋁[ F ] U ≡ ⋁[ F ] V
bicofinal→same-join U V (φ , ψ) = ⊑[ pos F ]-antisym _ _ ⋁U⊑⋁V ⋁V⊑⋁U where

  ⋁U⊑⋁V : [ (⋁[ F ] U) ⊑[ pos F ] (⋁[ F ] V) ]
  ⋁U⊑⋁V = bicofinal→same-join-lemma U V φ

  ⋁V⊑⋁U : [ (⋁[ F ] V) ⊑[ pos F ] (⋁[ F ] U) ]
  ⋁V⊑⋁U = bicofinal→same-join-lemma V U ψ
```
