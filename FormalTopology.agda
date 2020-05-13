{-# OPTIONS --cubical --safe #-}

module FormalTopology where

open import Basis
open import Poset

InteractionStr : (A : Type ℓ) → Type (suc ℓ)
InteractionStr {ℓ = ℓ} A =
  Σ[ B ∈ (A → Type ℓ) ] Σ[ C ∈ ({x : A} → B x → Type ℓ) ]({x : A} → {y : B x} → C y → A)

InteractionSys : (ℓ : Level) → Type (suc ℓ)
InteractionSys ℓ = Σ (Type ℓ) InteractionStr

state       : InteractionSys ℓ → Type ℓ
action      : (D : InteractionSys ℓ) → state D → Type ℓ
reaction    : (D : InteractionSys ℓ) → {x : state D} → action D x → Type ℓ
δ           : (D : InteractionSys ℓ) {x : state D} {y : action D x}
            → reaction D y → state D

state    (A , _ , _ , _) = A
action   (_ , B , _ , _) = B
reaction (_ , _ , C , _) = C
δ        (_ , _ , _ , d) = d

hasMono : (P : Poset ℓ₀ ℓ₁) → InteractionStr ∣ P ∣ₚ → Type (ℓ₀ ⊔ ℓ₁)
hasMono P i =
  (a : state IS) (b : action IS a) (c : reaction IS b) → [ δ IS c ⊑[ P ] a ]
  where
    IS : InteractionSys _
    IS = ∣ P ∣ₚ , i

module _ (P : Poset ℓ₀ ℓ₁) (ℐ-str : InteractionStr ∣ P ∣ₚ) where
  ℐ : InteractionSys ℓ₀
  ℐ = (∣ P ∣ₚ , ℐ-str)

  hasSimulation : Type (ℓ₀ ⊔ ℓ₁)
  hasSimulation =
    (a′ a : ∣ P ∣ₚ) → [ a′ ⊑[ P ] a ] →
      (b : action ℐ a) → Σ[ b′ ∈ action ℐ a′ ]
        ((c′ : reaction ℐ b′) → Σ[ c ∈ reaction ℐ b ] [ δ ℐ c′ ⊑[ P ] δ ℐ c ])

FormalTopology : (ℓ₀ ℓ₁ : Level) → Type (suc ℓ₀ ⊔ suc ℓ₁)
FormalTopology ℓ₀ ℓ₁ =
  Σ[ P ∈ Poset ℓ₀ ℓ₁ ] Σ[ ℐ ∈ InteractionStr ∣ P ∣ₚ ] hasMono P ℐ × hasSimulation P ℐ

pos : FormalTopology ℓ₀ ℓ₁ → Poset ℓ₀ ℓ₁
pos (P , _) = P

IS : (ℱ : FormalTopology ℓ₀ ℓ₁) → InteractionStr ∣ pos ℱ ∣ₚ
IS (_ , is , _) = is

stage : FormalTopology ℓ₀ ℓ₁ → Type ℓ₀
stage (P , ℐ-str , _) = state (∣ P ∣ₚ , ℐ-str)

exp : (ℱ : FormalTopology ℓ₀ ℓ₁) → stage ℱ → Type ℓ₀
exp (P , ℐ-str , _) = action (∣ P ∣ₚ , ℐ-str)

outcome : (ℱ : FormalTopology ℓ₀ ℓ₁) → {a : stage ℱ} → exp ℱ a → Type ℓ₀
outcome (P , ℐ-str , _) = reaction (∣ P ∣ₚ , ℐ-str)

next : (ℱ : FormalTopology ℓ₀ ℓ₁) {a : stage ℱ} {b : exp ℱ a} → outcome ℱ b → stage ℱ
next (P , ℐ-str , _) = δ (∣ P ∣ₚ , ℐ-str)

mono : (ℱ : FormalTopology ℓ₀ ℓ₁) → hasMono (pos ℱ) (IS ℱ)
mono (_ , _ , φ , _) = φ

sim : (ℱ : FormalTopology ℓ₀ ℓ₁) → hasSimulation (pos ℱ) (IS ℱ)
sim (_ , _ , _ , φ) = φ
