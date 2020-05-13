{-# OPTIONS --cubical --safe #-}

module ProductTopology where

open import Basis
open import Data.Sum
open import Poset
open import FormalTopology

module _ (𝔉 𝔊 : FormalTopology ℓ₀ ℓ₀) where
  P = pos 𝔉
  Q = pos 𝔊

  𝔉×𝔊 : FormalTopology ℓ₀ ℓ₀
  𝔉×𝔊 = P ×ₚ Q , ×-IS , ×-mono , ×-sim
    where
      ×-exp : ∣ P ×ₚ Q ∣ₚ → Type ℓ₀
      ×-exp (a₀ , a₁) = exp 𝔉 a₀ ⊎ exp 𝔊 a₁

      ×-out : {a : ∣ P ×ₚ Q ∣ₚ} → ×-exp a → Type ℓ₀
      ×-out (inj₁ b) = outcome 𝔉 b
      ×-out (inj₂ b) = outcome 𝔊 b

      ×-next : {a : ∣ P ×ₚ Q ∣ₚ} {b : ×-exp a} → ×-out {a = a} b → ∣ P ×ₚ Q ∣ₚ
      ×-next {a = (a₀ , a₁)} {b = inj₁ b} c = (next 𝔉 c) , a₁
      ×-next {a = (a₀ , a₁)} {b = inj₂ b} c = a₀         , (next 𝔊 c)

      ×-IS : InteractionStr ∣ P ×ₚ Q ∣ₚ
      ×-IS = ×-exp , ×-out , λ {a} {b} c → ×-next {b = b} c

      ×-mono : hasMono (P ×ₚ Q) ×-IS
      ×-mono (a₀ , a₁) (inj₁ b) c = (mono 𝔉 a₀ b c)   , ⊑[ Q ]-refl a₁
      ×-mono (a₀ , a₁) (inj₂ b) c = (⊑[ P ]-refl a₀) , mono 𝔊 a₁ b c

      ×-sim : hasSimulation (P ×ₚ Q) ×-IS
      ×-sim (a₀ , a₁) (a , a′) (a₀⊑a , a₁⊑a′) b with b
      ... | inj₁ b₀ = let (b₀′ , p) = sim 𝔉 _ _ a₀⊑a b₀
                      in inj₁ b₀′ , λ c₀ → π₀ (p c₀) , π₁ (p c₀) , a₁⊑a′
      ... | inj₂ b₁ = let (b₁′ , p) = sim 𝔊 _ _ a₁⊑a′ b₁
                      in inj₂ b₁′ , λ c₁ → π₀ (p c₁) , a₀⊑a , π₁ (p c₁)
