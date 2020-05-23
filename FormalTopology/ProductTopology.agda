{-# OPTIONS --cubical --safe #-}

module ProductTopology where

open import Basis
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
      ×-out (inl b) = outcome 𝔉 b
      ×-out (inr b) = outcome 𝔊 b

      ×-next : {a : ∣ P ×ₚ Q ∣ₚ} {b : ×-exp a} → ×-out {a = a} b → ∣ P ×ₚ Q ∣ₚ
      ×-next {a = (a₀ , a₁)} {b = inl b} c = (next 𝔉 c) , a₁
      ×-next {a = (a₀ , a₁)} {b = inr b} c = a₀         , (next 𝔊 c)

      ×-IS : InteractionStr ∣ P ×ₚ Q ∣ₚ
      ×-IS = ×-exp , ×-out , λ {a} {b} c → ×-next {b = b} c

      ×-mono : hasMono (P ×ₚ Q) ×-IS
      ×-mono (a₀ , a₁) (inl b) c = (mono 𝔉 a₀ b c)   , ⊑[ Q ]-refl a₁
      ×-mono (a₀ , a₁) (inr b) c = (⊑[ P ]-refl a₀) , mono 𝔊 a₁ b c

      ×-sim : hasSimulation (P ×ₚ Q) ×-IS
      ×-sim (a₀ , a₁) (a , a′) (a₀⊑a , a₁⊑a′) b with b
      ... | inl b₀ = let (b₀′ , p) = sim 𝔉 _ _ a₀⊑a b₀
                     in inl b₀′ , λ c₀ → π₀ (p c₀) , π₁ (p c₀) , a₁⊑a′
      ... | inr b₁ = let (b₁′ , p) = sim 𝔊 _ _ a₁⊑a′ b₁
                     in inr b₁′ , λ c₁ → π₀ (p c₁) , a₀⊑a , π₁ (p c₁)
