{-# OPTIONS --cubical --safe #-}

module Sierpinski where

open import Basis
open import Cubical.Data.Bool
open import Poset
open import FormalTopology

𝕊-pos : Poset ℓ-zero ℓ-zero
𝕊-pos = Bool , (_≤_ , isSetBool , (≤-refl , ≤-trans , ≤-antisym))
  where
    _≤_ : Bool → Bool → hProp ℓ-zero
    _     ≤ true  = Unit ℓ-zero , Unit-prop
    false ≤ false = Unit ℓ-zero , Unit-prop
    true  ≤ false = bot ℓ-zero

    ≤-refl : (x : Bool) → [ x ≤ x ]
    ≤-refl false = tt
    ≤-refl true  = tt

    ≤-trans : (x y z : Bool) → [ x ≤ y ] → [ y ≤ z ] → [ x ≤ z ]
    ≤-trans x false false p q = p
    ≤-trans x y     true  p q = tt

    ≤-antisym : (x y : Bool) → [ x ≤ y ] → [ y ≤ x ] → x ≡ y
    ≤-antisym false false p q = refl
    ≤-antisym true  true  p q = refl

𝕊-exp : Bool → Type ℓ-zero
𝕊-exp _ = Unit ℓ-zero

𝕊-out : {x : Bool} → 𝕊-exp x → Type ℓ-zero
𝕊-out tt = Unit ℓ-zero

𝕊-rev : {x : Bool} {y : 𝕊-exp x} → 𝕊-out {x} y → Bool
𝕊-rev {x = x} {y = tt} tt = x

𝕊-IS : InteractionStr Bool
𝕊-IS = 𝕊-exp , (λ {x} → 𝕊-out {x}) , 𝕊-rev

𝕊 : FormalTopology ℓ-zero ℓ-zero
𝕊 = 𝕊-pos , 𝕊-IS , 𝕊-has-mono , 𝕊-has-sim
  where
    𝕊-has-mono : hasMono 𝕊-pos 𝕊-IS
    𝕊-has-mono false tt tt = tt
    𝕊-has-mono true  tt tt = tt

    𝕊-has-sim  : hasSimulation 𝕊-pos 𝕊-IS
    𝕊-has-sim false false x tt = tt , λ { tt → tt , tt }
    𝕊-has-sim false true  x tt = tt , λ { tt → tt , tt }
    𝕊-has-sim true  true  x tt = tt , λ { tt → tt , tt }
