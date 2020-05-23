{-# OPTIONS --cubical #-}

module Sierpinski where

open import Basis
open import Cubical.Data.Bool
open import Poset

𝕊-pos : Poset zero zero
𝕊-pos = Bool , (_≤_ , isSetBool , (≤-refl , ≤-trans , ≤-antisym))
  where
    _≤_ : Bool → Bool → hProp zero
    _     ≤ true  = Unit zero , Unit-prop
    false ≤ false = Unit zero , Unit-prop
    true  ≤ false = bot zero

    ≤-refl : (x : Bool) → [ x ≤ x ]
    ≤-refl false = tt
    ≤-refl true  = tt

    ≤-trans : (x y z : Bool) → [ x ≤ y ] → [ y ≤ z ] → [ x ≤ z ]
    ≤-trans x false false p q = p
    ≤-trans x y     true  p q = tt

    ≤-antisym : (x y : Bool) → [ x ≤ y ] → [ y ≤ x ] → x ≡ y
    ≤-antisym false false p q = refl
    ≤-antisym true  true  p q = refl
