---
title: Some Experiments on Automata
---

<!--
```agda
{-# OPTIONS --cubical --safe #-}

module Automata where

open import Basis
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Fin
open import Cubical.Data.List hiding ([_])
open import Cubical.Functions.Logic
open import Cubical.Foundations.Function

open import FormalTopology renaming (δ to 𝕕)
open import Poset
```
-->

```agda
isFinite : 𝓤 ̇ → 𝓤 ̇
isFinite A = Σ[ n ∈ ℕ ] Fin n ≃ A
```


## Definition of DFA

```agda
record DFA : 𝓤₁ ̇ where
  field
    Q  : 𝓤₀ ̇
    S  : 𝓤₀ ̇
    δ  : Q → S → Q
    q₀ : Q
    F  : Q → hProp 𝓤₀

  field
    ∣Q∣   : ℕ
    Q-fin : Fin ∣Q∣ ≃ Q
    S-fin : isFinite S

  Q-set : isSet Q
  Q-set = subst isSet (ua Q-fin) isSetFin

open DFA
```

## Acceptance

```agda
_accepts_at_ : (M : DFA) → List (M .S) → M .Q → hProp 𝓤₀
_accepts_at_ M []       x = M .F x
_accepts_at_ M (a ∷ as) x = M accepts as at (M .δ x a)
```

```agda
_accepts_ : (M : DFA) → List (M .S) → hProp 𝓤₀
M accepts as = M accepts as at M .q₀
```

## The specialisation preorder

```agda
_<<<_ : (M : DFA) → M .Q → M .Q → hProp 𝓤₀
_<<<_ M x y = ∀[ s ∶ List (M .S) ] M accepts s at y ⇒ M accepts s at x
```

```agda
<<<-refl : (M : DFA) → [ ∀[ x ∶ M .Q ] (_<<<_ M x x) ]
<<<-refl M x s = idfun _
```

```agda
<<<-trans : (M : DFA)
          → (x y z : M .Q) → [ _<<<_ M x y ⇒ _<<<_ M y z ⇒ _<<<_ M x z ]
<<<-trans M x y z p q s = p s ∘ q s
```

```agda
isAntisymmetric : (M : DFA) → 𝓤₀ ̇
isAntisymmetric M = (x y : M .Q) → [ _<<<_ M x y ] → [ _<<<_ M y x ] → x ≡ y
```

```agda
dfa-poset : (M : DFA) → isAntisymmetric M → Poset 𝓤₀ 𝓤₀
dfa-poset M p = M .Q , _<<<_ M , Q-set M , <<<-refl M , <<<-trans M , p
```

## Interaction system

```agda
to-is : (M : DFA) → InteractionSys 𝓤₀
to-is M = M .Q , BB , CC , (λ {x} {y} → dd {x} {y})
  where
  BB : M .Q → 𝓤₀ ̇
  BB = const (Unit 𝓤₀)

  CC : Unit 𝓤₀ → Type 𝓤₀
  CC _ = M .S

  dd : {x : M .Q} {y : BB x} → CC y → M .Q
  dd {x = x} = M .δ x
```

## Formal topology

```agda
to-ft : (M : DFA) → isAntisymmetric M → FormalTopology 𝓤₀ 𝓤₀
to-ft M p = dfa-poset M p , π₁ (to-is M) , m , s
  where
  -- Kind of like a safety property.
  -- For the language of bad prefixes: If you accept the word, then you accept any
  -- extension of the word.
  m′ : (x : M .Q) (a : M .S) → [ _<<<_ M (M .δ x a) x ]
  m′ = {!!}

  m : hasMono (dfa-poset M p) (π₁ (to-is M))
  m a tt = m′ a

  s′ : (x′ x : M .Q)
     → [ _<<<_ M x′ x ]
     → (a′ : M .S)
     → Σ[ a ∈ M .S ] [ _<<<_ M (M .δ x′ a′) (M .δ x a) ]
  s′ = {!!}

  -- ∀ x′, x : Q. x′ ≤ x → ∀ a′ : Σ. ∃ a : Σ. δ(x′, a′) ≤ δ(x, a)

  s : hasSimulation (dfa-poset M p) (π₁ (to-is M))
  s a′ a x b = tt , s′ a′ a x


-- --}
```
