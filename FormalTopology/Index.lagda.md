```agda
{-# OPTIONS --cubical --safe #-}

module Index where

open import Basis
open import Poset
open import FormalTopology
open import Cover

import Nucleus
import CoverFormsNucleus
import UniversalProperty

open import Cubical.Data.Bool using (Bool; _≟_)

open import SnocList Bool _≟_
import CantorSpace
```

## Chapter 2: Foundations

### 2.3: Equivalence and univalence

**Definition 2.1**.

```agda
_ = isContr
```

**Definition 2.2**.

```agda
_ = fiber
```

**Definition 2.3**.

```agda
_ = isEquiv
```

**Definition 2.4**.

```agda
_ = _≃_
```

**Definition 2.5**.

```agda
_ = idEquiv
```

**Definition 2.6**.

```agda
-- TODO
```

**Definition 2.7**.

```agda
_ = _~_
```

**Proposition 2.8**.

```agda
_ = funExt
```

### 2.4: Homotopy levels

**Definition 2.9**.

```agda
_ = isOfHLevel
```

**Proposition 2.10**.

```agda
_ = isOfHLevelSuc
```

**Proposition 2.11**.

```agda
_ = isOfHLevelΠ
```

**Proposition 2.12**.

```agda
_ = isOfHLevelΣ
```

**Definition 2.13**.

```agda
_ = isProp
```

**Definition 2.14**.

```agda
-- TODO
```

**Definition 2.15**.

```agda
-- TODO
```

**Definition 2.16**.

```agda
_ = hProp
```

**Proposition 2.17**.

```agda
_ = isPropΠ
```

**Proposition 2.18**.

```agda
_ = isPropΣ
```

**Proposition 2.19**.

```agda
_ = isPropIsProp
```

**Proposition 2.20**.

```agda
_ = ΣProp≡
```

### 2.5: Powersets

TODO

### 2.6: Powersets

TODO

### 2.7: Higher inductive types

TODO

### 2.8: Truncation

TODO

## Chapter 3: Frames

### 3.1: Partially ordered sets

**Definition 3.1**.

```agda
_ = Poset
_ = PosetStr
_ = PosetAx
```

**Definition 3.2**.

```agda
_ = isDownwardsClosed
_ = DCSubset
```

### 3.2: Definition of a frame

TODO

### 3.3: Some properties of frames

TODO

### 3.4: Univalence for frames

TODO

### 3.5: Frame of downwards-closed subsets

TODO

### 3.6: Nuclei and their fixed points

TODO

## Chapter 4: Formal Topology

### 4.1: Interaction systems

**Definition 4.1**.

```agda
_ = InteractionStr
_ = InteractionSys
```

**Definition 4.2**.

```agda
_ = hasMono
```

**Definition 4.3**.

```agda
_ = hasSimulation
```

**Definition 4.4**.

```agda
_ = FormalTopology
```
### 4.2: Cover relation

Note that **Definition 4.5** is not formalised.

**Definition 4.7**.

```agda
_ = CoverFromFormalTopology._◀_
```

**Proposition 4.8**.

```agda
_ = CoverFromFormalTopology.◀-lem₁
```

**Proposition 4.9**.

```agda
_ = CoverFromFormalTopology.lem₂
```

**Proposition 4.10**.

```agda
_ = CoverFromFormalTopology.lem₃
```

**Proposition 4.11**.

```agda
_ = CoverFromFormalTopology.lem₄
```

### 4.3: Covers are nuclei

**Theorem 4.12**.

```agda
_ = CoverFormsNucleus.NucleusFrom.𝕛-nuclear
```

### 4.4: Lifting into the generated frame

**Definition 4.13**.

```agda
_ = CoverFormsNucleus.NucleusFrom.η
```

### 4.5: Formal topologies present

**Definition 4.14**.

```agda
_ = UniversalProperty.represents
```

**Definition 4.15**.

```agda
_ = UniversalProperty.isFlat
```

**Theorem 4.16**.

The theorem statement is given in:

```agda
_ = UniversalProperty.universal-prop
```

The proof is given in:

```agda
_ = UniversalProperty.main
```

**Lemma 4.17**.

```agda
_ = UniversalProperty.main-lemma
```

**Lemma 4.18**.

```agda
_ = UniversalProperty.MainProof.resp-⋁-lem
```

## Chapter 5: The Cantor space

### 5.1: The Cantor interaction system

**Definition 5.1**.

```agda
_ = SnocList._⌢_
_ = SnocList.[]
```

**Definition 5.2**.

```agda
_ = _++_
```

**Proposition 5.3**.

```agda
_ = SnocList-discrete
```

**Definition 5.4**.

```agda
_ = CantorSpace.ℂ-pos
```

**Definition 5.5**.

```agda
_ = CantorSpace.ℂ-IS
```

**Theorem 5.6**.

```agda
_ = CantorSpace.cantor
```

### 5.2: The Cantor space is compact

**Definition 5.7**.

```agda
_ = CantorSpace.down
```

**Definition 5.8**.

```agda
_ = CantorSpace.isCompact
```

**Lemma 5.9**.

```agda
_ = CantorSpace.U⊆V⇒◀U⊆◀V
```

**Lemma 5.10**. In the Agda formalisation, this is broken up into two functions.

```agda
_ = CantorSpace.↓-++-left
_ = CantorSpace.↓-++-right
```

**Lemma 5.11**.

```agda
_ = CantorSpace.◀^-decide
```

**Theorem 5.12**.

```agda
_ = CantorSpace.compact
```
