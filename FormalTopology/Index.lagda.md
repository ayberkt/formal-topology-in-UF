```agda
{-# OPTIONS --cubical --safe #-}

module Index where

import Basis
open import FormalTopology
open import Cover

import Poset
import Frame

import Nucleus
import CoverFormsNucleus
import UniversalProperty

import Cubical.Relation.Nullary
import Cubical.Relation.Nullary.DecidableEq
import Cubical.Foundations.Univalence
import Cubical.Foundations.SIP

open import Cubical.Data.Bool using (Bool; _≟_)

open import SnocList Bool _≟_
import CantorSpace
```

## Chapter 2: Foundations

### 2.3: Equivalence and univalence

**Definition 2.1**.

```agda
_ = Basis.isContr
```

**Definition 2.2**.

```agda
_ = Basis.fiber
```

**Definition 2.3**.

```agda
_ = Basis.isEquiv
```

**Definition 2.4**.

```agda
_ = Basis._≃_
```

**Definition 2.5**.

```agda
_ = Basis.idEquiv
```

**Definition 2.6**.

```agda
_ = Cubical.Foundations.Univalence.pathToEquiv
```

**Definition 2.7**.

```agda
_ = Basis._~_
```

**Proposition 2.8**.

```agda
_ = Basis.funExt
```

### 2.4: Homotopy levels

**Definition 2.9**.

```agda
_ = Basis.isOfHLevel
```

**Proposition 2.10**.

```agda
_ = Basis.isOfHLevelSuc
```

**Proposition 2.11**.

```agda
_ = Basis.isOfHLevelΠ
```

**Proposition 2.12**.

```agda
_ = Basis.isOfHLevelΣ
```

Definition 2.13 is omitted.

**Definition 2.14**.

```agda
_ = Basis.isProp
```

Proposition 2.15 is omitted.

**Definition 2.16**.

```agda
_ = Basis.hProp
```

**Proposition 2.17**.

```agda
_ = Basis.isPropΠ
```

**Proposition 2.18**.

```agda
_ = Basis.isPropΣ
```

**Proposition 2.19**.

```agda
_ = Basis.isPropIsProp
```

**Proposition 2.20**.

```agda
_ = Basis.ΣProp≡
```

**Definition 2.21**. This is defined directly for h-propositions in the
`cubical` library.

```agda
_ = Basis._⇔_
```

**Proposition 2.22**.

```agda
_ = Basis.⇔toPath
```

**Definition 2.23**.

```agda
_ = Basis.Iso
```

**Proposition 2.24**.

```agda
_ = Basis.isoToEquiv
_ = Basis.equivToIso
```

**Definition 2.25**.

```agda
_ = Basis.isSet
```

**Proposition 2.26**.

```agda
_ = Basis.isProp→isSet
```

**Proposition 2.27**.

```agda
_ = Basis.isSetHProp
```

**Proposition 2.28**.

```agda
_ = Basis.isSetΠ
```

**Proposition 2.29**.

```agda
_ = Basis.isSetΣ
```

**Proposition 2.30**.

```agda
_ = Basis.isPropIsSet
```

**Definition 2.31**.

```agda
_ = Cubical.Relation.Nullary.Dec
```

**Definition 2.32**.

```agda
_ = Cubical.Relation.Nullary.Discrete
```

**Theorem 2.33**.

```agda
_ = Cubical.Relation.Nullary.DecidableEq.Discrete→isSet
```

### 2.5: Powersets

**Definition 2.34**.

```agda
_ = Basis.𝒫
```

**Proposition 2.35**.

```agda
_ = Basis.𝒫-set
```

**Definition 2.36**.

```agda
_ = Basis._⊆_
```

**Definition 2.37**.

```agda
_ = Basis.entire
```

**Definition 2.38**.

```agda
_ = Basis._∩_
```

### 2.6: Families

**Definition 2.39**.

```agda
_ = Basis.Fam
```

**Definition 2.41**.

```agda
_ = Basis._ε_
```

**Definition 2.42**.

```agda
_ = Basis._⟨$⟩_
```

**Definition 2.43**.

```agda
_ = Basis.⟪_⟫
```

### 2.8: Truncation

**Definition 2.44**.

```agda
_ = Basis.∥_∥
_ = Basis.∥∥-prop
_ = Basis.∥∥-rec
```

## Chapter 3: Frames

### 3.1: Partially ordered sets

**Definition 3.1**.

```agda
_ = Poset.Poset
_ = Poset.PosetStr
_ = Poset.PosetAx
```

**Definition 3.2**.

```agda
_ = Poset.isDownwardsClosed
_ = Poset.DCSubset
```

**Proposition 3.3**.

```agda
_ = Poset.DCSubset-set
```

**Proposition 3.4**.

```agda
_ = Frame.DCPoset
```

**Definition 3.5**.

```agda
_ = Poset.isMonotonic
```

**Definition 3.6**.

```agda
_ = Poset.isPosetIso
```

### 3.2: Definition of a frame

**Definition 3.7**.

```agda
_ = Frame.RawFrameStr
_ = Frame.FrameAx
_ = Frame.FrameStr
```

**Proposition 3.8**.

```agda
_ = Frame.FrameAx-props
```

**Definition 3.9**.

```agda
_ = Frame.isFrameHomomorphism
_ = Frame._─f→_
_ = Frame._≅f_
```

**Definition 3.10**.

```agda
_ = Frame.isFrameIso
```

**Definition 3.11** is not explicitly defined. We refer to it in an ad hoc way
by referring to `_≅ₚ_` on the underlying posets.

The equivalence of Defn. 3.10 and Defn. 3.11 is stated only in passing in the
thesis, not as an explicit proposition but is witnessed in the Agda code
by the following function:

```agda
_ = Frame.≅ₚ≃≅f
```

### 3.3: Some properties of frames

**Proposition 3.12**.

```agda
_ = Frame.comm
```

**Lemma 3.13**.

```agda
_ = Frame.flatten
```

**Proposition 3.14**.

```agda
_ = Frame.family-iff
```

**Proposition 3.15**.

```agda
_ = Frame.sym-distr
```

### 3.4: Univalence for frames

**Definition 3.16**.

```agda
_ = Poset.isAMonotonicEqv
```

**Definition 3.17**.

```agda
_ = Cubical.Foundations.SIP.SIP
```

**Definition 3.18**.

```agda
_ = Frame.isHomoEqv
```

Equation 3.19.

```agda
_ = Frame.≃f≃≡
```

Equation 3.20.

```agda
_ = Frame.≃f≃≅ₚ
```

Equation 3.21.

```agda
_ = Frame.≅ₚ≃≡
```

### 3.5: Frames of downwards-closed subsets

**Theorem 3.22**.

```agda
_ = Frame.DCFrame
```

### 3.6: Nuclei and their fixed points

**Definition 3.23**.

```agda
_ = Nucleus.isNuclear
_ = Nucleus.Nucleus
```

**Proposition 3.24**.

```agda
_ = Nucleus.nuclei-resp-⊤
```

**Lemma 3.25**. This is broken up into two functions in the Agda formalisatoin.

```agda
_ = Frame.x⊑y⇒x=x∧y
_ = Frame.x=x∧y⇒x⊑y
```

**Proposition 3.26**.

```agda
_ = Nucleus.mono
```

**Proposition 3.27**.

```agda
_ = Nucleus.𝔣𝔦𝔵-pos
```

**Theorem 3.28**.

```agda
_ = Nucleus.𝔣𝔦𝔵
```

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
