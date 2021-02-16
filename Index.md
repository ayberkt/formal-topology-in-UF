<pre class="Agda"><a id="9" class="Symbol">{-#</a> <a id="13" class="Keyword">OPTIONS</a> <a id="21" class="Pragma">--cubical</a> <a id="31" class="Pragma">--safe</a> <a id="38" class="Symbol">#-}</a>

<a id="43" class="Keyword">module</a> <a id="50" href="Index.html" class="Module">Index</a> <a id="56" class="Keyword">where</a>

<a id="63" class="Keyword">import</a> <a id="70" href="Basis.html" class="Module">Basis</a>
<a id="76" class="Keyword">open</a> <a id="81" class="Keyword">import</a> <a id="88" href="FormalTopology.html" class="Module">FormalTopology</a>
<a id="103" class="Keyword">open</a> <a id="108" class="Keyword">import</a> <a id="115" href="Cover.html" class="Module">Cover</a>

<a id="122" class="Keyword">import</a> <a id="129" href="Poset.html" class="Module">Poset</a>
<a id="135" class="Keyword">import</a> <a id="142" href="Frame.html" class="Module">Frame</a>

<a id="149" class="Keyword">import</a> <a id="156" href="Nucleus.html" class="Module">Nucleus</a>
<a id="164" class="Keyword">import</a> <a id="171" href="CoverFormsNucleus.html" class="Module">CoverFormsNucleus</a>
<a id="189" class="Keyword">import</a> <a id="196" href="UniversalProperty.html" class="Module">UniversalProperty</a>

<a id="215" class="Keyword">import</a> <a id="222" href="Cubical.Relation.Nullary.html" class="Module">Cubical.Relation.Nullary</a>
<a id="247" class="Keyword">import</a> <a id="254" href="Cubical.Relation.Nullary.DecidableEq.html" class="Module">Cubical.Relation.Nullary.DecidableEq</a>
<a id="291" class="Keyword">import</a> <a id="298" href="Cubical.Foundations.Univalence.html" class="Module">Cubical.Foundations.Univalence</a>
<a id="329" class="Keyword">import</a> <a id="336" href="Cubical.Foundations.SIP.html" class="Module">Cubical.Foundations.SIP</a>

<a id="361" class="Keyword">open</a> <a id="366" class="Keyword">import</a> <a id="373" href="Cubical.Data.Bool.html" class="Module">Cubical.Data.Bool</a> <a id="391" class="Keyword">using</a> <a id="397" class="Symbol">(</a><a id="398" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a><a id="402" class="Symbol">;</a> <a id="404" href="Cubical.Data.Bool.Base.html#980" class="Function Operator">_≟_</a><a id="407" class="Symbol">)</a>

<a id="410" class="Keyword">open</a> <a id="415" class="Keyword">import</a> <a id="422" href="SnocList.html" class="Module">SnocList</a> <a id="431" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a> <a id="436" href="Cubical.Data.Bool.Base.html#980" class="Function Operator">_≟_</a>
<a id="440" class="Keyword">import</a> <a id="447" href="Compactness.html" class="Module">Compactness</a>
<a id="459" class="Keyword">import</a> <a id="466" href="CantorSpace.html" class="Module">CantorSpace</a>
</pre>
## Chapter 2: Foundations

### 2.3: Equivalence and univalence

**Definition 2.1**.

<pre class="Agda"><a id="576" href="Index.html#576" class="Function">_</a> <a id="578" class="Symbol">=</a> <a id="580" href="Cubical.Foundations.Prelude.html#10084" class="Function">Basis.isContr</a>
</pre>
**Definition 2.2**.

<pre class="Agda"><a id="628" href="Index.html#628" class="Function">_</a> <a id="630" class="Symbol">=</a> <a id="632" href="Cubical.Foundations.Equiv.Base.html#281" class="Function">Basis.fiber</a>
</pre>
**Definition 2.3**.

<pre class="Agda"><a id="678" href="Index.html#678" class="Function">_</a> <a id="680" class="Symbol">=</a> <a id="682" href="Agda.Builtin.Cubical.Glue.html#868" class="Record">Basis.isEquiv</a>
</pre>
**Definition 2.4**.

<pre class="Agda"><a id="730" href="Index.html#730" class="Function">_</a> <a id="732" class="Symbol">=</a> <a id="734" href="Agda.Builtin.Cubical.Glue.html#1051" class="Function Operator">Basis._≃_</a>
</pre>
**Definition 2.5**.

<pre class="Agda"><a id="778" href="Index.html#778" class="Function">_</a> <a id="780" class="Symbol">=</a> <a id="782" href="Cubical.Foundations.Equiv.Base.html#578" class="Function">Basis.idEquiv</a>
</pre>
**Definition 2.6**.

<pre class="Agda"><a id="830" href="Index.html#830" class="Function">_</a> <a id="832" class="Symbol">=</a> <a id="834" href="Cubical.Foundations.Univalence.html#8113" class="Function">Cubical.Foundations.Univalence.pathToEquiv</a>
</pre>
**Definition 2.7**.

<pre class="Agda"><a id="911" href="Index.html#911" class="Function">_</a> <a id="913" class="Symbol">=</a> <a id="915" href="Basis.html#4312" class="Function Operator">Basis._~_</a>
</pre>
**Proposition 2.8**.

<pre class="Agda"><a id="960" href="Index.html#960" class="Function">_</a> <a id="962" class="Symbol">=</a> <a id="964" href="Cubical.Foundations.Prelude.html#7957" class="Function">Basis.funExt</a>
</pre>
### 2.4: Homotopy levels

**Definition 2.9**.

<pre class="Agda"><a id="1037" href="Index.html#1037" class="Function">_</a> <a id="1039" class="Symbol">=</a> <a id="1041" href="Cubical.Foundations.HLevels.html#1106" class="Function">Basis.isOfHLevel</a>
</pre>
**Proposition 2.10**.

<pre class="Agda"><a id="1094" href="Index.html#1094" class="Function">_</a> <a id="1096" class="Symbol">=</a> <a id="1098" href="Cubical.Foundations.HLevels.html#1725" class="Function">Basis.isOfHLevelSuc</a>
</pre>
**Proposition 2.11**.

<pre class="Agda"><a id="1154" href="Index.html#1154" class="Function">_</a> <a id="1156" class="Symbol">=</a> <a id="1158" href="Cubical.Foundations.HLevels.html#13903" class="Function">Basis.isOfHLevelΠ</a>
</pre>
**Proposition 2.12**.

<pre class="Agda"><a id="1212" href="Index.html#1212" class="Function">_</a> <a id="1214" class="Symbol">=</a> <a id="1216" href="Cubical.Foundations.HLevels.html#12100" class="Function">Basis.isOfHLevelΣ</a>
</pre>
Definition 2.13 is omitted.

**Definition 2.14**.

<pre class="Agda"><a id="1298" href="Index.html#1298" class="Function">_</a> <a id="1300" class="Symbol">=</a> <a id="1302" href="Cubical.Foundations.Prelude.html#10148" class="Function">Basis.isProp</a>
</pre>
Proposition 2.15 is omitted.

**Definition 2.16**.

<pre class="Agda"><a id="1380" href="Index.html#1380" class="Function">_</a> <a id="1382" class="Symbol">=</a> <a id="1384" href="Cubical.Foundations.HLevels.html#1500" class="Function">Basis.hProp</a>
</pre>
**Proposition 2.17**.

<pre class="Agda"><a id="1432" href="Index.html#1432" class="Function">_</a> <a id="1434" class="Symbol">=</a> <a id="1436" href="Cubical.Foundations.HLevels.html#14996" class="Function">Basis.isPropΠ</a>
</pre>
**Proposition 2.18**.

<pre class="Agda"><a id="1486" href="Index.html#1486" class="Function">_</a> <a id="1488" class="Symbol">=</a> <a id="1490" href="Cubical.Foundations.HLevels.html#11983" class="Function">Basis.isPropΣ</a>
</pre>
**Proposition 2.19**.

<pre class="Agda"><a id="1540" href="Index.html#1540" class="Function">_</a> <a id="1542" class="Symbol">=</a> <a id="1544" href="Cubical.Foundations.Prelude.html#14239" class="Function">Basis.isPropIsProp</a>
</pre>
**Proposition 2.20**.

<pre class="Agda"><a id="1599" href="Index.html#1599" class="Function">_</a> <a id="1601" class="Symbol">=</a> <a id="1603" href="Cubical.Data.Sigma.Properties.html#11948" class="Function">Basis.Σ≡Prop</a>
</pre>
**Definition 2.21**. This is defined directly for h-propositions in the
`cubical` library.

<pre class="Agda"><a id="1721" href="Index.html#1721" class="Function">_</a> <a id="1723" class="Symbol">=</a> <a id="1725" href="Cubical.Functions.Logic.html#4258" class="Function Operator">Basis._⇔_</a>
</pre>
**Proposition 2.22**.

<pre class="Agda"><a id="1771" href="Index.html#1771" class="Function">_</a> <a id="1773" class="Symbol">=</a> <a id="1775" href="Cubical.Functions.Logic.html#2055" class="Function">Basis.⇔toPath</a>
</pre>
**Definition 2.23**.

<pre class="Agda"><a id="1824" href="Index.html#1824" class="Function">_</a> <a id="1826" class="Symbol">=</a> <a id="1828" href="Cubical.Foundations.Isomorphism.html#798" class="Record">Basis.Iso</a>
</pre>
**Proposition 2.24**.

<pre class="Agda"><a id="1874" href="Index.html#1874" class="Function">_</a> <a id="1876" class="Symbol">=</a> <a id="1878" href="Cubical.Foundations.Isomorphism.html#3152" class="Function">Basis.isoToEquiv</a>
<a id="1895" href="Index.html#1895" class="Function">_</a> <a id="1897" class="Symbol">=</a> <a id="1899" href="Cubical.Foundations.Equiv.html#2861" class="Function">Basis.equivToIso</a>
</pre>
**Definition 2.25**.

<pre class="Agda"><a id="1951" href="Index.html#1951" class="Function">_</a> <a id="1953" class="Symbol">=</a> <a id="1955" href="Cubical.Foundations.Prelude.html#10203" class="Function">Basis.isSet</a>
</pre>
**Proposition 2.26**.

<pre class="Agda"><a id="2003" href="Index.html#2003" class="Function">_</a> <a id="2005" class="Symbol">=</a> <a id="2007" href="Cubical.Foundations.Prelude.html#13767" class="Function">Basis.isProp→isSet</a>
</pre>
**Proposition 2.27**.

<pre class="Agda"><a id="2062" href="Index.html#2062" class="Function">_</a> <a id="2064" class="Symbol">=</a> <a id="2066" href="Cubical.Foundations.HLevels.html#19559" class="Function">Basis.isSetHProp</a>
</pre>
**Proposition 2.28**.

<pre class="Agda"><a id="2119" href="Index.html#2119" class="Function">_</a> <a id="2121" class="Symbol">=</a> <a id="2123" href="Cubical.Foundations.HLevels.html#15852" class="Function">Basis.isSetΠ</a>
</pre>
**Proposition 2.29**.

<pre class="Agda"><a id="2172" href="Index.html#2172" class="Function">_</a> <a id="2174" class="Symbol">=</a> <a id="2176" href="Cubical.Foundations.HLevels.html#12444" class="Function">Basis.isSetΣ</a>
</pre>
**Proposition 2.30**.

<pre class="Agda"><a id="2225" href="Index.html#2225" class="Function">_</a> <a id="2227" class="Symbol">=</a> <a id="2229" href="Cubical.Foundations.HLevels.html#4402" class="Function">Basis.isPropIsSet</a>
</pre>
**Definition 2.31**.

<pre class="Agda"><a id="2282" href="Index.html#2282" class="Function">_</a> <a id="2284" class="Symbol">=</a> <a id="2286" href="Cubical.Relation.Nullary.Base.html#472" class="Datatype">Cubical.Relation.Nullary.Dec</a>
</pre>
**Definition 2.32**.

<pre class="Agda"><a id="2350" href="Index.html#2350" class="Function">_</a> <a id="2352" class="Symbol">=</a> <a id="2354" href="Cubical.Relation.Nullary.Base.html#1410" class="Function">Cubical.Relation.Nullary.Discrete</a>
</pre>
**Theorem 2.33**.

<pre class="Agda"><a id="2420" href="Index.html#2420" class="Function">_</a> <a id="2422" class="Symbol">=</a> <a id="2424" href="Cubical.Relation.Nullary.Properties.html#5785" class="Function">Cubical.Relation.Nullary.DecidableEq.Discrete→isSet</a>
</pre>
### 2.5: Powersets

**Definition 2.34**.

<pre class="Agda"><a id="2531" href="Index.html#2531" class="Function">_</a> <a id="2533" class="Symbol">=</a> <a id="2535" href="Basis.html#4409" class="Function">Basis.𝒫</a>
</pre>
**Proposition 2.35**.

<pre class="Agda"><a id="2579" href="Index.html#2579" class="Function">_</a> <a id="2581" class="Symbol">=</a> <a id="2583" href="Basis.html#4591" class="Function">Basis.𝒫-set</a>
</pre>
**Definition 2.36**.

<pre class="Agda"><a id="2630" href="Index.html#2630" class="Function">_</a> <a id="2632" class="Symbol">=</a> <a id="2634" href="Basis.html#4840" class="Function Operator">Basis._⊆_</a>
</pre>
**Definition 2.37**.

<pre class="Agda"><a id="2679" href="Index.html#2679" class="Function">_</a> <a id="2681" class="Symbol">=</a> <a id="2683" href="Basis.html#5194" class="Function">Basis.entire</a>
</pre>
**Definition 2.38**.

<pre class="Agda"><a id="2731" href="Index.html#2731" class="Function">_</a> <a id="2733" class="Symbol">=</a> <a id="2735" href="Basis.html#5261" class="Function Operator">Basis._∩_</a>
</pre>
### 2.6: Families

**Definition 2.39**.

<pre class="Agda"><a id="2799" href="Index.html#2799" class="Function">_</a> <a id="2801" class="Symbol">=</a> <a id="2803" href="Basis.html#5634" class="Function">Basis.Fam</a>
</pre>
**Definition 2.41**.

<pre class="Agda"><a id="2848" href="Index.html#2848" class="Function">_</a> <a id="2850" class="Symbol">=</a> <a id="2852" href="Basis.html#5896" class="Function Operator">Basis._ε_</a>
</pre>
**Definition 2.42**.

<pre class="Agda"><a id="2897" href="Index.html#2897" class="Function">_</a> <a id="2899" class="Symbol">=</a> <a id="2901" href="Basis.html#6103" class="Function Operator">Basis._⟨$⟩_</a>
</pre>
**Definition 2.43**.

<pre class="Agda"><a id="2948" href="Index.html#2948" class="Function">_</a> <a id="2950" class="Symbol">=</a> <a id="2952" href="Basis.html#6863" class="Function Operator">Basis.⟪_⟫</a>
</pre>
### 2.8: Truncation

**Definition 2.44**.

<pre class="Agda"><a id="3018" href="Index.html#3018" class="Function">_</a> <a id="3020" class="Symbol">=</a> <a id="3022" href="Basis.html#7710" class="Datatype Operator">Basis.∥_∥</a>
<a id="3032" href="Index.html#3032" class="Function">_</a> <a id="3034" class="Symbol">=</a> <a id="3036" href="Basis.html#7797" class="Function">Basis.∥∥-prop</a>
<a id="3050" href="Index.html#3050" class="Function">_</a> <a id="3052" class="Symbol">=</a> <a id="3054" href="Basis.html#7855" class="Function">Basis.∥∥-rec</a>
</pre>
## Chapter 3: Frames

### 3.1: Partially ordered sets

**Definition 3.1**.

<pre class="Agda"><a id="3156" href="Index.html#3156" class="Function">_</a> <a id="3158" class="Symbol">=</a> <a id="3160" href="Poset.html#2165" class="Function">Poset.Poset</a>
<a id="3172" href="Index.html#3172" class="Function">_</a> <a id="3174" class="Symbol">=</a> <a id="3176" href="Poset.html#1701" class="Function">Poset.PosetStr</a>
<a id="3191" href="Index.html#3191" class="Function">_</a> <a id="3193" class="Symbol">=</a> <a id="3195" href="Poset.html#1264" class="Function">Poset.PosetAx</a>
</pre>
**Definition 3.2**.

<pre class="Agda"><a id="3243" href="Index.html#3243" class="Function">_</a> <a id="3245" class="Symbol">=</a> <a id="3247" href="Poset.html#6742" class="Function">Poset.isDownwardsClosed</a>
<a id="3271" href="Index.html#3271" class="Function">_</a> <a id="3273" class="Symbol">=</a> <a id="3275" href="Poset.html#7061" class="Function">Poset.DCSubset</a>
</pre>
**Proposition 3.3**.

<pre class="Agda"><a id="3325" href="Index.html#3325" class="Function">_</a> <a id="3327" class="Symbol">=</a> <a id="3329" href="Poset.html#7157" class="Function">Poset.DCSubset-set</a>
</pre>
**Proposition 3.4**.

<pre class="Agda"><a id="3383" href="Index.html#3383" class="Function">_</a> <a id="3385" class="Symbol">=</a> <a id="3387" href="Frame.html#18972" class="Function">Frame.DCPoset</a>
</pre>
**Definition 3.5**.

<pre class="Agda"><a id="3435" href="Index.html#3435" class="Function">_</a> <a id="3437" class="Symbol">=</a> <a id="3439" href="Poset.html#4668" class="Function">Poset.isMonotonic</a>
</pre>
**Definition 3.6**.

<pre class="Agda"><a id="3491" href="Index.html#3491" class="Function">_</a> <a id="3493" class="Symbol">=</a> <a id="3495" href="Poset.html#14763" class="Function">Poset.isPosetIso</a>
</pre>
### 3.2: Definition of a frame

**Definition 3.7**.

<pre class="Agda"><a id="3578" href="Index.html#3578" class="Function">_</a> <a id="3580" class="Symbol">=</a> <a id="3582" href="Frame.html#569" class="Function">Frame.RawFrameStr</a>
<a id="3600" href="Index.html#3600" class="Function">_</a> <a id="3602" class="Symbol">=</a> <a id="3604" href="Frame.html#3368" class="Function">Frame.FrameAx</a>
<a id="3618" href="Index.html#3618" class="Function">_</a> <a id="3620" class="Symbol">=</a> <a id="3622" href="Frame.html#3591" class="Function">Frame.FrameStr</a>
</pre>
**Proposition 3.8**.

<pre class="Agda"><a id="3672" href="Index.html#3672" class="Function">_</a> <a id="3674" class="Symbol">=</a> <a id="3676" href="Frame.html#27498" class="Function">Frame.FrameAx-props</a>
</pre>
**Definition 3.9**.

<pre class="Agda"><a id="3730" href="Index.html#3730" class="Function">_</a> <a id="3732" class="Symbol">=</a> <a id="3734" href="Frame.html#16622" class="Function">Frame.isFrameHomomorphism</a>
<a id="3760" href="Index.html#3760" class="Function">_</a> <a id="3762" class="Symbol">=</a> <a id="3764" href="Frame.html#17068" class="Function Operator">Frame._─f→_</a>
<a id="3776" href="Index.html#3776" class="Function">_</a> <a id="3778" class="Symbol">=</a> <a id="3780" href="Frame.html#18647" class="Function Operator">Frame._≅f_</a>
</pre>
**Definition 3.10**.

<pre class="Agda"><a id="3826" href="Index.html#3826" class="Function">_</a> <a id="3828" class="Symbol">=</a> <a id="3830" href="Frame.html#17592" class="Function">Frame.isFrameIso</a>
</pre>
**Definition 3.11** is not explicitly defined. We refer to it in an ad hoc way
by referring to `_≅ₚ_` on the underlying posets.

The equivalence of Defn. 3.10 and Defn. 3.11 is stated only in passing in the
thesis, not as an explicit proposition but is witnessed in the Agda code
by the following function:

<pre class="Agda"><a id="4168" href="Index.html#4168" class="Function">_</a> <a id="4170" class="Symbol">=</a> <a id="4172" href="Frame.html#34623" class="Function">Frame.≅ₚ≃≅f</a>
</pre>
### 3.3: Some properties of frames

**Proposition 3.12**.

<pre class="Agda"><a id="4256" href="Index.html#4256" class="Function">_</a> <a id="4258" class="Symbol">=</a> <a id="4260" href="Frame.html#9820" class="Function">Frame.comm</a>
</pre>
**Lemma 3.13**.

<pre class="Agda"><a id="4301" href="Index.html#4301" class="Function">_</a> <a id="4303" class="Symbol">=</a> <a id="4305" href="Frame.html#11918" class="Function">Frame.flatten</a>
</pre>
**Proposition 3.14**.

<pre class="Agda"><a id="4355" href="Index.html#4355" class="Function">_</a> <a id="4357" class="Symbol">=</a> <a id="4359" href="Frame.html#11389" class="Function">Frame.family-iff</a>
</pre>
**Proposition 3.15**.

<pre class="Agda"><a id="4412" href="Index.html#4412" class="Function">_</a> <a id="4414" class="Symbol">=</a> <a id="4416" href="Frame.html#13246" class="Function">Frame.sym-distr</a>
</pre>
### 3.4: Univalence for frames

**Definition 3.16**.

<pre class="Agda"><a id="4499" href="Index.html#4499" class="Function">_</a> <a id="4501" class="Symbol">=</a> <a id="4503" href="Poset.html#13109" class="Function">Poset.isAMonotonicEqv</a>
</pre>
**Definition 3.17**.

<pre class="Agda"><a id="4560" href="Index.html#4560" class="Function">_</a> <a id="4562" class="Symbol">=</a> <a id="4564" href="Cubical.Foundations.SIP.html#4416" class="Function">Cubical.Foundations.SIP.SIP</a>
</pre>
**Definition 3.18**.

<pre class="Agda"><a id="4627" href="Index.html#4627" class="Function">_</a> <a id="4629" class="Symbol">=</a> <a id="4631" href="Frame.html#25563" class="Function">Frame.isHomoEqv</a>
</pre>
Equation 3.19.

<pre class="Agda"><a id="4676" href="Index.html#4676" class="Function">_</a> <a id="4678" class="Symbol">=</a> <a id="4680" href="Frame.html#28325" class="Function">Frame.≃f≃≡</a>
</pre>
Equation 3.20.

<pre class="Agda"><a id="4720" href="Index.html#4720" class="Function">_</a> <a id="4722" class="Symbol">=</a> <a id="4724" href="Frame.html#28915" class="Function">Frame.≃f≃≅ₚ</a>
</pre>
Equation 3.21.

<pre class="Agda"><a id="4765" href="Index.html#4765" class="Function">_</a> <a id="4767" class="Symbol">=</a> <a id="4769" href="Frame.html#34491" class="Function">Frame.≅ₚ≃≡</a>
</pre>
### 3.5: Frames of downwards-closed subsets

**Theorem 3.22**.

<pre class="Agda"><a id="4857" href="Index.html#4857" class="Function">_</a> <a id="4859" class="Symbol">=</a> <a id="4861" href="Frame.html#19633" class="Function">Frame.DCFrame</a>
</pre>
### 3.6: Nuclei and their fixed points

**Definition 3.23**.

<pre class="Agda"><a id="4950" href="Index.html#4950" class="Function">_</a> <a id="4952" class="Symbol">=</a> <a id="4954" href="Nucleus.html#302" class="Function">Nucleus.isNuclear</a>
<a id="4972" href="Index.html#4972" class="Function">_</a> <a id="4974" class="Symbol">=</a> <a id="4976" href="Nucleus.html#601" class="Function">Nucleus.Nucleus</a>
</pre>
**Proposition 3.24**.

<pre class="Agda"><a id="5028" href="Index.html#5028" class="Function">_</a> <a id="5030" class="Symbol">=</a> <a id="5032" href="Nucleus.html#1730" class="Function">Nucleus.nuclei-resp-⊤</a>
</pre>
**Lemma 3.25**. This is broken up into two functions in the Agda formalisatoin.

<pre class="Agda"><a id="5148" href="Index.html#5148" class="Function">_</a> <a id="5150" class="Symbol">=</a> <a id="5152" href="Frame.html#7479" class="Function">Frame.x⊑y⇒x=x∧y</a>
<a id="5168" href="Index.html#5168" class="Function">_</a> <a id="5170" class="Symbol">=</a> <a id="5172" href="Frame.html#8213" class="Function">Frame.x=x∧y⇒x⊑y</a>
</pre>
**Proposition 3.26**.

<pre class="Agda"><a id="5224" href="Index.html#5224" class="Function">_</a> <a id="5226" class="Symbol">=</a> <a id="5228" href="Nucleus.html#2110" class="Function">Nucleus.mono</a>
</pre>
**Proposition 3.27**.

<pre class="Agda"><a id="5277" href="Index.html#5277" class="Function">_</a> <a id="5279" class="Symbol">=</a> <a id="5281" href="Nucleus.html#5137" class="Function">Nucleus.𝔣𝔦𝔵-pos</a>
</pre>
**Theorem 3.28**.

<pre class="Agda"><a id="5329" href="Index.html#5329" class="Function">_</a> <a id="5331" class="Symbol">=</a> <a id="5333" href="Nucleus.html#6053" class="Function">Nucleus.𝔣𝔦𝔵</a>
</pre>
## Chapter 4: Formal Topology

### 4.1: Interaction systems

**Definition 4.1**.

<pre class="Agda"><a id="5440" href="Index.html#5440" class="Function">_</a> <a id="5442" class="Symbol">=</a> <a id="5444" href="FormalTopology.html#141" class="Function">InteractionStr</a>
<a id="5459" href="Index.html#5459" class="Function">_</a> <a id="5461" class="Symbol">=</a> <a id="5463" href="FormalTopology.html#305" class="Function">InteractionSys</a>
</pre>
**Definition 4.2**.

<pre class="Agda"><a id="5512" href="Index.html#5512" class="Function">_</a> <a id="5514" class="Symbol">=</a> <a id="5516" href="FormalTopology.html#791" class="Function">hasMono</a>
</pre>
**Definition 4.3**.

<pre class="Agda"><a id="5558" href="Index.html#5558" class="Function">_</a> <a id="5560" class="Symbol">=</a> <a id="5562" href="FormalTopology.html#1125" class="Function">hasSimulation</a>
</pre>
**Definition 4.4**.

<pre class="Agda"><a id="5610" href="Index.html#5610" class="Function">_</a> <a id="5612" class="Symbol">=</a> <a id="5614" href="FormalTopology.html#1345" class="Function">FormalTopology</a>
</pre>### 4.2: Cover relation

Note that **Definition 4.5** is not formalised.

**Definition 4.7**.

<pre class="Agda"><a id="5736" href="Index.html#5736" class="Function">_</a> <a id="5738" class="Symbol">=</a> <a id="5740" href="Cover.html#685" class="Datatype Operator">CoverFromFormalTopology._◁_</a>
</pre>
**Proposition 4.8**.

<pre class="Agda"><a id="5803" href="Index.html#5803" class="Function">_</a> <a id="5805" class="Symbol">=</a> <a id="5807" href="Cover.html#1153" class="Function">CoverFromFormalTopology.◁-lem₁</a>
</pre>
**Proposition 4.9**.

<pre class="Agda"><a id="5873" href="Index.html#5873" class="Function">_</a> <a id="5875" class="Symbol">=</a> <a id="5877" href="Cover.html#1864" class="Function">CoverFromFormalTopology.◁-lem₂</a>
</pre>
**Proposition 4.10**.

<pre class="Agda"><a id="5944" href="Index.html#5944" class="Function">_</a> <a id="5946" class="Symbol">=</a> <a id="5948" href="Cover.html#2287" class="Function">CoverFromFormalTopology.◁-lem₃</a>
</pre>
**Proposition 4.11**.

<pre class="Agda"><a id="6015" href="Index.html#6015" class="Function">_</a> <a id="6017" class="Symbol">=</a> <a id="6019" href="Cover.html#2990" class="Function">CoverFromFormalTopology.◁-lem₄</a>
</pre>
### 4.3: Covers are nuclei

**Theorem 4.12**.

<pre class="Agda"><a id="6110" href="Index.html#6110" class="Function">_</a> <a id="6112" class="Symbol">=</a> <a id="6114" href="CoverFormsNucleus.html#1258" class="Function">CoverFormsNucleus.NucleusFrom.𝕛-nuclear</a>
</pre>
### 4.4: Lifting into the generated frame

**Definition 4.13**.

<pre class="Agda"><a id="6232" href="Index.html#6232" class="Function">_</a> <a id="6234" class="Symbol">=</a> <a id="6236" href="CoverFormsNucleus.html#3740" class="Function">CoverFormsNucleus.NucleusFrom.η</a>
</pre>
### 4.5: Formal topologies present

**Definition 4.14**.

<pre class="Agda"><a id="6339" href="Index.html#6339" class="Function">_</a> <a id="6341" class="Symbol">=</a> <a id="6343" href="UniversalProperty.html#561" class="Function">UniversalProperty.represents</a>
</pre>
**Definition 4.15**.

<pre class="Agda"><a id="6407" href="Index.html#6407" class="Function">_</a> <a id="6409" class="Symbol">=</a> <a id="6411" href="UniversalProperty.html#1588" class="Function">UniversalProperty.isFlat</a>
</pre>
**Theorem 4.16**.

The theorem statement is given in:

<pre class="Agda"><a id="6504" href="Index.html#6504" class="Function">_</a> <a id="6506" class="Symbol">=</a> <a id="6508" href="UniversalProperty.html#1858" class="Function">UniversalProperty.universal-prop</a>
</pre>
The proof is given in:

<pre class="Agda"><a id="6578" href="Index.html#6578" class="Function">_</a> <a id="6580" class="Symbol">=</a> <a id="6582" href="UniversalProperty.html#12516" class="Function">UniversalProperty.main</a>
</pre>
**Lemma 4.17**.

<pre class="Agda"><a id="6635" href="Index.html#6635" class="Function">_</a> <a id="6637" class="Symbol">=</a> <a id="6639" href="UniversalProperty.html#2321" class="Function">UniversalProperty.main-lemma</a>
</pre>
**Lemma 4.18**.

<pre class="Agda"><a id="6698" href="Index.html#6698" class="Function">_</a> <a id="6700" class="Symbol">=</a> <a id="6702" href="UniversalProperty.html#7362" class="Function">UniversalProperty.MainProof.resp-⋁-lem</a>
</pre>
## Chapter 5: The Cantor space

### 5.1: The Cantor interaction system

**Definition 5.1**.

<pre class="Agda"><a id="6847" href="Index.html#6847" class="Function">_</a> <a id="6849" class="Symbol">=</a> <a id="6851" href="SnocList.html#466" class="InductiveConstructor Operator">SnocList._⌢_</a>
<a id="6864" href="Index.html#6864" class="Function">_</a> <a id="6866" class="Symbol">=</a> <a id="6868" href="SnocList.html#449" class="InductiveConstructor">SnocList.[]</a>
</pre>
**Definition 5.2**.

<pre class="Agda"><a id="6914" href="Index.html#6914" class="Function">_</a> <a id="6916" class="Symbol">=</a> <a id="6918" href="SnocList.html#1952" class="Function Operator">_++_</a>
</pre>
**Proposition 5.3**.

<pre class="Agda"><a id="6958" href="Index.html#6958" class="Function">_</a> <a id="6960" class="Symbol">=</a> <a id="6962" href="SnocList.html#1303" class="Function">SnocList-discrete</a>
</pre>
**Definition 5.4**.

<pre class="Agda"><a id="7014" href="Index.html#7014" class="Function">_</a> <a id="7016" class="Symbol">=</a> <a id="7018" href="CantorSpace.html#1234" class="Function">CantorSpace.ℂ-pos</a>
</pre>
**Definition 5.5**.

<pre class="Agda"><a id="7070" href="Index.html#7070" class="Function">_</a> <a id="7072" class="Symbol">=</a> <a id="7074" href="CantorSpace.html#3233" class="Function">CantorSpace.ℂ-IS</a>
</pre>
**Theorem 5.6**.

<pre class="Agda"><a id="7122" href="Index.html#7122" class="Function">_</a> <a id="7124" class="Symbol">=</a> <a id="7126" href="CantorSpace.html#4331" class="Function">CantorSpace.cantor</a>
</pre>
### 5.2: The Cantor space is compact

**Definition 5.7**.

<pre class="Agda"><a id="7217" href="Index.html#7217" class="Function">_</a> <a id="7219" class="Symbol">=</a> <a id="7221" href="Compactness.html#537" class="Function">Compactness.down</a>
</pre>
**Definition 5.8**.

<pre class="Agda"><a id="7272" href="Index.html#7272" class="Function">_</a> <a id="7274" class="Symbol">=</a> <a id="7276" href="Compactness.html#668" class="Function">Compactness.isCompact</a>
</pre>
**Lemma 5.9**.

<pre class="Agda"><a id="7327" href="Index.html#7327" class="Function">_</a> <a id="7329" class="Symbol">=</a> <a id="7331" href="CantorSpace.html#5552" class="Function">CantorSpace.U⊆V⇒◁U⊆◁V</a>
</pre>
**Lemma 5.10**. In the Agda formalisation, this is broken up into two functions.

<pre class="Agda"><a id="7448" href="Index.html#7448" class="Function">_</a> <a id="7450" class="Symbol">=</a> <a id="7452" href="CantorSpace.html#5749" class="Function">CantorSpace.↓-++-left</a>
<a id="7474" href="Index.html#7474" class="Function">_</a> <a id="7476" class="Symbol">=</a> <a id="7478" href="CantorSpace.html#6159" class="Function">CantorSpace.↓-++-right</a>
</pre>
**Lemma 5.11**.

<pre class="Agda"><a id="7531" href="Index.html#7531" class="Function">_</a> <a id="7533" class="Symbol">=</a> <a id="7535" href="CantorSpace.html#6756" class="Function">CantorSpace.◁^-decide</a>
</pre>
**Theorem 5.12**.

<pre class="Agda"><a id="7589" href="Index.html#7589" class="Function">_</a> <a id="7591" class="Symbol">=</a> <a id="7593" href="CantorSpace.html#5493" class="Function">CantorSpace.compact</a>
</pre>