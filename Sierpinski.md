---
title: Sierpinski
---

<pre class="Agda"><a id="36" class="Symbol">{-#</a> <a id="40" class="Keyword">OPTIONS</a> <a id="48" class="Pragma">--cubical</a> <a id="58" class="Pragma">--safe</a> <a id="65" class="Symbol">#-}</a>

<a id="70" class="Keyword">module</a> <a id="77" href="Sierpinski.html" class="Module">Sierpinski</a> <a id="88" class="Keyword">where</a>

<a id="95" class="Keyword">open</a> <a id="100" class="Keyword">import</a> <a id="107" href="Basis.html" class="Module">Basis</a> <a id="113" class="Keyword">hiding</a> <a id="120" class="Symbol">(</a><a id="121" href="Basis.html#3346" class="Datatype">Bool</a><a id="125" class="Symbol">)</a>
<a id="127" class="Keyword">open</a> <a id="132" class="Keyword">import</a> <a id="139" href="Cubical.Data.Bool.html" class="Module">Cubical.Data.Bool</a>
<a id="157" class="Keyword">open</a> <a id="162" class="Keyword">import</a> <a id="169" href="Poset.html" class="Module">Poset</a>
<a id="175" class="Keyword">open</a> <a id="180" class="Keyword">import</a> <a id="187" href="FormalTopology.html" class="Module">FormalTopology</a>

<a id="𝕊-pos"></a><a id="203" href="Sierpinski.html#203" class="Function">𝕊-pos</a> <a id="209" class="Symbol">:</a> <a id="211" href="Poset.html#2165" class="Function">Poset</a> <a id="217" href="Cubical.Core.Primitives.html#1145" class="Primitive">ℓ-zero</a> <a id="224" href="Cubical.Core.Primitives.html#1145" class="Primitive">ℓ-zero</a>
<a id="231" href="Sierpinski.html#203" class="Function">𝕊-pos</a> <a id="237" class="Symbol">=</a> <a id="239" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a> <a id="244" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="246" class="Symbol">(</a><a id="247" href="Sierpinski.html#309" class="Function Operator">_≤_</a> <a id="251" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="253" href="Cubical.Data.Bool.Properties.html#1229" class="Function">isSetBool</a> <a id="263" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="265" class="Symbol">(</a><a id="266" href="Sierpinski.html#466" class="Function">≤-refl</a> <a id="273" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="275" href="Sierpinski.html#547" class="Function">≤-trans</a> <a id="283" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="285" href="Sierpinski.html#682" class="Function">≤-antisym</a><a id="294" class="Symbol">))</a>
  <a id="299" class="Keyword">where</a>
    <a id="309" href="Sierpinski.html#309" class="Function Operator">_≤_</a> <a id="313" class="Symbol">:</a> <a id="315" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a> <a id="320" class="Symbol">→</a> <a id="322" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a> <a id="327" class="Symbol">→</a> <a id="329" href="Cubical.Foundations.HLevels.html#1500" class="Function">hProp</a> <a id="335" href="Cubical.Core.Primitives.html#1145" class="Primitive">ℓ-zero</a>
    <a id="346" class="Symbol">_</a>     <a id="352" href="Sierpinski.html#309" class="Function Operator">≤</a> <a id="354" href="Agda.Builtin.Bool.html#188" class="InductiveConstructor">true</a>  <a id="360" class="Symbol">=</a> <a id="362" href="Basis.html#3101" class="Datatype">Unit</a> <a id="367" href="Cubical.Core.Primitives.html#1145" class="Primitive">ℓ-zero</a> <a id="374" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="376" href="Basis.html#3148" class="Function">Unit-prop</a>
    <a id="390" href="Agda.Builtin.Bool.html#182" class="InductiveConstructor">false</a> <a id="396" href="Sierpinski.html#309" class="Function Operator">≤</a> <a id="398" href="Agda.Builtin.Bool.html#182" class="InductiveConstructor">false</a> <a id="404" class="Symbol">=</a> <a id="406" href="Basis.html#3101" class="Datatype">Unit</a> <a id="411" href="Cubical.Core.Primitives.html#1145" class="Primitive">ℓ-zero</a> <a id="418" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="420" href="Basis.html#3148" class="Function">Unit-prop</a>
    <a id="434" href="Agda.Builtin.Bool.html#188" class="InductiveConstructor">true</a>  <a id="440" href="Sierpinski.html#309" class="Function Operator">≤</a> <a id="442" href="Agda.Builtin.Bool.html#182" class="InductiveConstructor">false</a> <a id="448" class="Symbol">=</a> <a id="450" href="Basis.html#3268" class="Function">bot</a> <a id="454" href="Cubical.Core.Primitives.html#1145" class="Primitive">ℓ-zero</a>

    <a id="466" href="Sierpinski.html#466" class="Function">≤-refl</a> <a id="473" class="Symbol">:</a> <a id="475" class="Symbol">(</a><a id="476" href="Sierpinski.html#476" class="Bound">x</a> <a id="478" class="Symbol">:</a> <a id="480" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a><a id="484" class="Symbol">)</a> <a id="486" class="Symbol">→</a> <a id="488" href="Basis.html#1600" class="Function Operator">[</a> <a id="490" href="Sierpinski.html#476" class="Bound">x</a> <a id="492" href="Sierpinski.html#309" class="Function Operator">≤</a> <a id="494" href="Sierpinski.html#476" class="Bound">x</a> <a id="496" href="Basis.html#1600" class="Function Operator">]</a>
    <a id="502" href="Sierpinski.html#466" class="Function">≤-refl</a> <a id="509" href="Agda.Builtin.Bool.html#182" class="InductiveConstructor">false</a> <a id="515" class="Symbol">=</a> <a id="517" href="Basis.html#3135" class="InductiveConstructor">tt</a>
    <a id="524" href="Sierpinski.html#466" class="Function">≤-refl</a> <a id="531" href="Agda.Builtin.Bool.html#188" class="InductiveConstructor">true</a>  <a id="537" class="Symbol">=</a> <a id="539" href="Basis.html#3135" class="InductiveConstructor">tt</a>

    <a id="547" href="Sierpinski.html#547" class="Function">≤-trans</a> <a id="555" class="Symbol">:</a> <a id="557" class="Symbol">(</a><a id="558" href="Sierpinski.html#558" class="Bound">x</a> <a id="560" href="Sierpinski.html#560" class="Bound">y</a> <a id="562" href="Sierpinski.html#562" class="Bound">z</a> <a id="564" class="Symbol">:</a> <a id="566" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a><a id="570" class="Symbol">)</a> <a id="572" class="Symbol">→</a> <a id="574" href="Basis.html#1600" class="Function Operator">[</a> <a id="576" href="Sierpinski.html#558" class="Bound">x</a> <a id="578" href="Sierpinski.html#309" class="Function Operator">≤</a> <a id="580" href="Sierpinski.html#560" class="Bound">y</a> <a id="582" href="Basis.html#1600" class="Function Operator">]</a> <a id="584" class="Symbol">→</a> <a id="586" href="Basis.html#1600" class="Function Operator">[</a> <a id="588" href="Sierpinski.html#560" class="Bound">y</a> <a id="590" href="Sierpinski.html#309" class="Function Operator">≤</a> <a id="592" href="Sierpinski.html#562" class="Bound">z</a> <a id="594" href="Basis.html#1600" class="Function Operator">]</a> <a id="596" class="Symbol">→</a> <a id="598" href="Basis.html#1600" class="Function Operator">[</a> <a id="600" href="Sierpinski.html#558" class="Bound">x</a> <a id="602" href="Sierpinski.html#309" class="Function Operator">≤</a> <a id="604" href="Sierpinski.html#562" class="Bound">z</a> <a id="606" href="Basis.html#1600" class="Function Operator">]</a>
    <a id="612" href="Sierpinski.html#547" class="Function">≤-trans</a> <a id="620" href="Sierpinski.html#620" class="Bound">x</a> <a id="622" href="Agda.Builtin.Bool.html#182" class="InductiveConstructor">false</a> <a id="628" href="Agda.Builtin.Bool.html#182" class="InductiveConstructor">false</a> <a id="634" href="Sierpinski.html#634" class="Bound">p</a> <a id="636" href="Sierpinski.html#636" class="Bound">q</a> <a id="638" class="Symbol">=</a> <a id="640" href="Sierpinski.html#634" class="Bound">p</a>
    <a id="646" href="Sierpinski.html#547" class="CatchallClause Function">≤-trans</a><a id="653" class="CatchallClause"> </a><a id="654" href="Sierpinski.html#654" class="CatchallClause Bound">x</a><a id="655" class="CatchallClause"> </a><a id="656" href="Sierpinski.html#656" class="CatchallClause Bound">y</a><a id="657" class="CatchallClause">     </a><a id="662" href="Agda.Builtin.Bool.html#188" class="CatchallClause InductiveConstructor">true</a><a id="666" class="CatchallClause">  </a><a id="668" href="Sierpinski.html#668" class="CatchallClause Bound">p</a><a id="669" class="CatchallClause"> </a><a id="670" href="Sierpinski.html#670" class="CatchallClause Bound">q</a> <a id="672" class="Symbol">=</a> <a id="674" href="Basis.html#3135" class="InductiveConstructor">tt</a>

    <a id="682" href="Sierpinski.html#682" class="Function">≤-antisym</a> <a id="692" class="Symbol">:</a> <a id="694" class="Symbol">(</a><a id="695" href="Sierpinski.html#695" class="Bound">x</a> <a id="697" href="Sierpinski.html#697" class="Bound">y</a> <a id="699" class="Symbol">:</a> <a id="701" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a><a id="705" class="Symbol">)</a> <a id="707" class="Symbol">→</a> <a id="709" href="Basis.html#1600" class="Function Operator">[</a> <a id="711" href="Sierpinski.html#695" class="Bound">x</a> <a id="713" href="Sierpinski.html#309" class="Function Operator">≤</a> <a id="715" href="Sierpinski.html#697" class="Bound">y</a> <a id="717" href="Basis.html#1600" class="Function Operator">]</a> <a id="719" class="Symbol">→</a> <a id="721" href="Basis.html#1600" class="Function Operator">[</a> <a id="723" href="Sierpinski.html#697" class="Bound">y</a> <a id="725" href="Sierpinski.html#309" class="Function Operator">≤</a> <a id="727" href="Sierpinski.html#695" class="Bound">x</a> <a id="729" href="Basis.html#1600" class="Function Operator">]</a> <a id="731" class="Symbol">→</a> <a id="733" href="Sierpinski.html#695" class="Bound">x</a> <a id="735" href="Agda.Builtin.Cubical.Path.html#381" class="Function Operator">≡</a> <a id="737" href="Sierpinski.html#697" class="Bound">y</a>
    <a id="743" href="Sierpinski.html#682" class="Function">≤-antisym</a> <a id="753" href="Agda.Builtin.Bool.html#182" class="InductiveConstructor">false</a> <a id="759" href="Agda.Builtin.Bool.html#182" class="InductiveConstructor">false</a> <a id="765" href="Sierpinski.html#765" class="Bound">p</a> <a id="767" href="Sierpinski.html#767" class="Bound">q</a> <a id="769" class="Symbol">=</a> <a id="771" href="Cubical.Foundations.Prelude.html#898" class="Function">refl</a>
    <a id="780" href="Sierpinski.html#682" class="Function">≤-antisym</a> <a id="790" href="Agda.Builtin.Bool.html#188" class="InductiveConstructor">true</a>  <a id="796" href="Agda.Builtin.Bool.html#188" class="InductiveConstructor">true</a>  <a id="802" href="Sierpinski.html#802" class="Bound">p</a> <a id="804" href="Sierpinski.html#804" class="Bound">q</a> <a id="806" class="Symbol">=</a> <a id="808" href="Cubical.Foundations.Prelude.html#898" class="Function">refl</a>

<a id="𝕊-exp"></a><a id="814" href="Sierpinski.html#814" class="Function">𝕊-exp</a> <a id="820" class="Symbol">:</a> <a id="822" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a> <a id="827" class="Symbol">→</a> <a id="829" href="Cubical.Core.Primitives.html#1230" class="Primitive">Type</a> <a id="834" href="Cubical.Core.Primitives.html#1145" class="Primitive">ℓ-zero</a>
<a id="841" href="Sierpinski.html#814" class="Function">𝕊-exp</a> <a id="847" class="Symbol">_</a> <a id="849" class="Symbol">=</a> <a id="851" href="Basis.html#3101" class="Datatype">Unit</a> <a id="856" href="Cubical.Core.Primitives.html#1145" class="Primitive">ℓ-zero</a>

<a id="𝕊-out"></a><a id="864" href="Sierpinski.html#864" class="Function">𝕊-out</a> <a id="870" class="Symbol">:</a> <a id="872" class="Symbol">{</a><a id="873" href="Sierpinski.html#873" class="Bound">x</a> <a id="875" class="Symbol">:</a> <a id="877" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a><a id="881" class="Symbol">}</a> <a id="883" class="Symbol">→</a> <a id="885" href="Sierpinski.html#814" class="Function">𝕊-exp</a> <a id="891" href="Sierpinski.html#873" class="Bound">x</a> <a id="893" class="Symbol">→</a> <a id="895" href="Cubical.Core.Primitives.html#1230" class="Primitive">Type</a> <a id="900" href="Cubical.Core.Primitives.html#1145" class="Primitive">ℓ-zero</a>
<a id="907" href="Sierpinski.html#864" class="Function">𝕊-out</a> <a id="913" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="916" class="Symbol">=</a> <a id="918" href="Basis.html#3101" class="Datatype">Unit</a> <a id="923" href="Cubical.Core.Primitives.html#1145" class="Primitive">ℓ-zero</a>

<a id="𝕊-rev"></a><a id="931" href="Sierpinski.html#931" class="Function">𝕊-rev</a> <a id="937" class="Symbol">:</a> <a id="939" class="Symbol">{</a><a id="940" href="Sierpinski.html#940" class="Bound">x</a> <a id="942" class="Symbol">:</a> <a id="944" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a><a id="948" class="Symbol">}</a> <a id="950" class="Symbol">{</a><a id="951" href="Sierpinski.html#951" class="Bound">y</a> <a id="953" class="Symbol">:</a> <a id="955" href="Sierpinski.html#814" class="Function">𝕊-exp</a> <a id="961" href="Sierpinski.html#940" class="Bound">x</a><a id="962" class="Symbol">}</a> <a id="964" class="Symbol">→</a> <a id="966" href="Sierpinski.html#864" class="Function">𝕊-out</a> <a id="972" class="Symbol">{</a><a id="973" href="Sierpinski.html#940" class="Bound">x</a><a id="974" class="Symbol">}</a> <a id="976" href="Sierpinski.html#951" class="Bound">y</a> <a id="978" class="Symbol">→</a> <a id="980" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a>
<a id="985" href="Sierpinski.html#931" class="Function">𝕊-rev</a> <a id="991" class="Symbol">{</a><a id="992" class="Argument">x</a> <a id="994" class="Symbol">=</a> <a id="996" href="Sierpinski.html#996" class="Bound">x</a><a id="997" class="Symbol">}</a> <a id="999" class="Symbol">{</a><a id="1000" class="Argument">y</a> <a id="1002" class="Symbol">=</a> <a id="1004" href="Basis.html#3135" class="InductiveConstructor">tt</a><a id="1006" class="Symbol">}</a> <a id="1008" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1011" class="Symbol">=</a> <a id="1013" href="Sierpinski.html#996" class="Bound">x</a>

<a id="𝕊-IS"></a><a id="1016" href="Sierpinski.html#1016" class="Function">𝕊-IS</a> <a id="1021" class="Symbol">:</a> <a id="1023" href="FormalTopology.html#141" class="Function">InteractionStr</a> <a id="1038" href="Agda.Builtin.Bool.html#163" class="Datatype">Bool</a>
<a id="1043" href="Sierpinski.html#1016" class="Function">𝕊-IS</a> <a id="1048" class="Symbol">=</a> <a id="1050" href="Sierpinski.html#814" class="Function">𝕊-exp</a> <a id="1056" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1058" class="Symbol">(λ</a> <a id="1061" class="Symbol">{</a><a id="1062" href="Sierpinski.html#1062" class="Bound">x</a><a id="1063" class="Symbol">}</a> <a id="1065" class="Symbol">→</a> <a id="1067" href="Sierpinski.html#864" class="Function">𝕊-out</a> <a id="1073" class="Symbol">{</a><a id="1074" href="Sierpinski.html#1062" class="Bound">x</a><a id="1075" class="Symbol">})</a> <a id="1078" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1080" href="Sierpinski.html#931" class="Function">𝕊-rev</a>

<a id="𝕊"></a><a id="1087" href="Sierpinski.html#1087" class="Function">𝕊</a> <a id="1089" class="Symbol">:</a> <a id="1091" href="FormalTopology.html#1345" class="Function">FormalTopology</a> <a id="1106" href="Cubical.Core.Primitives.html#1145" class="Primitive">ℓ-zero</a> <a id="1113" href="Cubical.Core.Primitives.html#1145" class="Primitive">ℓ-zero</a>
<a id="1120" href="Sierpinski.html#1087" class="Function">𝕊</a> <a id="1122" class="Symbol">=</a> <a id="1124" href="Sierpinski.html#203" class="Function">𝕊-pos</a> <a id="1130" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1132" href="Sierpinski.html#1016" class="Function">𝕊-IS</a> <a id="1137" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1139" href="Sierpinski.html#1174" class="Function">𝕊-has-mono</a> <a id="1150" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1152" href="Sierpinski.html#1275" class="Function">𝕊-has-sim</a>
  <a id="1164" class="Keyword">where</a>
    <a id="1174" href="Sierpinski.html#1174" class="Function">𝕊-has-mono</a> <a id="1185" class="Symbol">:</a> <a id="1187" href="FormalTopology.html#791" class="Function">hasMono</a> <a id="1195" href="Sierpinski.html#203" class="Function">𝕊-pos</a> <a id="1201" href="Sierpinski.html#1016" class="Function">𝕊-IS</a>
    <a id="1210" href="Sierpinski.html#1174" class="Function">𝕊-has-mono</a> <a id="1221" href="Agda.Builtin.Bool.html#182" class="InductiveConstructor">false</a> <a id="1227" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1230" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1233" class="Symbol">=</a> <a id="1235" href="Basis.html#3135" class="InductiveConstructor">tt</a>
    <a id="1242" href="Sierpinski.html#1174" class="Function">𝕊-has-mono</a> <a id="1253" href="Agda.Builtin.Bool.html#188" class="InductiveConstructor">true</a>  <a id="1259" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1262" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1265" class="Symbol">=</a> <a id="1267" href="Basis.html#3135" class="InductiveConstructor">tt</a>

    <a id="1275" href="Sierpinski.html#1275" class="Function">𝕊-has-sim</a>  <a id="1286" class="Symbol">:</a> <a id="1288" href="FormalTopology.html#1125" class="Function">hasSimulation</a> <a id="1302" href="Sierpinski.html#203" class="Function">𝕊-pos</a> <a id="1308" href="Sierpinski.html#1016" class="Function">𝕊-IS</a>
    <a id="1317" href="Sierpinski.html#1275" class="Function">𝕊-has-sim</a> <a id="1327" href="Agda.Builtin.Bool.html#182" class="InductiveConstructor">false</a> <a id="1333" href="Agda.Builtin.Bool.html#182" class="InductiveConstructor">false</a> <a id="1339" href="Sierpinski.html#1339" class="Bound">x</a> <a id="1341" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1344" class="Symbol">=</a> <a id="1346" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1349" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1351" class="Symbol">λ</a> <a id="1353" class="Symbol">{</a> <a id="1355" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1358" class="Symbol">→</a> <a id="1360" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1363" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1365" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1368" class="Symbol">}</a>
    <a id="1374" href="Sierpinski.html#1275" class="Function">𝕊-has-sim</a> <a id="1384" href="Agda.Builtin.Bool.html#182" class="InductiveConstructor">false</a> <a id="1390" href="Agda.Builtin.Bool.html#188" class="InductiveConstructor">true</a>  <a id="1396" href="Sierpinski.html#1396" class="Bound">x</a> <a id="1398" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1401" class="Symbol">=</a> <a id="1403" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1406" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1408" class="Symbol">λ</a> <a id="1410" class="Symbol">{</a> <a id="1412" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1415" class="Symbol">→</a> <a id="1417" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1420" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1422" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1425" class="Symbol">}</a>
    <a id="1431" href="Sierpinski.html#1275" class="Function">𝕊-has-sim</a> <a id="1441" href="Agda.Builtin.Bool.html#188" class="InductiveConstructor">true</a>  <a id="1447" href="Agda.Builtin.Bool.html#188" class="InductiveConstructor">true</a>  <a id="1453" href="Sierpinski.html#1453" class="Bound">x</a> <a id="1455" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1458" class="Symbol">=</a> <a id="1460" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1463" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1465" class="Symbol">λ</a> <a id="1467" class="Symbol">{</a> <a id="1469" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1472" class="Symbol">→</a> <a id="1474" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1477" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="1479" href="Basis.html#3135" class="InductiveConstructor">tt</a> <a id="1482" class="Symbol">}</a>
</pre>