# Semantics With Applications
## 5.3 Safety of analysis

---

## 概要

解析関数${\cal PA,PB,PS}$がそれぞれ、${\cal A,B,S_{ds}}$に関して正しいことを示す。

具体的には、次の3つの関係を示していく。
- ${\cal A}[\\![a]\\!]\ {\rm \underline{sat}_{Aexp}}\ {\cal PA}[\\![a]\\!]$
- ${\cal B}[\\![b]\\!]\ {\rm \underline{sat}_{Bexp}}\ {\cal PB}[\\![b]\\!]$
- $${\cal S}\_{\rm ds}[\\![S]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![S]\\!]$$

---

# Expressions

---

$g:{\bf State \to Z},\ h:{\bf PState \to P}$とする。  
解析$h$が意味論$g$に関して正しいことを、$g\ {\rm \underline{sat}_{Aexp}}\ h$と表す。

$g\ {\rm \underline{sat}\_{Aexp}}\ h$  
$\Leftrightarrow s\_1 \equiv s\_2\ {\rm \underline{rel}\_{Stm}}\ ps$ ならば、 $g\ s\_1 \equiv g\ s\_2\ {\rm \underline{rel}\_{Aexp}}\ h\ ps$  
$\Leftrightarrow s\_1 \equiv s\_2\ {\rm \underline{rel}\_{Stm}}\ ps$ かつ $h\ ps = {\rm OK}$ ならば、 $g\ s\_1 = g\ s\_2$

- - -

**(おさらい)**

$v\_1 \equiv v\_2\ {\rm \underline{rel}\_{Aexp}}\ p \Leftrightarrow p = D?$ または $v\_1\ = v\_2$  
$s\_1 \equiv s\_2\ {\rm \underline{rel}\_{Stm}}\ ps \Leftrightarrow ps\ {\rm on \verb|-| track} = D?$ または $\forall x \in {\bf Var} \cap {\rm OK}(ps):\ s_1\ x=s_2\ x$

---

**事実 5.29**

任意の$a \in {\bf Aexp}$について${\cal A}[\\![a]\\!]\ {\rm \underline{sat}_{Aexp}}\ {\cal PA}[\\![a]\\!]$

**[証明]**

補題 1.11と練習 5.11より明らか。

--

**[証明の補足]**

${\cal A}[\\![a]\\!]\ {\rm \underline{sat}\_{Aexp}}\ {\cal PA}[\\![a]\\!]$  
$\Leftrightarrow s\_1 \equiv s\_2\ {\rm \underline{rel}\_{Stm}}\ ps$ かつ ${\cal PA}[\\![a]\\!]ps = {\rm OK}$ ならば、 ${\cal A}[\\![a]\\!]s\_1 = {\cal A}[\\![a]\\!]s\_2$

**補題 1.11**

任意の$x \in {\rm FV}(a)$について$s\ x=s'\ x$ならば、${\cal A}[\\![a]\\!]s={\cal A}[\\![a]\\!]s'$

**練習 5.11**

${\cal PA}[\\![a]\\!]ps = {\rm OK} \Leftrightarrow {\rm FV}(a) \cup {\rm \\{on \verb|-| track\\}} \subseteq {\rm OK}(ps)$

---

**練習 5.30**

${\rm \underline{sat}\_{Bexp}}$を定義し、任意の$b \in {\bf Bexp}$について${\cal B}[\\![b]\\!]\ {\rm \underline{sat}_{Bexp}}\ {\cal PB}[\\![b]\\!]$
となることを示せ。

---

**[解答]**

$g:{\bf State \to T},\ h:{\bf PState \to P}$として、$g\ {\rm \underline{sat}\_{Bexp}}\ h$を次のように定義する。  
$g\ {\rm \underline{sat}\_{Bexp}}\ h$  
$\Leftrightarrow s\_1 \equiv s\_2\ {\rm \underline{rel}\_{Stm}}\ ps$ならば、$g\ s\_1 \equiv g\ s\_2\ {\rm \underline{rel}\_{Bexp}}\ h\ ps$

練習 1.12と練習 5.11より明らかに${\cal B}[\\![b]\\!]\ {\rm \underline{sat}_{Bexp}}\ {\cal PB}[\\![b]\\!]$


---

# Statements

---

$g:{\bf State \to State},\ h:{\bf PState \to PState}$として、$g\ {\rm \underline{sat}\_{Stm}}\ h$を定義する。
  
$g\ {\rm \underline{sat}\_{Stm}}\ h$  
$\Updownarrow$  
$s\_1 \equiv s\_2\ {\rm \underline{rel}}\ ps$ かつ $h\ ps$が適当ならば、  
$g\ s\_1 = {\rm \underline{undef}},\ g\ s\_2 = {\rm \underline{undef}}$ または  
$g\ s\_1 \ne {\rm \underline{undef}},\ g\ s\_2 \ne {\rm \underline{undef}},\ g\ s\_1 \equiv g\ s\_2\ {\rm \underline{rel}}\ h\ ps$

つまり、${\cal S}\_{\rm ds}[\\![S]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![S]\\!]$とは、$S$の実行前の状態について$s\_1 \equiv s\_2\ {\rm \underline{rel}}\ ps$ならば、$S$は$s\_1,s\_2$上でともにループするか、$S$の実行後においても関係が保たれるということを表す。

---

**定理 5.31**

任意のWhile言語の文$S$について${\cal S}\_{\rm ds}[\\![S]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![S]\\!]$

- - -

これを証明するために、補題を2つ示す。

---

**補題 5.32**

$g\_1,g\_2:{\bf State \hookrightarrow State},\ h\_1,h\_2:{\bf PState \to PState},$  
任意の$ps \in {\bf PState}$について  
$ps\ {\rm on \verb|-| track} \sqsubseteq\_{\rm P} (h\_2\ ps)\ {\rm on \verb|-| track} \tag{*}$  
とすると、次が成り立つ。

$g\_1\ {\rm \underline{sat}\_{Stm}}\ h\_1$かつ$g\_2\ {\rm \underline{sat}\_{Stm}}\ h\_2$ならば、$g\_2 \circ g\_1\ {\rm \underline{sat}\_{Stm}}\ h\_2 \circ h\_1$

---

**[証明]**

$s\_1 \equiv s\_2\ {\rm \underline{rel}}\ ps$ かつ $(h\_2 \circ h\_1)\ ps$が適当であるとする。

(*)より、$h\_2\ (h\_1\ ps)$が適当であることから、$h\_1\ ps$は適当である。

仮定$g\_1\ {\rm \underline{sat}\_{Stm}}\ h\_1$より、  
$g\_1\ s\_1 = {\rm \underline{undef}},\ g\_1\ s\_2 = {\rm \underline{undef}}$ または  
$g\_1\ s\_1 \ne {\rm \underline{undef}},\ g\_1\ s\_2 \ne {\rm \underline{undef}},\ g\_1\ s\_1 \equiv g\_1\ s\_2\ {\rm \underline{rel}}\ h\_1\ ps$

---

前者の場合、  
$(g\_2 \circ g\_1)\ s\_1 = {\rm \underline{undef}}$ かつ $(g\_2 \circ g\_1)\ s\_2 = {\rm \underline{undef}}$

後者の場合、  
$g\_1\ s\_1 \equiv g\_1\ s\_2\ {\rm \underline{rel}}\ h\_1\ ps$ かつ $h\_2(h\_1\ ps)$が適当であることを用いると、  
仮定$g\_2\ {\rm \underline{sat}\_{Stm}}\ h\_2$より、  
$g\_2\ (g\_1\ s\_1) = {\rm \underline{undef}},\ g\_2\ (g\_1\ s\_2) = {\rm \underline{undef}}$ または  
$g\_2\ (g\_1\ s\_1) \ne {\rm \underline{undef}},\ g\_2\ (g\_1\ s\_2) \ne {\rm \underline{undef}},\ g\_2\ (g\_1\ s\_1) \equiv g\_2\ (g\_1\ s\_2)\ {\rm \underline{rel}}\ h\_2\ (h\_1\ ps)$

したがって、両者ともに$g\_2 \circ g\_1\ {\rm \underline{sat}\_{Stm}}\ h\_2 \circ h\_1$が示された。

---

**補題 5.33**

$g\_1,g\_2:{\bf State \hookrightarrow State},\ g:{\bf State \to T},$  
$h\_1,h\_2:{\bf PState \to PState},\ f:{\bf PState \to P}$  
とすると、次が成り立つ。

$g\ {\rm \underline{sat}\_{Bexp}}\ f,\ g\_1\ {\rm \underline{sat}\_{Stm}}\ h\_1,\ g\_2\ {\rm \underline{sat}\_{Stm}}\ h\_2$ならば、${\rm cond}(g,g\_1,g\_2)\ {\rm \underline{sat}\_{Stm}}\ {\rm cond\_P}(f,h\_1,h\_2)$

---

[証明]  
$s\_1 \equiv s\_2\ {\rm \underline{rel}}\ ps$ かつ ${\rm cond\_P}(f,h\_1,h\_2)\ ps$が適当であるとする。

$f\ ps = {\rm D?}$と仮定すると、${\rm cond\_P}(f,h\_1,h\_2)\ ps = {\rm LOST}$となり、${\rm cond\_P}(f,h\_1,h\_2)\ ps$が適当でなくなるため矛盾。

したがって$f\ ps = {\rm OK}$となり、$g\ {\rm \underline{sat}\_{Bexp}}\ f$より$g\ s\_1 = g\ s\_2$  
また、${\rm cond\_P}(f,h\_1,h\_2)\ ps = (h\_1\ ps) \sqcup\_{\rm PS} (h\_2\ ps)$  
$g$によって選ばれる分岐を$i$で表すことにすると、  
$s\_1 \equiv s\_2\ {\rm \underline{rel}}\ ps$ かつ $h\_i\ ps$は適当である。

仮定$g\_i\ {\rm \underline{sat}\_{Stm}}\ h\_i$より、  
$g\_i\ s\_1 = {\rm \underline{undef}},\ g\_i\ s\_2 = {\rm \underline{undef}}$ または  
$g\_i\ s\_1 \ne {\rm \underline{undef}},\ g\_i\ s\_2 \ne {\rm \underline{undef}},\ g\_i\ s\_1 \equiv g\_i\ s\_2\ {\rm \underline{rel}}\ h\_i\ ps$

---

前者の場合、  
${\rm cond}(g,g\_1,g\_2)\ s\_1 = {\rm \underline{undef}},\ {\rm cond}(g,g\_1,g\_2)\ s\_2 = {\rm \underline{undef}}$

後者の場合、  
${\rm cond}(g,g\_1,g\_2)\ s\_1 \ne {\rm \underline{undef}},\ {\rm cond}(g,g\_1,g\_2)\ s\_2 \ne {\rm \underline{undef}},$  
${\rm cond}(g,g\_1,g\_2)\ s\_1 \equiv {\rm cond}(g,g\_1,g\_2)\ s\_2\ {\rm \underline{rel}}\ h\_i\ ps$  
明らかに、$h\_i\ ps \sqsubseteq h\_1\ ps \sqcup\_{\rm PS} h\_2\ ps$であり、
${\rm cond\_P}$の定義と補題 5.8より、  
${\rm cond}(g,g\_1,g\_2)\ s\_1 \equiv {\rm cond}(g,g\_1,g\_2)\ s\_2\ {\rm \underline{rel}}\ {\rm cond\_P}(f,h\_1,h\_2)\ ps$

--

**補題 5.8**

${\rm \underline{rel}\_{Stm}}$はクリプキ関係である。

つまり、$ps\_1 \sqsubseteq ps\_2$ならば、任意の$s\_1,s\_2 \in {\bf State}$について$s\_1 \equiv s\_2\ {\rm \underline{rel}\_{Stm}}\ ps\_1 \Rightarrow s\_1 \equiv s\_2\ {\rm \underline{rel}\_{Stm}}\ ps\_2$

---

**[定理 5.31の証明]**

$S$に関する構造的帰納法により、${\cal S}\_{\rm ds}[\\![S]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![S]\\!]$を示す。

---

[$x:=a$の場合]

$s\_1 \equiv s\_2\ {\rm \underline{rel}}\ ps$ かつ ${\cal PS}[\\![x:=a]\\!]ps$が適当であるとする。

練習 5.27より、${\cal PS}[\\![x:=a]\\!]ps$が適当であることから$ps$は適当である。  
また、${\cal S}\_{\rm ds}[\\![x:=a]\\!]s\_1$と${\cal S}\_{\rm ds}[\\![x:=a]\\!]s\_2$は定義されるので、  
任意の$y \in {\bf Var} \cap \{\rm OK}({\cal PS}[\\![x:=a]\\!]ps)$について
$$({\cal S}\_{\rm ds}[\\![x:=a]\\!]s\_1)\ y = ({\cal S}\_{\rm ds}[\\![x:=a]\\!]s\_2)\ y$$
を示せばよい。

$y \ne x,\ y \in \{\rm OK}({\cal PS}[\\![x:=a]\\!]ps)$とすると、$y \in \{\rm OK}(ps)$となり、${\cal S}\_{\rm ds}$の定義より、$({\cal S}\_{\rm ds}[\\![x:=a]\\!]s\_1)\ y = ({\cal S}\_{\rm ds}[\\![x:=a]\\!]s\_2)\ y$

$y = x,\ x \in \{\rm OK}({\cal PS}[\\![x:=a]\\!]ps)$とすると、仮定$s\_1 \equiv s\_2\ {\rm \underline{rel}}\ ps$と$({\cal PS}[\\![x:=a]\\!]ps)\ x = {\rm OK}$を用いて、事実 5.29より、
$${\cal A}[\\![a]\\!]s\_1 = {\cal A}[\\![a]\\!]s\_2$$

--

**練習 5.27**

任意の文$S$について、$ps\ {\rm on \verb|-| track} \sqsubseteq ({\cal PS}[\\![S]\\!]ps)\ {\rm on \verb|-| track}$  
すなわち、${\cal PS}[\\![S]\\!]ps$が適当ならば、$ps$は適当である。

---

[${\rm skip}$の場合]

明らかに、${\cal S}\_{\rm ds}[\\![{\rm skip}]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![{\rm skip}]\\!]$

[$S\_1;S\_2$の場合]

帰納法の仮定より、
$${\cal S}\_{\rm ds}[\\![S\_1]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![S\_1]\\!],\ {\cal S}\_{\rm ds}[\\![S\_2]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![S\_2]\\!]$$

練習 5.27より、任意の$ps$について$ps\ {\rm on \verb|-| track} \sqsubseteq\_{\rm P} ({\cal PS}[\\![S\_2]\\!]ps)\ {\rm on \verb|-| track}$  
したがって、補題 5.32より、
$${\cal S}\_{\rm ds}[\\![S\_2]\\!] \circ {\cal S}\_{\rm ds}[\\![S\_1]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![S\_2]\\!] \circ {\cal PS}[\\![S\_1]\\!]$$

---

[${\rm if}\ b\ {\rm then}\ S\_1\ {\rm else}\ S\_2$の場合]

練習 5.30より、
$${\cal B}[\\![b]\\!]\ {\rm \underline{sat}\_{Bexp}}\ {\cal PB}[\\![b]\\!]$$
帰納法の仮定より、
$${\cal S}\_{\rm ds}[\\![S\_1]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![S\_1]\\!],\ {\cal S}\_{\rm ds}[\\![S\_2]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![S\_2]\\!]$$
補題 5.33より、
$${\rm cond}({\cal B}[\\![b]\\!],{\cal S}\_{\rm ds}[\\![S\_1]\\!],{\cal S}\_{\rm ds}[\\![S\_2]\\!])\ {\rm \underline{sat}\_{Stm}}\ {\rm cond\_P}({\cal PB}[\\![b]\\!],{\cal PS}[\\![S\_1]\\!],{\cal PS}[\\![S\_2]\\!])$$

---

[${\rm while}\ b\ {\rm do}\ S$の場合]

${\rm FIX}(G)\ {\rm \underline{sat}\_{Stm}}\ {\rm FIX}(H)$  
where  
$G\ g = {\rm cond}({\cal B}[\\![b]\\!],g\circ{\cal S}\_{\rm ds}[\\![S]\\!],{\rm id})$  
$H\ h = {\rm cond\_P}({\cal PB}[\\![b]\\!],h\circ{\cal PS}[\\![S]\\!],{\rm id})$  
を示す。

最小不動点の定義は次の通りである。  
${\rm FIX}\ G = \bigsqcup\\{G^n\ g\_0 \mid n \ge 0\\}\ {\rm where}\ g\_0\ s = {\rm \underline{undef}}$  
${\rm FIX}\ H = \bigsqcup\\{H^n\ h\_0 \mid n \ge 0\\}\ {\rm where}\ h\_0\ ps = {\rm INIT}$

まず(\*)を示し、次に(\*\*)を示す。
$$G^n\ g\_0\ {\rm \underline{sat}\_{Stm}}\ {\rm FIX}\ H \tag{\*}$$
$${\rm FIX}\ G\ {\rm \underline{sat}\_{Stm}}\ {\rm FIX}\ H \tag{\*\*}$$

---

(*)を$n$に関する帰納法で示す。 

まず、$g\_0\ s = {\rm \underline{undef}}$であるから、$g\_0\ {\rm \underline{sat}\_{Stm}}\ {\rm FIX}\ H$

次に、$G^n\ g\_0\ {\rm \underline{sat}\_{Stm}}\ {\rm FIX}\ H$と仮定して$n+1$に対する結果を示す。  
練習 5.30より、${\cal B}[\\![b]\\!]\ {\rm \underline{sat}\_{Bexp}}\ {\cal PB}[\\![b]\\!]$  
帰納法の仮定より、${\cal S}\_{\rm ds}[\\![S]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![S]\\!]$  
さらに、明らかに${\rm id}\ {\rm \underline{sat}\_{Stm}}\ {\rm id}$  
また、練習 5.27より、任意の$ps$について$ps\ {\rm on \verb|-| track} \sqsubseteq\_{\rm P} (({\rm FIX}\ H)\ ps)\ {\rm on \verb|-| track}$  

以上を用いて、補題 5.32, 5.33より、
$${\rm cond}({\cal B}[\\![b]\\!],(G^n\ g\_0)\circ{\cal S}\_{\rm ds}[\\![S]\\!],{\rm id})\ {\rm \underline{sat}\_{Stm}}\ {\rm cond\_P}({\cal PB}[\\![b]\\!],({\rm FIX}\ H)\circ{\cal PS}[\\![S]\\!],{\rm id})$$
すなわち、
$$G^{n+1}\ g\_0\ {\rm \underline{sat}\_{Stm}}\ {\rm FIX}\ H$$

---

最後に(**)すなわち$\bigsqcup  Y\ {\rm \underline{sat}\_{Stm}}\ {\rm FIX}\ H\ {\rm where}\ Y = \\{G^n\ g\_0 \mid n \ge 0\\}$を示す。

$s\_1 \equiv s\_2\ {\rm \underline{rel}}\ ps$ かつ $({\rm FIX}\ H) \ ps$が適当であるとする。  
(*)より、任意の$g \in Y$について$g\ {\rm \underline{sat}\_{Stm}}\ {\rm FIX}\ H$であるから、  
$g\ s\_1 = {\rm \underline{undef}},\ g\ s\_2 = {\rm \underline{undef}}$ または  
$g\ s\_1 \ne {\rm \underline{undef}},\ g\ s\_2 \ne {\rm \underline{undef}},\ g\ s\_1 \equiv g\ s\_2\ {\rm \underline{rel}}\ ({\rm FIX}\ H)\ ps$

$(\bigsqcup Y)\ s\_1 = {\rm \underline{undef}}$とすると、任意の$g \in Y$について$g\ s\_1 = {\rm \underline{undef}}$  
それにより、任意の$g \in Y$について$g\ s\_2 = {\rm \underline{undef}}$となり、$(\bigsqcup Y)\ s\_2 = {\rm \underline{undef}}$  
同様に、$(\bigsqcup Y)\ s\_2 = {\rm \underline{undef}}$ならば$(\bigsqcup Y)\ s\_1 = {\rm \underline{undef}}$

したがって$(\bigsqcup Y)\ s\_1 \ne {\rm \underline{undef}},\ (\bigsqcup Y)\ s\_2 \ne {\rm \underline{undef}}$の場合について考える。

---

$x \in {\bf Var} \cap {\rm OK}(({\rm FIX}\ H)\ ps)$とする。  
補題 4.25より、
${\rm graph}(\bigsqcup Y) = \bigcup \\{{\rm graph}\ g \mid g \in Y\\}$  
$i = 1,2$について$(\bigsqcup Y)\ s\_i \ne {\rm \underline{undef}}$であるから  
$g\_i\ s\_i \ne {\rm \underline{undef}}$かつ$(\bigsqcup Y)\ s\_i = g\_i\ s\_i$となる$g\_i \in Y$が存在する。

$Y$が鎖であることより$g\_1 \sqsubseteq g\_2$または$g\_2 \sqsubseteq g\_1$であるから、  
大きい方を$g$とすると、

$$
\begin{eqnarray\*}
((\sqcup Y)\ s\_1)\ x &=& (g\_1\ s\_1)\ x\ &\because (\sqcup Y)\ s\_1 = g\_1\ s\_1\\\\
&=& (g\ s\_1)\ x\ &\because g\_1 \sqsubseteq g かつ g\_1\ s\_1 \ne {\rm \underline{undef}}\\\\
&=& (g\ s\_2)\ x\ &\because g\ s\_1 \equiv g\ s\_2\ {\rm \underline{rel}}\ ({\rm FIX}\ H)\ ps\\\\
&=& (g\_2\ s\_2)\ x\ &\because g\_2 \sqsubseteq g かつ g\_2\ s\_2 \ne {\rm \underline{undef}}\\\\
&=& ((\sqcup Y)\ s\_2)\ x\ &\because (\sqcup Y)\ s\_2 = g\_2\ s\_2
\end{eqnarray\*}
$$

---

## まとめ

1. $\bf State \hookrightarrow State$と$\bf PState \to PState$の間に関係$\rm \underline{sat}_{Stm}$を定義した。
2. 表示的意味論で用いられる補助関数と解析関数の間で関係が保存されることを示した。(補題 5.32, 補題 5.33)
3. $S$に関する構造的帰納法により意味関数と解析関数の間に関係が成り立つことを示した。

---

**練習 5.35**

${\cal PS}$の定義において、  
$${\rm cond\_P}(f,h\_1,h\_2)\ ps = \begin{cases}
(h\_1\ ps) \sqcup\_{\rm PS}(h\_2\ ps) & (f\ ps = {\rm OK})\\\\
{\rm LOST} & (f\ ps = {\rm D?})
\end{cases}$$
の代わりに  
$${\rm cond'\_P}(f,h\_1,h\_2)\ ps = (h\_1\ ps) \sqcup\_{\rm PS}(h\_2\ ps)$$
を用いた場合、定理 5.31が成り立たないことを示せ。
---

[解答]

$S\_1 : x:=1,\ S\_2 : x:=2,\ S\_{12} : {\rm if}\ x=1\ {\rm then}\ S\_1\ {\rm else}\ S\_2$とする。

$ps\ x = D?$ かつ $ps\ y = {\rm OK},\ y \in ({\bf Var} \cup {\rm \\{on\verb|-|track\\}}) \setminus \\{x\\}$  
$s\_1\ x = 1$ かつ $s\_1\ y = 0,\ y \in {\rm Var} \setminus \\{x\\}$  
$s\_2\ x = 2$ かつ $s\_2\ y = 0,\ y \in {\rm Var} \setminus \\{x\\}$  
とすると、$s\_1 \equiv s\_2\ {\rm \underline{rel}}\ ps$

また、${\cal PS}[\\![S\_1]\\!]ps$と${\cal PS}[\\![S\_2]\\!]ps$は適当であるから、  
${\cal PS}[\\![S\_{12}]\\!]ps = ({\cal PS}[\\![S\_1]\\!]ps) \sqcup\_{\rm PS}({\cal PS}[\\![S\_2]\\!]ps)$は適当である。

ところが、${\cal S}\_{\rm ds}[\\![S\_{12}]\\!]s\_1 \ne {\rm \underline{undef}},\ {\cal S}\_{\rm ds}[\\![S\_{12}]\\!]s\_2 \ne {\rm \underline{undef}},\ {\cal PS}[\\![S\_{12}]\\!]ps\ x = {\rm OK}$  
であるにも関わらず、${\cal S}\_{\rm ds}[\\![S\_{12}]\\!]s\_1\ x \ne {\cal S}\_{\rm ds}[\\![S\_{12}]\\!]s\_2\ x$となるため、  
${\cal S}\_{\rm ds}[\\![S\_{12}]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![S\_{12}]\\!]$は成り立たない。

---

**練習 5.36**

${\rm cond'\_P}$を次のように改善する。  
${\rm cond'\_P}(f,h\_1,h\_2)\ ps$  
$= \begin{cases}
(h\_1\ ps) \sqcup\_{\rm PS}(h\_2\ ps)\ \ \ \ \ \ \ \ (f\ ps = {\rm OK})\\\\
((h\_1\ ps[{\rm on \verb|-| track \mapsto D?}]) \sqcup\_{\rm PS}(h\_2\ ps[{\rm on \verb|-| track \mapsto D?}]))[{\rm on \verb|-| track \mapsto OK}]\\\\
\ \ \ \ \ \ \ \ (f\ ps = {\rm D?})
\end{cases}$

${\rm cond'\_P}$が${\rm cond\_P}$よりも好ましくなるような文を挙げよ。  
また、${\rm cond\_P}$を${\rm cond'\_P}$に置き換えた場合に安全性の証明は成り立つか。  
成り立たない場合は証明可能な安全性を挙げよ。

---

[解答]

$S\_1 : {\rm skip},\ S\_2 : {\rm while\ true\ do\ skip},\ S\_{12} : {\rm if}\ x=1\ {\rm then}\ S\_1\ {\rm else}\ S\_2$  
$ps\ x = D?,\ ps\ y = {\rm OK},\ y \in ({\bf Var} \cup {\rm \\{on\verb|-|track\\}}) \setminus \\{x\\}$  
$s\_1\ x = 1,\ s\_1\ y = 0,\ y \in {\rm Var} \setminus \\{x\\}$  
$s\_2\ x = 2,\ s\_2\ y = 0,\ y \in {\rm Var} \setminus \\{x\\}$  
とする。

${\rm cond\_P}$を用いた場合、${\cal PS}[\\![S\_{12}]\\!]ps\ {\rm on\verb|-|track} = {\rm D?}$となるが、  
${\rm cond'\_P}$を用いた場合、${\cal PS}[\\![S\_{12}]\\!]ps\ {\rm on\verb|-|track} = {\rm OK}$となり、より好ましい。

一方で、$s\_1 \equiv s\_2\ {\rm \underline{rel}}\ ps$ かつ ${\cal PS}[\\![S\_{12}]\\!]ps$が適当であるにも関わらず、${\cal S}\_{\rm ds}[\\![S\_{12}]\\!]s\_1 \ne {\rm \underline{undef}},\ {\cal S}\_{\rm ds}[\\![S\_{12}]\\!]s\_2 = {\rm \underline{undef}}$となるため、${\cal S}\_{\rm ds}[\\![S\_{12}]\\!]\ {\rm \underline{sat}\_{Stm}}\ {\cal PS}[\\![S\_{12}]\\!]$は成り立たない。

---

${\rm \underline{sat}'\_{Stm}}$を次のように定義すると、${\rm cond'\_P}$を用いた場合には、  
${\cal S}\_{\rm ds}[\\![S]\\!]\ {\rm \underline{sat}'\_{Stm}}\ {\cal PS}[\\![S]\\!]$が成り立つと考えられる。

$g\ {\rm \underline{sat}'\_{Stm}}\ h$  
$\Updownarrow$  
$s\_1 \equiv s\_2\ {\rm \underline{rel}}\ ps,\ g\ s\_1 \ne {\rm \underline{undef}},\ g\ s\_2 \ne {\rm \underline{undef}}$ かつ $h\ ps$が適当ならば、  
$g\ s\_1 \equiv g\ s\_2\ {\rm \underline{rel}}\ h\ ps$