[← 目次](README.md)

# Final — 仮定を伴わない停止性の結論

本章は、前章までに証明された 2 つの命題、すなわち (I) 標準形における基本列の共終性
（[`AscArg.md`](AscArg.md)）と (II) 反復帰納的集合 $`W_u`$（[(D.W)](Wset.md#d-W)）への所属
（[`Wset.md`](Wset.md)）を合成し、仮定を 1 つも持たない形の停止性
$`\mathrm{WF}(R_{\mathrm{step}})`$ と、無限展開列の非存在を得る。
本章の宣言は 5 個ですべて定理であり、その証明はすべて既証明の定理への引数の代入のみからなる
（本章では帰納法を一切用いない）。
最後に `#print axioms` による機械検査の結果を記録する。

## 記法

この章で用いる Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `Acc R x` | $`\mathrm{Acc}(R,x)`$ | $`x`$ が関係 $`R`$ について到達可能 |
| `WellFounded R` | $`\mathrm{WF}(R)`$ | $`\forall x,\ \mathrm{Acc}(R,x)`$ |
| `fun a b => ST_PS a ∧ ST_PS b ∧ translate a <o translate b` | $`R_{\mathrm{ST}}`$ | 標準形に制限した $`\prec`$ の $`\mathrm{tr}`$ による引き戻し（[(D.Rst)](Wset.md#d-Rst) と同一の式） |
| `Rnf` | $`R_{\mathrm{nf}}`$ | 項側の順序（$`\mathrm{NF}`$ に制限した $`\prec`$） |
| `stepRel` | $`R_{\mathrm{step}}`$ | 標準形上の 1 ステップ関係 |
| `S : ℕ → PairSeq` | $`(S_i)_{i\in\mathbb{N}}`$ | ペア列の無限列 |

既出の記号は次の通りである。

| Lean | 本文 | 定義 |
|---|---|---|
| `PairSeq` | $`\mathrm{PairSeq}`$ | [(D.PairSeq)](Def.md#d-PairSeq) |
| `M.length` | $`\lvert M\rvert`$ | [(D.PairSeq)](Def.md#d-PairSeq) |
| `M⟦n⟧` | $`M[n]`$ | [(D.oper)](Def.md#d-oper) |
| `ST_PS M` | $`M \in \mathrm{ST\_PS}`$ | [(D.ST_PS)](Def.md#d-ST_PS) |
| `step M N` | $`M \Rightarrow N`$ | [(D.step)](Def.md#d-step) |
| `translate M` | $`\mathrm{tr}\,M`$ | [(D.translate)](Mechanized.md#d-translate) |
| `x <o y` | $`x \prec y`$ | [(D.olt)](Mechanized.md#d-olt) |
| `x ≤o y` | $`x \preceq y`$ | [(D.ole)](Mechanized.md#d-ole) |
| `NF` | $`\mathrm{NF}`$ | [(D.NF)](Proofs.md#d-NF) |

### 到達可能性と整礎性

本章の主張はすべて Lean 4 の core に属する 2 つの述語で書かれている。意味を固定しておく。

**関係の向きの規約.** 本証明では、関係 $`R`$ の適用 $`R\,y\,x`$ を「$`y`$ が $`x`$ の下にある」と読む。
すなわち $`R\,y\,x`$ は Isabelle の $`(y,x)\in R`$ に対応する（[`Proofs.md`](Proofs.md) の移植規約）。

**到達可能性 $`\mathrm{Acc}(R,x)`$.** 次の 1 つの導入規則で生成される最小の述語である。

```math
\frac{\ \forall y,\ R\,y\,x \to \mathrm{Acc}(R,y)\ }{\ \mathrm{Acc}(R,x)\ }
```

最小性は次の除去規則（Lean の `Acc.rec`）として用いられる。任意の述語
$`P : \alpha \to \mathrm{Prop}`$ について、

```math
\Bigl(\forall x,\ \bigl(\forall y,\ R\,y\,x \to \mathrm{Acc}(R,y)\bigr)
 \to \bigl(\forall y,\ R\,y\,x \to P(y)\bigr) \to P(x)\Bigr)
 \ \Longrightarrow\ \forall x,\ \mathrm{Acc}(R,x) \to P(x).
```

**整礎性 $`\mathrm{WF}(R)`$.** Lean の `WellFounded R` は構成子
`intro : (∀ x, Acc R x) → WellFounded R` を唯一持つ帰納型であり、逆向きの射影
`WellFounded.apply : WellFounded R → ∀ x, Acc R x` を持つ。したがって

```math
\mathrm{WF}(R) \iff \forall x,\ \mathrm{Acc}(R,x)
```

であり、本文ではこの同値を断りなく用いる。

## 証明全体の依存関係

本章の 5 定理に至る経路を、モジュール単位で示す。図中の `★` 印は本章の宣言である。

```
[Def]         PairSeq,  M[n],  ST_PS,  M ⇒ N
  │
[Mechanized]  tr,  ≺,  ≼ ────────── m_step_decreases ───────────────┐
  │                                                                │
  ├─[Wf]─[Wfsum]─[Otembed]─[Gterm0Olt]─[Seqlex]─[Nrm]─[Nrmstep]     │
  │                │                                               │
  │                ├─[Cofinality]  pss_cofinality_of_argdom        │
  │                │        │                                      │
  │                │     [AscArg]  argDomCore_holds                │
  │                │        │      ascArgDom_of_core               │
  │                │        │      pss_cofinality_of_core          │
  │                │        ▼                                      │
  │                │     ★ pss_cofinality_holds          … (I)     │
  │                │        │                                      │
  │                └─[Wset]  W_membership,  acc_of_W     … (II)    │
  │                         │  wf_of_cofinality_and_membership     │
  │                         │  wf_olt_ST_PS_of_cofinality          │
  │                         ▼                                      │
  │                      ★ wf_olt_ST_PS_holds                      │
  │                         │                                      │
  │             [OrdinalFree]  acc_Rnf_of_acc_PS                    │
  │                         │  wf_Rnf_of_wf_PS                     │
  │                         ▼                                      │
  │                      ★ wf_Rnf_holds                            │
  │                         │                                      │
  └───────────────[Proofs]  step_terminates ◄─────────────────────┘
                            no_infinite_expansion
                            │
                            ▼
                      ★ PSS_terminates_unconditional
                      ★ no_infinite_expansion_holds
```

図中の各名前の所在とリンクは次の通りである。

| 名前 | 所在 | 役割 |
|---|---|---|
| [(T.m_step_decreases)](Mechanized.md#t-m_step_decreases) | Mechanized | $`1<\lvert M\rvert`$, $`1\le n`$ ならば $`\mathrm{tr}(M[n]) \prec \mathrm{tr}\,M`$ |
| [(D.ArgDomCore)](AscArg.md#d-ArgDomCore) | AscArg | 単一標準形の内部で述べた引数支配の命題 |
| [(T.argDomCore_holds)](AscArg.md#t-argDomCore_holds) | AscArg | $`\mathrm{ArgDomCore}`$ が成り立つ |
| [(T.ascArgDom_of_core)](AscArg.md#t-ascArgDom_of_core) | AscArg | $`\mathrm{ArgDomCore} \to \mathrm{AscArgDom}`$（[(D.AscArgDom)](Cofinality.md#d-AscArgDom)） |
| [(T.pss_cofinality_of_argdom)](Cofinality.md#t-pss_cofinality_of_argdom) | Cofinality | $`\mathrm{AscArgDom}`$ から共終性 |
| [(T.pss_cofinality_of_core)](AscArg.md#t-pss_cofinality_of_core) | AscArg | 上 2 つの合成 |
| [(T.W_membership)](Wset.md#t-W_membership) | Wset | $`\forall M \in \mathrm{ST\_PS},\ \exists u,\ M \in W_u`$ |
| [(T.acc_of_W)](Wset.md#t-acc_of_W) | Wset | 共終性の下で $`M \in W_u \to \mathrm{Acc}(R_{\mathrm{ST}},M)`$ |
| [(T.wf_of_cofinality_and_membership)](Wset.md#t-wf_of_cofinality_and_membership) | Wset | 上 2 つの合成 |
| [(T.wf_olt_ST_PS_of_cofinality)](Wset.md#t-wf_olt_ST_PS_of_cofinality) | Wset | 共終性 $`\to \mathrm{WF}(R_{\mathrm{ST}})`$ |
| [(T.acc_Rnf_of_acc_PS)](OrdinalFree.md#t-acc_Rnf_of_acc_PS) | OrdinalFree | 到達可能性を $`\mathrm{tr}`$ に沿って移す |
| [(T.wf_Rnf_of_wf_PS)](OrdinalFree.md#t-wf_Rnf_of_wf_PS) | OrdinalFree | $`\mathrm{WF}(R_{\mathrm{ST}}) \to \mathrm{WF}(R_{\mathrm{nf}})`$ |
| [(T.step_terminates)](Proofs.md#t-step_terminates) | Proofs | $`\mathrm{WF}(R_{\mathrm{nf}}) \to \mathrm{WF}(R_{\mathrm{step}})`$ |
| [(T.no_infinite_expansion)](Proofs.md#t-no_infinite_expansion) | Proofs | $`\mathrm{WF}(R_{\mathrm{nf}}) \to`$ 無限展開列の非存在 |

[(T.m_step_decreases)](Mechanized.md#t-m_step_decreases) は
[(T.step_terminates)](Proofs.md#t-step_terminates) と
[(T.no_infinite_expansion)](Proofs.md#t-no_infinite_expansion) の内部で使われており、
本章の証明本文には現れない。図の右端の縦線はその依存を表す。

---

## 主定理

<a id="t-pss_cofinality_holds"></a>
### 定理 PSS Bachmann 共終性（無仮定） (T.pss_cofinality_holds)

**主張** 任意の $`M, N \in \mathrm{PairSeq}`$ について、

```math
M \in \mathrm{ST\_PS},\quad N \in \mathrm{ST\_PS},\quad \mathrm{tr}\,N \prec \mathrm{tr}\,M
```

ならば

```math
\exists n,\ \bigl(1 \le n \ \wedge\ \mathrm{tr}\,N \preceq \mathrm{tr}(M[n])\bigr).
```

**証明** 引用する定理は
[(T.pss_cofinality_of_core)](AscArg.md#t-pss_cofinality_of_core) であり、その形は

```math
\mathrm{ArgDomCore} \ \to\ \forall M, N,\
 M \in \mathrm{ST\_PS} \to N \in \mathrm{ST\_PS} \to \mathrm{tr}\,N \prec \mathrm{tr}\,M
 \to \exists n,\ \bigl(1 \le n \wedge \mathrm{tr}\,N \preceq \mathrm{tr}(M[n])\bigr)
```

である（$`\mathrm{ArgDomCore}`$ は [(D.ArgDomCore)](AscArg.md#d-ArgDomCore)）。
第 1 引数には [(T.argDomCore_holds)](AscArg.md#t-argDomCore_holds) を代入する。これは
$`\mathrm{ArgDomCore}`$ という命題そのものの証明であるから、型は一致する。
残る 3 つの引数 $`M \in \mathrm{ST\_PS}`$、$`N \in \mathrm{ST\_PS}`$、$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ には
本定理の仮定をそのまま渡す。結論は求める式である。∎

**注意（主張の内容）.** この定理は、$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ をみたす標準形 $`N`$ に対し、
$`\mathrm{tr}\,N \preceq \mathrm{tr}(M[n])`$ をみたす基本列の項 $`M[n]`$ が $`n \ge 1`$ の範囲に存在することを
述べている。$`n \ge 1`$ という制限は [(D.ST_PS)](Def.md#d-ST_PS) の規則 (oper) の前提そのものであるから、
$`M \in \mathrm{ST\_PS}`$ と合わせて $`M[n] \in \mathrm{ST\_PS}`$ が従う。
さらに $`1 < \lvert M\rvert`$ であれば [(D.step)](Def.md#d-step) の規則 (step\_oper) の前提も満たされ、
$`M \Rightarrow M[n]`$ が成り立つ。
この命題が $`W_u`$ 側の到達可能性の議論
[(T.acc_of_W)](Wset.md#t-acc_of_W) の唯一の外部入力である。

<a id="t-wf_olt_ST_PS_holds"></a>
### 定理 標準形に制限した $`\prec`$ の整礎性（無仮定） (T.wf_olt_ST_PS_holds)

**主張** 関係

```math
R_{\mathrm{ST}}\,a\,b \ :\Longleftrightarrow\
 a \in \mathrm{ST\_PS} \ \wedge\ b \in \mathrm{ST\_PS} \ \wedge\ \mathrm{tr}\,a \prec \mathrm{tr}\,b
```

について $`\mathrm{WF}(R_{\mathrm{ST}})`$ が成り立つ。すなわち
$`\forall M \in \mathrm{PairSeq},\ \mathrm{Acc}(R_{\mathrm{ST}}, M)`$。

**証明** 引用する定理は
[(T.wf_olt_ST_PS_of_cofinality)](Wset.md#t-wf_olt_ST_PS_of_cofinality)（Lean の完全名は
`YAPSS.Wset.wf_olt_ST_PS_of_cofinality`）であり、その形は

```math
\Bigl(\forall M, N,\ M \in \mathrm{ST\_PS} \to N \in \mathrm{ST\_PS}
 \to \mathrm{tr}\,N \prec \mathrm{tr}\,M
 \to \exists n,\ \bigl(1 \le n \wedge \mathrm{tr}\,N \preceq \mathrm{tr}(M[n])\bigr)\Bigr)
 \ \to\ \mathrm{WF}(R_{\mathrm{ST}})
```

である。この仮定は [(T.pss_cofinality_holds)](#t-pss_cofinality_holds) の主張と
一字一句同じ命題であるから、それを代入して結論を得る。∎

**注意（Lean 側の $`\eta`$ 展開）.** Lean のソースでは
`Wset.wf_olt_ST_PS_of_cofinality (fun hM hN h => pss_cofinality_holds hM hN h)` と書かれている。
`pss_cofinality_holds` の $`M, N`$ は暗黙引数 `{M N : PairSeq}` であり、これを引数位置に
そのまま置くと Lean は暗黙引数をメタ変数として直ちに具体化してしまう。
`fun hM hN h => …` と $`\eta`$ 展開することで、$`M, N`$ が仮定 `hM hN h` から決まる形に
再抽象化される。命題としては同一であり、数学的な内容は上の代入に尽きる。

<a id="t-wf_Rnf_holds"></a>
### 定理 項側順序 $`R_{\mathrm{nf}}`$ の整礎性（無仮定） (T.wf_Rnf_holds)

**主張** $`\mathrm{WF}(R_{\mathrm{nf}})`$。ここで
[(D.Rnf)](Proofs.md#d-Rnf), [(D.NF)](Proofs.md#d-NF) により

```math
R_{\mathrm{nf}}\,v\,u \ :\Longleftrightarrow\ v \prec u \ \wedge\ u \in \mathrm{NF} \ \wedge\ v \in \mathrm{NF},
\qquad
\mathrm{NF} = \{\, t \mid \exists M,\ M \in \mathrm{ST\_PS} \wedge \mathrm{tr}\,M = t \,\}
```

である。

**証明** 引用する定理は [(T.wf_Rnf_of_wf_PS)](OrdinalFree.md#t-wf_Rnf_of_wf_PS) であり、その形は

```math
\mathrm{WF}(R_{\mathrm{ST}}) \ \to\ \mathrm{WF}(R_{\mathrm{nf}})
```

で、仮定に現れる関係は
[(T.wf_olt_ST_PS_holds)](#t-wf_olt_ST_PS_holds) の結論に現れる関係と同じ式
$`\lambda a\,b.\ a \in \mathrm{ST\_PS} \wedge b \in \mathrm{ST\_PS} \wedge \mathrm{tr}\,a \prec \mathrm{tr}\,b`$
である。よって [(T.wf_olt_ST_PS_holds)](#t-wf_olt_ST_PS_holds) を代入して結論を得る。∎

<a id="t-PSS_terminates_unconditional"></a>
### 定理 PSS の停止性（無仮定） (T.PSS_terminates_unconditional)

**主張** $`\mathrm{WF}(R_{\mathrm{step}})`$。ここで [(D.stepRel)](Proofs.md#d-stepRel) により

```math
R_{\mathrm{step}}\,T\,M \ :\Longleftrightarrow\ M \in \mathrm{ST\_PS} \ \wedge\ M \Rightarrow T
```

である（$`M \Rightarrow T`$ は [(D.step)](Def.md#d-step)）。

**証明** 引用する定理は [(T.step_terminates)](Proofs.md#t-step_terminates) であり、その形は

```math
\mathrm{WF}(R_{\mathrm{nf}}) \ \to\ \mathrm{WF}(R_{\mathrm{step}})
```

である。仮定に [(T.wf_Rnf_holds)](#t-wf_Rnf_holds) を代入して結論を得る。∎

**注意（主張の内容）.** 上の「到達可能性と整礎性」の同値により、この主張は

```math
\forall M \in \mathrm{PairSeq},\ \mathrm{Acc}(R_{\mathrm{step}}, M)
```

と同じである。関係の向きの規約により $`R_{\mathrm{step}}\,T\,M`$ は「$`T`$ が $`M`$ の 1 ステップ下」を
意味する。ここから「$`R_{\mathrm{step}}`$ に関する無限下降列が存在しない」を導くのが次の定理であり、
その導出は [(T.no_infinite_expansion)](Proofs.md#t-no_infinite_expansion) の内部で、
上に述べた $`\mathrm{Acc}`$ の除去規則を述語
$`P(x) :\equiv \forall i,\ S_i = x \to \bot`$ に適用することで行われている。

<a id="t-no_infinite_expansion_holds"></a>
### 定理 無限展開列の非存在（無仮定） (T.no_infinite_expansion_holds)

**主張**

```math
\neg\ \exists S : \mathbb{N} \to \mathrm{PairSeq},\
 \Bigl(\bigl(\forall i,\ S_i \in \mathrm{ST\_PS}\bigr) \ \wedge\
 \bigl(\forall i,\ S_i \Rightarrow S_{i+1}\bigr)\Bigr).
```

すなわち、すべての項が標準形であり、かつ各項から次の項へ 1 ステップ展開
[(D.step)](Def.md#d-step) で移るような無限列 $`(S_i)_{i\in\mathbb{N}}`$ は存在しない。

**証明** 引用する定理は [(T.no_infinite_expansion)](Proofs.md#t-no_infinite_expansion) であり、その形は

```math
\mathrm{WF}(R_{\mathrm{nf}}) \ \to\
 \neg\ \exists S : \mathbb{N} \to \mathrm{PairSeq},\
 \bigl((\forall i,\ S_i \in \mathrm{ST\_PS}) \wedge (\forall i,\ S_i \Rightarrow S_{i+1})\bigr)
```

である。仮定に [(T.wf_Rnf_holds)](#t-wf_Rnf_holds) を代入して結論を得る。∎

---

## 公理検査

Lean ファイル `lean/YAPSS/Final.lean` の末尾には、本章の 5 定理に対する `#print axioms`
コマンドが置かれている。これらは宣言ではなく、証明項が依存する公理を列挙させる指示である。
実行結果は次の通りであった（本 md の作成時に、ビルド済み `olean` を読み込む別ファイルから
再実行して確認した）。

```
'YAPSS.pss_cofinality_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'YAPSS.wf_olt_ST_PS_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'YAPSS.wf_Rnf_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'YAPSS.PSS_terminates_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'YAPSS.no_infinite_expansion_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

この 3 つは Lean 4 / Mathlib の標準公理である。

- `propext` : 命題外延性。$`\forall p\, q : \mathrm{Prop},\ (p \leftrightarrow q) \to p = q`$。
- `Classical.choice` : 選択公理。$`\forall \alpha,\ \mathrm{Nonempty}\,\alpha \to \alpha`$。
  たとえば [(D.parent)](Def.md#d-parent) の $`\varepsilon`$ 作用素、および
  `by_cases` が用いる排中律が、この公理に依存する。
- `Quot.sound` : 商の健全性。$`\forall \alpha,\ \forall r : \alpha \to \alpha \to \mathrm{Prop},\ \forall a\, b : \alpha,\ r\,a\,b \to \mathrm{Quot.mk}\,r\,a = \mathrm{Quot.mk}\,r\,b`$。

一覧に `sorryAx` が現れないことが、未証明の穴が存在しないことの機械検査である。
また、名前付きの仮定（`axiom` 宣言や `variable` として置かれた命題）も現れていない。
したがって本章の 5 定理は、Lean 4 / Mathlib の標準公理のみに依存する。

**用いていない道具について.** `lean/YAPSS/Final.lean` 冒頭のコメントは、この経路が
順序数評価写像 `oV`、Buchholz の `OT`/`wf3` 埋め込み、および係数支配の事実
（`H0clause` / `Gterm` 由来のもの）のいずれも用いないことを記録している。
ただし上の `#print axioms` が保証するのは、公理と `sorryAx` を使っていないことのみであって、
この「どの補題を使っていないか」という記述ではない。
本章はこの記述の検証を行っていない。

<!-- TODO: 「oV / OT / wf3 / H0clause をこの経路が用いない」という Lean 側コメントの主張は、
     証明項の依存宣言を機械的に列挙して確認するのが本来である（例: 依存グラフの走査）。
     本章では未検証のまま、出典を明示して引用するにとどめた。 -->
