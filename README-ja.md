# yet-another-pss-proof

ペア数列システム (Pair Sequence System, PSS) の停止性の、オリジナルの停止証明と
その Isabelle/HOL による形式証明。

**経緯と本証明の位置づけ。** ペア数列システムは **Bashicu 氏** が考案した。
その停止性は **P進大好きbot 氏** が証明した
（[`pss-original-paper.html`](../pss-original-paper.html)、Buchholz の ψ を用いる）。
**本リポジトリの証明は、P進大好きbot 氏の証明とは無関係な独立のオリジナル証明である**
（同氏の手法・補題には依拠しない）。

本証明はペア数列を **`p_a(b)+c` という独自のオーダー記法** へ変換し、
`(a,b,c)` の3次元超限帰納法で素直に停止性を導く。これは原始数列システム
(Primitive Sequence System, PrSS) の停止証明
（[`prss-proof`](https://github.com/koteitan/prss-proof)）と同じ戦略
（数列を整礎な記法へ写し、展開ステップで測度が真に減少することを示す）を、
ペア数列へ一般化したものである。PSS の強さは ψ₀(ψ_ω(0))（Buchholz ordinal）と
考えられており、添字 `a` を自然数（0,1,2,… とその上限 ω）に取ることに対応する。

## バージョン管理内ファイル

| ファイル | 役割 |
|---|---|
| `README-ja.md` | このファイル。リポジトリ内ファイルの説明。 |
| `proof-ja.md` | markdown + MathJax による数学的証明（上位・人間向け）。できるだけ数式で記述。 |
| `def.thy` | Bashicu 氏のペア数列システムの定義部分（Isabelle）。`pss-original-paper.html` に倣い、論文に忠実な変数名を用いる。 |
| `proofs.thy` | `proof-ja.md` に対応する上位の形式証明（停止性定理本体）。`proof` は Isabelle の予約語のため `proofs` とする。 |
| `mechanized.thy` | `proof-ja.md` では省いた細かい部分（下位）。記法 `p_a(b)+c`、整礎性、translate、減少補題。 |
| `ROOT` | Isabelle セッション `YAPSS` のビルド定義。 |

## ビルド

```sh
isbman build -d . -v YAPSS
```

（`isbman` は同一マシン上で複数の証明を安全に走らせるための Isabelle ビルドマネージャ。）

## 出典・クレジット

- ペア数列システムの考案：Bashicu 氏。
- ペア数列システムの停止性の証明：P進大好きbot 氏「ペア数列の停止性」巨大数研究 Wiki
  （本リポジトリの証明とは無関係な別証明）。
- Koteitan「[Purely mathematical definition of BMS](https://googology.fandom.com/wiki/User_blog:Koteitan/Purely_mathematical_definition_of_BMS)」巨大数研究 Wiki（定義の参照）。
