project: yet another PSS termination proof

@pss-original-paper.html に原始数列、ペア数列システムの定義があります。
pss-proof/git/ に P進大好きbot氏の論文をもとにした Pair Sequence System の停止証明のisabelleによる形式証明の途中、prss-proof にオリジナルの原始数列の停止証明とその形式証明（完成)があります。

PrSS(原始数列システム)の停止証明とそのisabelle形式証明を参考にして、これと同じアプローチで、
PSS(ペア数列システム)の停止証明をオリジナルで作り、isabelle形式証明を付けたいです。

PrSSでは、原始数列を Cuntor Normal Form に直し、w^a+b を超限帰納法で停止することを証明しています。
PSSでは、ペア数列システムをBuchholzのψ_α(β)に直すtranslate 関数を作って証明しています。
今回は、ペア数列システムがBuchholzのψとは微妙にずれていくのでPSSが難航しているので、
そのかわりに、Buchholz とはちがう p_a(b)+c に変換することで、より素直な超限帰納法で解ける別のアプローチを目指したいと思います。

ペア数列 (x,y)は、ネスト深さxにあるp_yに変換することができます。
ex. (0,0)=p_0(0)
ex. (0,0)(1,0)=p_0(p_0(0)) (２個目のpは深さが1)
ex. (0,0)(1,1)=p_0(p_1(0))
ex. (0,0)(1,0)(1,0)=p_0(p_0(0)+p_0(0))
ex. (0,0)(1,1)(2,2)(3,3)=p_0(p_1(p_2(p_3(0))))

p_a(b)+c の形に直して a,b,c の３つの減り方をする３次元の超限帰納法で解くことができるのではないかと考えます。

# ファイル構成
ファイル構成を説明します。
* が付いているファイルはまだ存在しないので作成して下さい。

- ./ : バージョン管理外のファイルは個々においてください。(著作権的にアップロードしてはいけないものなど)
- CLAUDE.md : 注意事項などが書いてあります。読んでください。
- request.md : このファイルです。このファイルが編集できるのはユーザーのみです。
- *.md : バージョン管理外の必要なファイルはここにおいてください。
- BM4-Analysis-2021.4.27.xlsx : 実際に存在するstandard な PSSの例。反例探し、健全性チェックなどに使ってください。
- yaBMS/c/bms : expand, standard 判定などPSSのアルゴリズム。
- git/ : バージョン管理下のディレクトリです。koteitan/yet-another-pss-proof が clone されています。
  * proof-ja.md: markdown + mathjax を使った証明。できるだけ数式で書くこと。
  * def.thy: @pss-original-paper.html に対応する部分。
  * proof.thy: proof-ja.md に対応する部分。上位部分。
  * mechanized.thy: proof-ja.md では書かなかった細かい部分。下位部分。

