
### ★★(2026-06-10 続9) olt on NF = 数列の列 lex（249500対 全一致）＋Trans 対角の正体
- **実測: 標準形 M,N について olt(translate M, translate N) ⟺ seqlex(M,N)**（列 (r0,r1) の
  辞書式・prefix 小、500 форм 全対 249500 で相違 0）。
  ⟹ translate は (ST_PS, seqlex) ≅ (NF, olt) の順序同型（構文的に証明可能な見込み・要 Isabelle 化）。
  ⟹ wfE ⟺ 「標準形の seqlex 無限降下列が無い」（BMS ネイティブな形）。
- P進 Trans の対角値（content.md 6142）: Trans((u,u)…(v,v)) = **D_u(D_v 0)**（昇順タワー→2段）。
  Trans(標準形) ∈ OT_B は P進が証明済（6124）⟹ 橋の像は wf_olt_wf3 のクラス内。
- 較正実験: oper n ↔ OT bracket z の対応はケース依存（(0,0)(1,1) は n-2、対角3 は n-1）⟹
  経験的 Trans には I–VI の完全実装が必要（pss-proof python に Trans は無い、buchholz.py に
  OT/bracket/in_OT あり流用可）。
- (β1) の最終形: 「seqlex M N ⟹ Trans M <_OT Trans N」（P進 機構のみで閉じる新定理）
  ＋ olt=seqlex（自前）＋ wf_olt_wf3（自前・済）⟹ wfE 完結、ya-pss 前半は丸ごと存続。
- 次手候補: (1) olt=seqlex を Isabelle 化（独立価値・確実）、(2) Trans の Python 実装で
  seqlex-単調性を実測、(3) ユーザーと α/β 最終確認。
