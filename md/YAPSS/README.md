[← README](../../README-ja.md)

# `md/YAPSS/` — 証明本文の目次

`lean/YAPSS/*.lean` の各モジュールに 1 対 1 で対応する。編集方針は
[`../requirement.md`](../requirement.md)。

**基盤 → 結論の順**に並べる。各ファイルは自分より上の行のファイルの定義・命題のみを引用する。

| # | ファイル | 行数 | 宣言数 | 依存 |
|---:|---|---:|---:|---|
| 1 | [`Def.md`](Def.md) | 132 | 14 | — |
| 2 | [`Mechanized.md`](Mechanized.md) | 998 | 47 | Def |
| 3 | [`Psi.md`](Psi.md) | 124 | 8 | — |
| 4 | [`Proofs.md`](Proofs.md) | 115 | 8 | Mechanized |
| 5 | [`Wf.md`](Wf.md) | 1194 | 45 | Proofs |
| 6 | [`Wfsum.md`](Wfsum.md) | 98 | 6 | Wf |
| 7 | [`Otembed.md`](Otembed.md) | 163 | 15 | Psi,Wfsum |
| 8 | [`Gterm0Olt.md`](Gterm0Olt.md) | 58 | 2 | Mechanized,Otembed |
| 9 | [`Seqlex.md`](Seqlex.md) | 715 | 27 | Wf |
| 10 | [`Nrm.md`](Nrm.md) | 668 | 44 | Otembed |
| 11 | [`Nrmstep.md`](Nrmstep.md) | 2135 | 99 | Nrm,Seqlex |
| 12 | [`Cofinality.md`](Cofinality.md) | 1106 | 41 | Mechanized,Gterm0Olt,Seqlex,Nrmstep |
| 13 | [`AscArg.md`](AscArg.md) | 1930 | 49 | Cofinality |
| 14 | [`Wset.md`](Wset.md) | 2055 | 110 | Nrmstep |
| 15 | [`OrdinalFree.md`](OrdinalFree.md) | 86 | 2 | Cofinality,Wset,Proofs |
| 16 | [`Final.md`](Final.md) | 63 | 5 | AscArg,OrdinalFree |

## 記号の所在

他ファイルで定義された記号を引用するときのリンク先。アンカーは定義が `d-<識別子>`、
定理が `t-<識別子>`（例 `[(D.olt)](Mechanized.md#d-olt)`）。

```
Def:
   PairSeq(a) entry(d) nextrel0(d) le0(d) nextrel1(d) nextR(d) Pred(d) idx1(d) hasParent(d) parent(d) oper(d) diagSeq(d) ST_PS(i) step(i)
Mechanized:
   Three(i) olt(d) ole(d) lead(d) olt_P_of_lead_lt(t) olt_irrefl(t) olt_Z_iff(t) olt_trans(t) olt_total(t) olt_ole_trans(t) olt_P_b(t) olt_P_c(t) translate(d) lead_translate(t) takeWhile_append_all(t) dropWhile_append_all(t) takeWhile_append_not(t) dropWhile_append_not(t) drop_eq_map_getD(t) nextrel0_entry0_less(t) le0_entry0_mono(t) nextrel0_index_less(t) nextrel0_rtrancl_index_le(t) le0_interval_gt(t) translate_single_tree(t) translate_block_append(t) translate_shift(t) translate_ctx_cong(t) sndSet(d) sndSet_mono(t) idx1_le1(t) oper_eq_self_of_short(t) oper_eq_pred_of_zero(t) oper_eq_pred_of_noParent(t) oper_bad_unfold(t) translate_snoc_increase(t) translate_dropLast_decrease(t) translate_takeWhile_snoc_le(t) core_i0(t) core_i1(t) translate_oper_pred(t) parent_nextR(t) nextR_index_lt(t) nextR_chain0(t) oper_bad_blocks(t) translate_oper_bad(t) m_step_decreases(t)
Psi:
   Om(d) Om_of_pos(t) Cstep(d) Citer(d) Cset(d) psi(d) Psi(d) addprinc(d)
Proofs:
   NF(d) Rnf(d) oper_eq_self_short(t) stepRel(d) step_terminates_cond(t) no_infinite_expansion_cond(t) step_terminates(t) no_infinite_expansion(t)
Wf:
   spine(d) cmax(d) climb(d) maxsub(d) cmax_ge(t) slex(d) slex_refl(t) getD_eq_getElem'(t) incpref(d) incpref_cons_cons(t) takeWhile_fst_nest(t) spine_translate_eq(t) cmax_append(t) maxsub_translate(t) maxsub_eq_climb_iff(t) oper_eq_dropLast_append(t) diagSeq_cons(t) fst_in_diagSeq(t) translate_diagSeq(t) cnf(d) cnf_translate_diagSeq_aux(t) cnf_diag(t) cnf_snoc(t) cnf_dropLast(t) cnf_take(t) cnf_replicate_block(t) cnf_ctx_cong(t) cnf_tail(t) cnf_oper_i1eq0(t) shiftr0(d) copies(d) shiftr0_cons(t) mem_shiftr0(t) copies_succ_front(t) copies_nonempty(t) copies_succ_cons(t) copies_v0_le(t) copies_tl_gt(t) cnf_copies(t) cnf_oper_i1eq1(t) copies_replicate(t) cnf_oper(t) cnf_ST_PS(t) tops(d) cnf_tops_le(t)
Wfsum:
   sargs(d) margs(d) ole_trans(t) summands(d) summands_shape(t) tsize(d)
Otembed:
   oV(d) psi_le_oV(t) allprinc_lt(d) oV_lt_of_allprinc(t) spinesub_le(d) spinesub_le_mono(t) Gterm(d) Gterm_P(t) mem_Gterm_P(t) hdle(d) wf3(d) wf3_spinesub_le(t) headle_all(d) hdle_head_ignores_tail(t) Gterm_tsize(t)
Gterm0Olt:
   translate_append_ge(t) translate_take_le(t)
Seqlex:
   pairlt(d) seqlex(d) seqlex_append_cancel(t) seqlex_prefix(t) steps1(d) blockok(d) steps1_iff(t) steps1_tail(t) steps1_append(t) steps1_dropLast(t) blockok_dropLast(t) blockok_arg(t) blockok_tail(t) seqlex_arg_or_tail(t) seqlex_imp_olt(t) seqlex_total(t) olt_iff_seqlex(t) getLastD_eq_getD(t) getLastD_ne_nil_indep(t) headI_append_left(t) getLastD_append_right(t) steps1_flatMap(t) steps1_diag_range(t) blockok_diagSeq(t) blockok_oper(t) blockok_ST_PS(t) olt_ST_iff_seqlex(t)
Nrm:
   oltDecidable(i) Glist(d) Glist_P(t) mem_Glist(t) maxo(d) maxo_cons(t) maxo_in(t) maxo_hdtl_in(t) proj(d) proj_id(t) proj_rec(t) proj_G(t) ins(d) ins_P(t) nrm(d) nrm_P(t) stps_len_pos(t) stps_head(t) getD_app_right(t) entry_append_right(t) nextrel0_append_right(t) rtg_nextrel0_lift(t) le0_append_right_of(t) nextrel0_lt(t) rtg_nextrel0_unlift(t) le0_append_right(t) nextrel0_no_cross(t) nextrel0_no_pred_zero(t) rtg_to_root(t) le0_no_cross(t) nextrel1_append_right(t) nextR_append_right(t) idx1_append_right(t) nextR_le0(t) nextR_src_in_T(t) hasParent_append_right(t) parent_append_right(t) take_append_right(t) copyblock_append(t) Pred_append_right(t) no_hasParent_of_row0_zero(t) oper_append_right(t) map_range_entry_eq_take(t) oper_headD(t)
Nrmstep:
   maxo_ub(t) maxo_ub_mem(t) Gterm_trans(t) mem_filter_Gterm(t) mem_filter_not_olt(t) proj_ole(t) pfire(d) pfire_iff(t) proj_nofire(t) olt_ole_trans(t) absorb_mono(t) ins_olt_mono(t) lext(i) lflip(i) einc(i) eflip(i) translate_cons(t) translate_single(t) nrm_leaf(t) snocok(d) snocok_cons(t) nrm_snoc_seg(t) maxr1(d) maxr1_cons(t) le_maxr1(t) r1ok(d) diagSeq0_length(t) diagSeq0_getD(t) r1ok_diagSeq(t) getD_take(t) r1ok_take(t) r1ok_dropLast(t) getD_append_left(t) getD_append_right(t) index_decomp(t) copies_map_length(t) copies_map_getD(t) copyExp(d) copyExp_length(t) copyExp_getD_pre(t) copyExp_getD_copy(t) hostM_getD_pre(t) hostM_getD_blk(t) hostM_length(t) r1ok_copyExp(t) getD_mem(t) dominated_PM_zero(t) r1ok_min_d0zero(t) r1ok_min_d0pos(t) hostM_getD_lp(t) r1ok_Pred(t) climb_bound(t) r1ok_oper(t) r1ok_ST_PS(t) hdarg(d) noabsorb(d) maxo_bad_nofire(t) proj_eq_maxo_bad(t) descok(d) descok_P(t) mvstep(d) mvstep_nofire(t) proj_mvstep(t) tsize_mvstep_lt(t) proj0_olt_of_mvstep_olt(t) Rdesc(i) SubBlock(i) repB(d) repB_succ(t) nextrel0_bound(t) le0_le(t) z0ok(d) z0ok_diagSeq(t) z0ok_take(t) z0ok_Pred(t) z0ok_copyExp(t) nextrel0_unique(t) nextrel1_unique(t) blockok_head_zero(t) parent0_exists(t) chain_to_zero(t) parent1_exists(t) nextR_one_iff(t) nextR_zero_iff(t) hp_last(t) z0ok_oper(t) z0ok_ST_PS(t) sclimb(d) rtg_through_pivot(t) le0_through_pivot(t) entry_shift(t) nextrel0_shift_iff(t) rtg_shift_of(t) rtg_shift_to(t) le0_shift_iff(t) idx1_shift(t) nextrel1_shift_iff(t) predGuard(d) predImages(i)
Cofinality:
   pairlt_trans(t) seqlex_trans(t) sle(d) sle_refl(t) seqlex_sle_trans(t) seqlex_append_mono(t) sle_append_mono(t) seqlex_snoc_cases(t) SeqlexCofinality(d) pss_cofinality_of_seqlex(t) entry_zero(t) entry_one(t) dropLast_snoc_getD(t) seqlex_cof_short(t) seqlex_cof_zero(t) hasParent_last_ST_PS(t) sle_append_cancel(t) getD_append_right'(t) getD_last_of_snoc(t) nextrel1_snd_succ(t) oper_bad_blocks_all(t) seqlex_splice(t) split_block(t) copy_dom_zero(t) copies_zero_succ(t) crux_zero(t) AscCrux(d) AscCrux1(d) shiftr0_length(t) mem_shiftr0_le(t) shiftr0_copies(t) AscArgDom(d) shiftr0_append(t) copies_succ_back(t) asc_crux1_of_argdom(t) asc_head_step(t) seqlex_cof_bad(t) seqlex_cofinality_of_crux(t) pss_cofinality(t) pss_cofinality_of_crux(t) pss_cofinality_of_argdom(t)
AscArg:
   seqlex_of_sle_not_prefix(t) peel_aux(t) sle_take_of_short(t) sle_trans(t) sle_of_append_left(t) seqlex_of_sle_snoc(t) shiftr0_injective(t) seqlex_shiftr0(t) sle_shiftr0(t) SpineOK(d) ArgDomCore(d) spineOK_of_nextrel1(t) ascArgDom_of_core(t) pss_cofinality_of_core(t) ArgDomCoreOn(d) argDomCore_of_on(t) argdom_pos(t) argDomCoreOn_diag(t) argDomCoreOn_snoc_zero(t) argDomCoreOn_drop_left(t) shiftl0(d) shiftl0_cons(t) shiftl0_append(t) mem_shiftl0(t) shiftr0_shiftl0(t) shiftr0_comm(t) argDomCoreOn_shiftr0(t) split_prefix_left(t) split_prefix_right(t) copies_headI(t) argbound_split(t) argbound_len(t) argDomCoreOn_bad_A1(t) arg_split(t) seqlex_of_sle_snoc'(t) argDomCoreOn_bad_B(t) shiftr0_add(t) sle_of_prefix(t) shiftr0_prefix(t) prefix_append_left(t) copies_length(t) split_append_left(t) prefix_cons_append(t) spineOK_of_nextrel1_strict(t) argDomCoreOn_bad_A2(t) argDomCoreOn_bad(t) argDomCoreOn_oper(t) argDomCoreOn_ST_PS(t) argDomCore_holds(t)
Wset:
   translate_eq_Z_iff(t) eq_Z_of_olt_one(t) stps_ne_nil(t) stps_len_one(t) domT(d) graft(d) based(d) not_domT_nil(t) natDom(d) natDom_iff(t) oper_eq_graft_nil_of_domT(t) r1cand(d) hasParent_one_iff(t) domT_iff(t) lfpS(d) lfpS_lowerbound(t) lfpS_unfold_le(t) lfpS_unfold_ge(t) lfpS_unfold(t) Aop(d) Aset(d) Aop_mono_X(t) Aset_mono(t) Aop_mono_level(t) Aop_cong(t) Wf(d) W(d) Wf_coh(t) Wf_eq_W(t) W_unfold(t) A1(t) A2(t) A2'(t) A1_intro(t) W_nil(t) W_mono(t) Rst(d) acc_of_translate_eq(t) acc_of_nat_branch(t) acc_of_W(t) argOK(d) rsum(d) nextR_shift_iff(t) hasParent_shift(t) parent_shift(t) oper_shift(t) domT_shift(t) natDom_shift(t) graft_shift(t) W_shift(t) split_lastMin(t) map_sub_add(t) rsum_decomp(t) entry_sub_zero(t) oper_append_gen(t) graft_append(t) hasParent_append_gen(t) domT_append(t) natDom_append(t) XA(d) entry_zero_headD(t) oper_head_eq(t) entry_pair_mem(t) oper_mem_ge(t) graft_mem_ge(t) graft_head_eq(t) XA_closed(t) W_add(t) graft_Om(t) domT_Om(t) Om_mem_W(t) Wstar(d) tow(d) graft_cons(t) entry_cons(t) nextR_cons(t) le0_cons(t) idx1_cons(t) hasParent_zero_iff(t) le0_cons_zero(t) len_succ(t) entry_cons_last(t) le0_cons_last(t) nextR_cons_last(t) idx1_cons_last(t) cons_len_lt(t) hasParent_cons_one(t) oper_root_tiling(t) oper_cons_nat(t) oper_cons_succ(t) oper_cons_tower(t) domT_cons_of_lt(t) argOK_oper(t) argOK_graft(t) argOK_dropLast(t) based_cons(t) rsum_self_cons(t) W_flatMap_copies(t) Wstar_closed(t) tree_shift(t) mem_of_Aclosed_aux(t) mem_of_Aclosed(t) mem_Wstar(t) mem_W_of_bound_aux(t) mem_W_of_bound(t) le_maxr1(t) mem_W_maxr1(t) W_membership(t) wf_of_cofinality_and_membership(t) wf_olt_ST_PS_of_cofinality(t)
OrdinalFree:
   acc_Rnf_of_acc_PS(t) wf_Rnf_of_wf_PS(t)
Final:
   pss_cofinality_holds(t) wf_olt_ST_PS_holds(t) wf_Rnf_holds(t) PSS_terminates_unconditional(t) no_infinite_expansion_holds(t)
```
