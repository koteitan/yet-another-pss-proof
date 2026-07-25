[← README](../../README-ja.md)

# `md/YAPSS/` — 証明本文の目次

`lean/YAPSS/*.lean` の各モジュールに 1 対 1 で対応する。編集方針は
[`../requirement.md`](../requirement.md)。

**基盤 → 結論の順**に並べる。各ファイルは自分より上の行のファイルの定義・命題のみを引用する。

| # | ファイル | Lean 行数 | 宣言数 | 依存 |
|---:|---|---:|---:|---|
| 1 | [`Def.md`](Def.md) | 131 | 14 | — |
| 2 | [`Mechanized.md`](Mechanized.md) | 997 | 56 | Def |
| 3 | [`Proofs.md`](Proofs.md) | 114 | 8 | Mechanized |
| 4 | [`Wf.md`](Wf.md) | 1193 | 67 | Proofs |
| 5 | [`Wfsum.md`](Wfsum.md) | 97 | 10 | Wf |
| 6 | [`Gterm.md`](Gterm.md) | 53 | 5 | Wfsum |
| 7 | [`Seqlex.md`](Seqlex.md) | 714 | 34 | Wf |
| 8 | [`Nrm.md`](Nrm.md) | 539 | 48 | Gterm |
| 9 | [`Nrmstep.md`](Nrmstep.md) | 2135 | 107 | Nrm,Seqlex |
| 10 | [`Cofinality.md`](Cofinality.md) | 1092 | 40 | Mechanized,Seqlex,Nrmstep |
| 11 | [`AscArg.md`](AscArg.md) | 1929 | 50 | Cofinality |
| 12 | [`Wset.md`](Wset.md) | 2056 | 113 | Nrmstep |
| 13 | [`OrdinalFree.md`](OrdinalFree.md) | 87 | 2 | Cofinality,Wset,Proofs |
| 14 | [`Final.md`](Final.md) | 65 | 5 | AscArg,OrdinalFree |

## 記号の所在

他ファイルで定義された記号を引用するときのリンク先。アンカーは定義が `d-<識別子>`、
定理が `t-<識別子>`（例 `[(D.olt)](Mechanized.md#d-olt)`）。

```
Def:
   PairSeq entry nextrel0 le0 nextrel1 nextR Pred idx1 hasParent parent oper diagSeq ST_PS step
Mechanized:
   Three olt ole olt_Z_Z olt_Z_P olt_P_Z olt_P_P lead lead_Z lead_P olt_P_of_lead_lt olt_irrefl not_olt_Z olt_Z_iff olt_trans olt_total olt_ole_trans olt_P_b olt_P_c translate lead_translate takeWhile_append_all dropWhile_append_all takeWhile_append_not dropWhile_append_not drop_eq_map_getD nextrel0_entry0_less le0_entry0_mono nextrel0_index_less nextrel0_rtrancl_index_le le0_interval_gt translate_single_tree translate_block_append translate_shift translate_ctx_cong sndSet mem_sndSet sndSet_nil sndSet_mono idx1_le1 oper_eq_self_of_short oper_eq_pred_of_zero oper_eq_pred_of_noParent oper_bad_unfold translate_snoc_increase translate_dropLast_decrease translate_takeWhile_snoc_le core_i0 core_i1 translate_oper_pred parent_nextR nextR_index_lt nextR_chain0 oper_bad_blocks translate_oper_bad m_step_decreases
Proofs:
   NF Rnf oper_eq_self_short stepRel step_terminates_cond no_infinite_expansion_cond step_terminates no_infinite_expansion
Wf:
   spine spine_Z spine_P cmax climb maxsub maxsub_Z maxsub_P cmax_nil cmax_cons cmax_ge slex slex_nil slex_cons_nil slex_cons_cons slex_refl getD_eq_getElem' incpref incpref_nil incpref_single incpref_cons_cons takeWhile_fst_nest spine_translate_eq cmax_append maxsub_translate maxsub_eq_climb_iff oper_eq_dropLast_append diagSeq_cons fst_in_diagSeq translate_diagSeq cnf cnf_Z cnf_P_Z cnf_P_P cnf_translate_diagSeq_aux cnf_diag cnf_snoc cnf_dropLast cnf_take cnf_replicate_block cnf_ctx_cong cnf_tail cnf_oper_i1eq0 shiftr0 copies shiftr0_zero shiftr0_nil shiftr0_eq_nil translate_shiftr0 shiftr0_cons mem_shiftr0 copies_zero copies_succ_front copies_one copies_nonempty copies_succ_cons copies_v0_le copies_tl_gt cnf_copies cnf_oper_i1eq1 copies_replicate cnf_oper cnf_ST_PS tops tops_Z tops_P cnf_tops_le
Wfsum:
   sargs sargs_Z sargs_P margs ole_trans summands summands_Z summands_P summands_shape tsize
Gterm:
   Gterm Gterm_Z Gterm_P mem_Gterm_P Gterm_tsize
Seqlex:
   pairlt seqlex seqlex_nil_iff not_seqlex_nil seqlex_cons_cons seqlex_append_cancel seqlex_prefix steps1 steps1_nil steps1_single steps1_cons_cons blockok blockok_nil steps1_iff steps1_tail steps1_append steps1_dropLast blockok_dropLast blockok_arg blockok_tail seqlex_arg_or_tail seqlex_imp_olt seqlex_total olt_iff_seqlex getLastD_eq_getD getLastD_ne_nil_indep headI_append_left getLastD_append_right steps1_flatMap steps1_diag_range blockok_diagSeq blockok_oper blockok_ST_PS olt_ST_iff_seqlex
Nrm:
   oltDecidable Glist Glist_Z Glist_P mem_Glist maxo maxo_nil maxo_cons maxo_in maxo_hdtl_in proj proj_id proj_rec proj_G ins ins_Z ins_P nrm nrm_Z nrm_P stps_len_pos stps_head getD_app_right entry_append_right nextrel0_append_right rtg_nextrel0_lift le0_append_right_of nextrel0_lt rtg_nextrel0_unlift le0_append_right nextrel0_no_cross nextrel0_no_pred_zero rtg_to_root le0_no_cross nextrel1_append_right nextR_append_right idx1_append_right nextR_le0 nextR_src_in_T hasParent_append_right parent_append_right take_append_right copyblock_append Pred_append_right no_hasParent_of_row0_zero oper_append_right map_range_entry_eq_take oper_headD
Nrmstep:
   maxo_ub maxo_ub_mem Gterm_trans mem_filter_Gterm mem_filter_not_olt proj_ole pfire pfire_iff proj_nofire olt_ole_trans absorb_mono ins_olt_mono lext lflip einc eflip translate_nil translate_cons translate_single proj_Z nrm_leaf snocok snocok_nil snocok_cons nrm_snoc_seg maxr1 maxr1_nil maxr1_cons le_maxr1 r1ok diagSeq0_length diagSeq0_getD r1ok_diagSeq getD_take r1ok_take r1ok_dropLast getD_append_left getD_append_right index_decomp copies_map_length copies_map_getD copyExp copyExp_length copyExp_getD_pre copyExp_getD_copy hostM_getD_pre hostM_getD_blk hostM_length r1ok_copyExp getD_mem dominated_PM_zero r1ok_min_d0zero r1ok_min_d0pos hostM_getD_lp r1ok_Pred climb_bound r1ok_oper r1ok_ST_PS hdarg hdarg_Z hdarg_P noabsorb maxo_bad_nofire proj_eq_maxo_bad descok descok_Z descok_P mvstep mvstep_nofire proj_mvstep tsize_mvstep_lt proj0_olt_of_mvstep_olt Rdesc SubBlock repB repB_zero repB_succ nextrel0_bound le0_le z0ok z0ok_diagSeq z0ok_take z0ok_Pred z0ok_copyExp nextrel0_unique nextrel1_unique blockok_head_zero parent0_exists chain_to_zero parent1_exists nextR_one_iff nextR_zero_iff hp_last z0ok_oper z0ok_ST_PS sclimb rtg_through_pivot le0_through_pivot entry_shift nextrel0_shift_iff rtg_shift_of rtg_shift_to le0_shift_iff idx1_shift nextrel1_shift_iff predGuard predImages
Cofinality:
   pairlt_trans seqlex_trans sle sle_refl seqlex_sle_trans seqlex_append_mono sle_append_mono seqlex_snoc_cases SeqlexCofinality pss_cofinality_of_seqlex entry_zero entry_one dropLast_snoc_getD seqlex_cof_short seqlex_cof_zero hasParent_last_ST_PS sle_append_cancel getD_append_right' getD_last_of_snoc nextrel1_snd_succ oper_bad_blocks_all seqlex_splice split_block copy_dom_zero copies_zero_succ crux_zero AscCrux AscCrux1 shiftr0_length mem_shiftr0_le shiftr0_copies AscArgDom shiftr0_append copies_succ_back asc_crux1_of_argdom asc_head_step seqlex_cof_bad seqlex_cofinality_of_crux pss_cofinality pss_cofinality_of_crux pss_cofinality_of_argdom
AscArg:
   seqlex_of_sle_not_prefix peel_aux sle_take_of_short sle_trans sle_of_append_left seqlex_of_sle_snoc shiftr0_injective seqlex_shiftr0 sle_shiftr0 SpineOK ArgDomCore spineOK_of_nextrel1 ascArgDom_of_core pss_cofinality_of_core ArgDomCoreOn argDomCore_of_on argdom_pos argDomCoreOn_diag argDomCoreOn_snoc_zero argDomCoreOn_drop_left shiftl0 shiftl0_cons shiftl0_append mem_shiftl0 shiftl0_shiftr0 shiftr0_shiftl0 shiftr0_comm argDomCoreOn_shiftr0 split_prefix_left split_prefix_right copies_headI argbound_split argbound_len argDomCoreOn_bad_A1 arg_split seqlex_of_sle_snoc' argDomCoreOn_bad_B shiftr0_add sle_of_prefix shiftr0_prefix prefix_append_left copies_length split_append_left prefix_cons_append spineOK_of_nextrel1_strict argDomCoreOn_bad_A2 argDomCoreOn_bad argDomCoreOn_oper argDomCoreOn_ST_PS argDomCore_holds
Wset:
   translate_eq_Z_iff eq_Z_of_olt_one stps_ne_nil stps_len_one domT graft based based_nil graft_nil not_domT_nil natDom natDom_nil natDom_iff oper_eq_graft_nil_of_domT r1cand hasParent_one_iff domT_iff lfpS lfpS_lowerbound lfpS_unfold_le lfpS_unfold_ge lfpS_unfold Aop Aset Aop_mono_X Aset_mono Aop_mono_level Aop_cong Wf W Wf_coh Wf_eq_W W_unfold A1 A2 A2' A1_intro W_nil W_mono Rst acc_of_translate_eq acc_of_nat_branch acc_of_W argOK rsum nextR_shift_iff hasParent_shift parent_shift oper_shift domT_shift natDom_shift graft_shift W_shift split_lastMin map_sub_add rsum_decomp entry_sub_zero oper_append_gen graft_append hasParent_append_gen domT_append natDom_append XA entry_zero_headD oper_head_eq entry_pair_mem oper_mem_ge graft_mem_ge graft_head_eq XA_closed W_add graft_Om domT_Om Om_mem_W Wstar tow graft_cons entry_cons nextR_cons le0_cons idx1_cons hasParent_zero_iff le0_cons_zero len_succ entry_cons_last le0_cons_last nextR_cons_last idx1_cons_last cons_len_lt hasParent_cons_one oper_root_tiling oper_cons_nat oper_cons_succ oper_cons_tower domT_cons_of_lt argOK_oper argOK_graft argOK_dropLast based_cons rsum_self_cons W_flatMap_copies Wstar_closed tree_shift mem_of_Aclosed_aux mem_of_Aclosed mem_Wstar mem_W_of_bound_aux mem_W_of_bound le_maxr1 mem_W_maxr1 W_membership wf_of_cofinality_and_membership wf_olt_ST_PS_of_cofinality
OrdinalFree:
   acc_Rnf_of_acc_PS wf_Rnf_of_wf_PS
Final:
   pss_cofinality_holds wf_olt_ST_PS_holds wf_Rnf_holds PSS_terminates_unconditional no_infinite_expansion_holds
```
