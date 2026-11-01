# `L20261018/Infra/Cohomology/ResidueLES` — sec. 2.4 · the continuous residue long exact sequence

33 modules.  Part of the development's [index](../../../README.md); see also [`DECLARATIONS.md`](../../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../../RENAME-MAP.tsv).

Paper items formalised here: `prop-residue-map-long-exact`; 1 raw line anchor.

| module | paper | declarations | lines |
|---|---|---|---|
| [`Step001_f2_delta_zero_vanishes`](Step001_f2_delta_zero_vanishes.lean) | `prop-residue-map-long-exact` | `dimShiftSES`, `dimShiftSES_X₁`, `dimShiftSES_X₃`, `deltaZero_coindBot_comp_coind` (+2 more) | 128 |
| [`Step002_t_cokernel_constructed`](Step002_t_cokernel_constructed.lean) |  | `qSES`, `qSES_X₁`, `qSES_X₂`, `qSES_X₃` (+6 more) | 113 |
| [`Step003_f1_square`](Step003_f1_square.lean) | `prop-residue-map-long-exact` | `f1Sq`, `delta_dimShiftUpSES_eq`, `f1Sq_τ₁_eq`, `f1Sq_τ₃_eq` (+1 more) | 138 |
| [`Step004_i_star_delta_zero_bar`](Step004_i_star_delta_zero_bar.lean) |  | `cokerSES_X₂`, `qSES_g_comp_deltaZeroBar`, `iTame_comp_deltaZeroBar`, `mono_δ_cokerSES` | 96 |
| [`Step005_delta_two_comp_inf_zero`](Step005_delta_two_comp_inf_zero.lean) |  | `deltaTwo_firstHalf'_hom_eq`, `inflationIso_hom_eq`, `epi_δ_cokerSES`, `delta_coind_comp_infl'` (+2 more) | 126 |
| [`Step006_mu_p_smooth_discrete`](Step006_mu_p_smooth_discrete.lean) |  | `carrier_V`, `carrier_H2`, `carrier_cup`, `isSmoothDiscrete_muP` | 99 |
| [`Step007_continuous_615`](Step007_continuous_615.lean) |  | `muP_eq_ofDiscreteModule`, `compactSpace_absoluteGaloisGroup`, `contCoindBotDimensionShiftTwo`, `contCoindBotDimensionShiftTwo_type_lock` | 103 |
| [`Step008_base_ring_alignment`](Step008_base_ring_alignment.lean) |  | `restrictScalarsInt_muP`, `contH1BaseBridge`, `contH2BaseBridge` | 87 |
| [`Step009_continuous_dim_shift_ses`](Step009_continuous_dim_shift_ses.lean) |  | `contCoindSES`, `contDimShiftSES`, `contDeltaZeroBar` | 53 |
| [`Step010_continuous_f2`](Step010_continuous_f2.lean) |  | `contDeltaZeroBar_kills_proj` | 45 |
| [`Step011_continuous_res_delta_square`](Step011_continuous_res_delta_square.lean) |  | `contDelta_res_naturality`, `contDeltaZeroBar_eq_delta` | 52 |
| [`Step012_continuous_t_carrier`](Step012_continuous_t_carrier.lean) | `line:9528` | `contB`, `contC`, `contInvA`, `contInvB` (+12 more) | 174 |
| [`Step013_continuous_f1`](Step013_continuous_f1.lean) | `prop-residue-map-long-exact` | `contProjInv`, `contProjInv_coe`, `contProjInv_smul`, `contKI_le_ker_contProjInv` (+8 more) | 208 |
| [`Step014_continuous_d_two_blocks`](Step014_continuous_d_two_blocks.lean) |  | `isIso_contCoindSES_delta`, `epi_contCoindSES_delta`, `contPairITame`, `contPairSubtypeC` (+4 more) | 162 |
| [`Step015_vkg_kummer_decomposition`](Step015_vkg_kummer_decomposition.lean) |  | `exists_unit_kummerClass_of_mem_ker`, `forall_VKG_cup_eq_zero_of_units`, `residueSpan_le_ker_of_units`, `VKG_cup_eq_zero_of_residueSpan_le` | 104 |
| [`Step016_delta_t_iso`](Step016_delta_t_iso.lean) |  | `isIso_contInvSES_delta`, `epi_contInvSES_delta`, `contInvSES_X₂` | 77 |
| [`Step017_delta_t_iso_upper`](Step017_delta_t_iso_upper.lean) |  | `subsingleton_of_topRep_iso`, `isClosed_bot_quot`, `subsingleton_continuousCoindBot` | 100 |
| [`Step018_cont_inv_b_pointwise`](Step018_cont_inv_b_pointwise.lean) |  | `coe_smul`, `mem_contInvB_iff`, `contInvB_apply_eq_of_mk_eq`, `contInvB_lift_wd` | 77 |
| [`Step019_cont_inv_b_descend`](Step019_cont_inv_b_descend.lean) |  | `contInvBDescendFun`, `contInvBDescendFun_comp_mk`, `contInvBDescendFun_add`, `contInvBDescendFun_injective` (+3 more) | 92 |
| [`Step020_pull_back_map`](Step020_pull_back_map.lean) |  | `quotientMk_mul_mem_eq`, `coindBotPull`, `coindBotPull_apply`, `coindBotPull_mem` (+1 more) | 101 |
| [`Step021_descend_pull_inverse`](Step021_descend_pull_inverse.lean) |  | `contInvBDescend_comp_coindBotToContInvB`, `coindBotToContInvB_injective` | 72 |
| [`Step022_bi_iso_assembly`](Step022_bi_iso_assembly.lean) |  | `contInvBDescendCoind`, `contInvBEquivCoind` | 120 |
| [`Step023_is_locally_constant_descend`](Step023_is_locally_constant_descend.lean) |  | `contInvBDescendFun_locallyConstant`, `contInvBEquivCoindBot` | 70 |
| [`Step024_top_rep_iso_coind`](Step024_top_rep_iso_coind.lean) |  | `contInvBEquivCoindBot_smul`, `contInvBEquivCoindBot_symm_smul`, `contInvBTopRepIso`, `subsingleton_contInvB` (+1 more) | 126 |
| [`Step025_delta_t_iso_usable`](Step025_delta_t_iso_usable.lean) |  | `epi_contInvSES_delta_uncond`, `contInvSES_delta_one_isIso`, `epi_contInvSES_delta_one`, `isIso_contInvSES_delta_inertia` (+1 more) | 73 |
| [`Step026_invariants_equiv_self`](Step026_invariants_equiv_self.lean) |  | `contInvAEquiv`, `contInvAEquiv_smul` | 83 |
| [`Step027_invariants_equiv_self_top_rep`](Step027_invariants_equiv_self_top_rep.lean) |  | `contInvA_smul_eq_self`, `contInvATopRepIso` | 71 |
| [`Step028_t_equiv_coind_quotient`](Step028_t_equiv_coind_quotient.lean) |  | `contT_equiv_coindQuotient` | 63 |
| [`Step029_hk_content_layer`](Step029_hk_content_layer.lean) |  | `contInvIncl_equiv_unit` | 74 |
| [`Step030_right_square_closed`](Step030_right_square_closed.lean) |  | `contKI_map_eq`, `contT_equiv_coindQuotient'` | 71 |
| [`Step031_inf_c_inverse_hypothesis`](Step031_inf_c_inverse_hypothesis.lean) |  | `subsingleton_H1_contC` | 63 |
| [`Step032_inf_c_inverse_narrowed`](Step032_inf_c_inverse_narrowed.lean) |  | `RestrictedCoindAcyclic`, `subsingleton_H1_contC_inertia` | 82 |
| [`Step033_restricted_coind_acyclic_nonempty`](Step033_restricted_coind_acyclic_nonempty.lean) |  | `restrictedCoindAcyclic_bot` | 54 |
