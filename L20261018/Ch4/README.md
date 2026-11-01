# `L20261018/Ch4` — sec. 4 · Hensel valuations and ramification in the first slot

48 modules.  Part of the development's [index](../README.md); see also [`DECLARATIONS.md`](../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../RENAME-MAP.tsv).

Source items formalised here: `lem:basis-change`, `lem:ramified-vanishing`, `prop:prelim-residue`, `thm:ramified`; 9 line anchors.

| module | source item | declarations | lines |
|---|---|---|---|
| [`Step001_basis_change_first_slot`](Step001_basis_change_first_slot.lean) | `lem:basis-change` | `cup_sum_sum`, `cup_basis_change`, `basis_change_kummer` | 142 |
| [`Step002_residue_cup_data_shape`](Step002_residue_cup_data_shape.lean) | `lem:ramified-vanishing` | `ResidueCupData`, `plane`, `commonCupMap`, `orth` (+9 more) | 299 |
| [`Step003_ramified_vanishing_paper_objects`](Step003_ramified_vanishing_paper_objects.lean) | `lem:ramified-vanishing`, `prop:prelim-residue` | `HenselResidueData`, `toResidueCupData`, `ramified_vanishing`, `ramified_vanishing_kummer` (+2 more) | 193 |
| [`Step004_thm_ramified_assembly`](Step004_thm_ramified_assembly.lean) | `thm:ramified` | `thm_ramified_1`, `thm_ramified_2` | 104 |
| [`Step005_corollary_four_four_dimension`](Step005_corollary_four_four_dimension.lean) | `line:1646` | `val_surjective`, `ker_val_eq_range_infl`, `finrank_eq_finrank_add_one`, `finrank_range_commonCupMap` (+2 more) | 122 |
| [`Step006_thm_ramified_no_d`](Step006_thm_ramified_no_d.lean) | `thm:ramified` | `theta1`, `theta2`, `theta1_apply`, `theta2_apply` (+7 more) | 220 |
| [`Step007_corollary_four_four_no_d`](Step007_corollary_four_four_no_d.lean) | `line:1646` | `residueCupData_explicit`, `residueCupData_explicit_val`, `residueCupData_explicit_cup`, `finrank_eq_finrank_add_one_uncond` (+2 more) | 135 |
| [`Step008_rank_contradiction_single_phi`](Step008_rank_contradiction_single_phi.lean) | `line:1646` | `Bex_Phi_theta`, `phi_comp`, `phi_range_map`, `finrank_range_eq` (+2 more) | 166 |
| [`Step009_dk_eq_one_is_a_theorem`](Step009_dk_eq_one_is_a_theorem.lean) | `line:1646` | `exists_ne_zero_mem_ker`, `finrank_ker_valLin_le_one`, `finrank_ker_valLin_eq_one`, `corollary_4_4_uncond'` (+3 more) | 187 |
| [`Step010_basis_change_brauer_class`](Step010_basis_change_brauer_class.lean) | `lem:basis-change` | `basis_change_brauer` | 50 |
| [`Step011_transition_paragraph_4_1_4_2`](Step011_transition_paragraph_4_1_4_2.lean) | `line:1596`, `line:1599` | `pair_linearIndependent`, `finrank_plane_eq_two`, `finrank_ker_restrict_plane_eq_one`, `residue_not_pow_of_kummerClass_ne_zero` (+3 more) | 201 |
| [`Step012_ramified_vanishing_paper_route`](Step012_ramified_vanishing_paper_route.lean) | `line:1608` | `cup_eq_zero_of_mem_orth`, `HenselResidueData.ker_val_eq_range_infl`, `finrank_ker_restrict_plane_eq_one_general`, `orth_eq_bot_paper_route` (+1 more) | 222 |
| [`Step013_basis_selection_u`](Step013_basis_selection_u.lean) | `line:1596` | `range_pair_eq`, `exists_basis_val_eq` | 114 |
| [`Step014_ramified_vanishing_hensel_level`](Step014_ramified_vanishing_hensel_level.lean) | `line:1608` | `cup_self_free`, `range_pair_eq_free`, `pair_linearIndependent_free`, `finrank_plane_eq_two_free` (+4 more) | 263 |
| [`Step015_thm_ramified_1_sec_2_4_only`](Step015_thm_ramified_1_sec_2_4_only.lean) | `line:1636` | `mem_orth_iff`, `orth_map_eq`, `thm_ramified_1_of_D` | 151 |
| [`Step016_corollary_four_four_sec_2_4_only`](Step016_corollary_four_four_sec_2_4_only.lean) | `line:1648` | `henselResidueData_explicit_of_D`, `henselResidueData_explicit_of_D_val`, `residueCupData_explicit_of_D`, `finrank_eq_finrank_add_one_of_D` (+1 more) | 100 |
| [`Step017_thm_ramified_and_corollary_class_free`](Step017_thm_ramified_and_corollary_class_free.lean) | `line:1636`, `line:1648` | `zmodMulPairing_eq_muPairing_free`, `cup_compat_muP_zmod_free`, `theta1_free`, `theta2_free` (+9 more) | 232 |
| [`Step018_single_carrier_thm_ramified`](Step018_single_carrier_thm_ramified.lean) | `line:1636`, `line:1637` | `cup_kummerClass_ne_zero_free`, `Bex_Phi_theta_free`, `phi_comp_free`, `phi_range_map_free` (+3 more) | 170 |
| [`Step019_single_carrier_statement`](Step019_single_carrier_statement.lean) |  | `ch4_single_carrier_combined` | 91 |
| [`Step020_delta_two_eq_res_carrier`](Step020_delta_two_eq_res_carrier.lean) |  | `res_tame_values`, `paperUseSpan`, `res_eq_on_paperUseSpan`, `mem_paperUseSpan_pi` (+1 more) | 83 |
| [`Step021_d_elementary_block`](Step021_d_elementary_block.lean) |  | `toAdd_pow_int`, `valMonoidGen`, `valMonoidGen_ker`, `valQuotGen` (+4 more) | 145 |
| [`Step022_d_residue_field`](Step022_d_residue_field.lean) |  | `ofAdd_one_zpow_gen`, `val_mul_uniformizer_zpow`, `kummerClass_split_gen`, `valH1LinearGen` (+1 more) | 117 |
| [`Step023_tame_residue_facts_reduction`](Step023_tame_residue_facts_reduction.lean) |  | `tame_pi_u_redundant` | 76 |
| [`Step024_tame_residue_facts_class_free`](Step024_tame_residue_facts_class_free.lean) |  | `generalHensel_reduction` | 62 |
| [`Step025_d_class_eq_cup_sum`](Step025_d_class_eq_cup_sum.lean) |  | `D_class_eq_cup_sum` | 78 |
| [`Step026_residue_span_bot_reduction`](Step026_residue_span_bot_reduction.lean) |  | `h2_eq_zero_of_cd_le_one`, `tameResidueFacts_of_span_eq_bot` | 76 |
| [`Step027_residue_span_bot_skeleton`](Step027_residue_span_bot_skeleton.lean) |  | `residueSpan_eq_bot_of_le_range`, `tameResidueFacts_of_le_range`, `exists_henselResidueData_of_le_range` | 113 |
| [`Step028_r1_linear_transport`](Step028_r1_linear_transport.lean) |  | `injective_of_comp_eq`, `residuePhi_injective_transport` | 91 |
| [`Step029_r1_two_carriers_wired`](Step029_r1_two_carriers_wired.lean) |  | `injective_of_comp_eq_fun`, `valH1LinearGen_redEquiv1`, `residuePhi_injective_muNRep`, `tameResidueFacts_Galo_of_span_eq_bot` (+1 more) | 217 |
| [`Step030_unramified_decomposition_algebraic`](Step030_unramified_decomposition_algebraic.lean) |  | `exists_unit_of_valH1Gen_eq_zero`, `residueSpan_eq_bot_of_units`, `cup_kummerClass_unit_eq_zero_of_norm`, `residueSpan_eq_bot_of_norm` (+5 more) | 308 |
| [`Step031_ch4_closed_units_cup_vanish`](Step031_ch4_closed_units_cup_vanish.lean) | `line:1608`, `line:1636`, `line:1648` | `orth_eq_bot_of_discrete_valuation'`, `thm_ramified_1_of_discrete_valuation'`, `corollary_4_4_of_discrete_valuation'` | 150 |
| [`Step032_v_and_d_exists`](Step032_v_and_d_exists.lean) |  | `moduleFinite_adjoinRoot`, `exists_henselResidueData_uncond` | 87 |
| [`Step033_ch4_three_and_exists_d`](Step033_ch4_three_and_exists_d.lean) | `line:1050`, `line:1608`, `line:1636`, `line:1648` | `tameResidueFacts_Galo_noBridge_of_hζ`, `tameResidueFacts_Galo_noBridge`, `exists_henselResidueData_noBridge`, `orth_eq_bot_noBridge` (+2 more) | 182 |
| [`Step034_exists_d_unconditional`](Step034_exists_d_unconditional.lean) | `prop:prelim-residue` | `exists_henselResidueData_uncond_noBridge` | 73 |
| [`Step035_exists_d_no_finite_residue`](Step035_exists_d_no_finite_residue.lean) |  | `exists_henselResidueData_of_residueMap` | 52 |
| [`Step036_ch4_three_without_finite_residue`](Step036_ch4_three_without_finite_residue.lean) |  | `orth_eq_bot_general`, `thm_ramified_1_general`, `corollary_4_4_general` | 139 |
| [`Step037_ch4_without_finite_dimensional_v`](Step037_ch4_without_finite_dimensional_v.lean) | `line:1636` | `finrank_ker_restrict_plane_eq_one_nofin`, `orth_eq_bot_paper_route_hensel_nofin`, `thm_ramified_1_of_D_free_nofin`, `orth_eq_bot_of_discrete_valuation_nofin` (+3 more) | 343 |
| [`Step038_ch4_proof_structure_index`](Step038_ch4_proof_structure_index.lean) |  | `residueSpan_eq_bot_of_subsingleton_H2_residue`, `tameResidueFacts_Galo_of_residueSpan_eq_bot`, `ch4TameSymbolHyp_of_residueSpan_eq_bot`, `ch4TameSymbolHyp_of_subsingleton_H2_residue'` | 177 |
| [`Step039_ch4_four_without_finite_residue`](Step039_ch4_four_without_finite_residue.lean) | `line:1050`, `line:1608`, `line:1636`, `line:1648` | `tameResidueFacts_of_merkurjevSuslin`, `orth_eq_bot_of_merkurjevSuslin`, `thm_ramified_1_of_merkurjevSuslin`, `corollary_4_4_of_merkurjevSuslin` (+1 more) | 192 |
| [`Step040_corollary_four_four_paper_level`](Step040_corollary_four_four_paper_level.lean) | `line:1646` | `corollary_4_4_paper` | 93 |
| [`Step041_thm_ramified_two_rank_barrier`](Step041_thm_ramified_two_rank_barrier.lean) | `line:1635` | `thm_ramified_2_paper` | 64 |
| [`Step042_hd_infl_final_form`](Step042_hd_infl_final_form.lean) |  | `not_ringChar_dvd_of_coprime`, `deltaTwoGaloBase'_cup_eq_zero'`, `hd_infl_of_linear` | 102 |
| [`Step043_ch4_closure_certificate`](Step043_ch4_closure_certificate.lean) |  | — | 87 |
| [`Step044_ch4_hypothesis_deflation_audit`](Step044_ch4_hypothesis_deflation_audit.lean) |  | `isUnit_natCast_of_charZero`, `ramified_vanishing_paper` | 116 |
| [`Step045_hd_infl_discharged`](Step045_hd_infl_discharged.lean) |  | `hd_infl_F5_uncond` | 87 |
| [`Step046_exists_residue_map`](Step046_exists_residue_map.lean) |  | `coeffInclH1`, `subtypeCompCoeffInclH1`, `coeffInclH1_injective`, `coeffInclH1_ne_zero` (+10 more) | 453 |
| [`Step047_ch4_three_d_free`](Step047_ch4_three_d_free.lean) | `line:1608`, `line:1636`, `line:1648` | `orth_eq_bot_viaResidue`, `thm_ramified_1_viaResidue`, `corollary_4_4_viaResidue` | 230 |
| [`Step048_r2_infinite_residue_certificate`](Step048_r2_infinite_residue_certificate.lean) |  | `isUnit_natCast_residueField`, `hilbert90_residueField`, `kummerIso_residueField`, `kummerMap_residueField_surjective` (+1 more) | 107 |
