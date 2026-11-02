# `L20261018/Ch2/Hensel/ResidueMap` — sec. 2.4 · the residue map, its exact sequence, (R1) and (R2)

84 modules.  Part of the development's [index](../../../README.md); see also [`DECLARATIONS.md`](../../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../../RENAME-MAP.tsv).

Source items formalised here: `GS2017/lemma-residue-cup-product`, `GS2017/prop-units-cohomology`, `lem:ramified-vanishing`, `prop:prelim-kummer-valuation`, `prop:prelim-residue`; 10 line anchors.

| module | source item | declarations | lines |
|---|---|---|---|
| [`Step001_open_residual_advance`](Step001_open_residual_advance.lean) | `line:1017` | `principalUnit_pow_surjective`, `principalUnit_pow_surjective_prime`, `toyHenselResidueData`, `toyHenselResidueData_nonempty` (+1 more) | 125 |
| [`Step002_unit_reduction_principal_units`](Step002_unit_reduction_principal_units.lean) | `lem:ramified-vanishing`, `line:1017`, `prop:prelim-kummer-valuation` | `principalUnits_le_pow_range`, `principalUnit_exists_pow_eq`, `unitPow_iff_residuePow`, `unit_pow_of_residue_pow` | 87 |
| [`Step003_residue_valuation_h1`](Step003_residue_valuation_h1.lean) | `prop:prelim-kummer-valuation` | `valOfUnit`, `toAdd_mul'`, `toAdd_pow'`, `valOfUnit_mul` (+6 more) | 144 |
| [`Step004_valuation_decomposition_unique`](Step004_valuation_decomposition_unique.lean) | `prop:prelim-kummer-valuation` | `exists_decomp_linear`, `val_eq_of_decomp_linear`, `unique_decomp_linear`, `exists_decomp` (+2 more) | 120 |
| [`Step005_residue_cup_data_fields_reduced`](Step005_residue_cup_data_fields_reduced.lean) | `lem:ramified-vanishing` | `decomp_mem_ker`, `residueCupDataOfKer`, `vanishing_of_ker`, `ramified_vanishing_reduced` | 138 |
| [`Step006_tame_pi_u_of`](Step006_tame_pi_u_of.lean) | `lem:ramified-vanishing` | `tame_pi_u_of`, `vanishing_of_ker3`, `ramified_vanishing_reduced3` | 89 |
| [`Step007_valuation_to_add_tools`](Step007_valuation_to_add_tools.lean) |  | `toAdd_inv'`, `toAdd_val_pi_pow`, `toAdd_val_mul_pow_inv` | 36 |
| [`Step008_exists_unit_rep`](Step008_exists_unit_rep.lean) | `prop:prelim-kummer-valuation` | `toAdd_one'`, `toAdd_eq_one_iff`, `toAdd_val_mul_pow`, `exists_unit_rep` | 71 |
| [`Step009_tame_uu_of_units`](Step009_tame_uu_of_units.lean) |  | `tame_uu_of_units`, `ramified_vanishing_units` | 62 |
| [`Step010_cup_unit_unit_eq_zero`](Step010_cup_unit_unit_eq_zero.lean) |  | `cup_unit_unit_eq_zero` | 25 |
| [`Step011_cup_fp_unit_unit_eq_zero`](Step011_cup_fp_unit_unit_eq_zero.lean) |  | `cupFp_unit_unit_eq_zero` | 24 |
| [`Step012_bridge_kc_unit_cup_zero`](Step012_bridge_kc_unit_cup_zero.lean) | `prop:prelim-residue` | `cup_bridgeKc_unit_unit_eq_zero`, `hUU_of_scale` | 123 |
| [`Step013_huu_reduced_to_linear_dependence`](Step013_huu_reduced_to_linear_dependence.lean) | `prop:prelim-residue` | `cup_self`, `cup_eq_zero_of_left_mem_span`, `cup_eq_zero_of_right_mem_span`, `hUU_of_ker_le_one` | 84 |
| [`Step014_ker_v_one_dim_group_core`](Step014_ker_v_one_dim_group_core.lean) |  | `exists_pow_eq_of_pow_eq_one` | 84 |
| [`Step015_huu_residue_field_power_relation`](Step015_huu_residue_field_power_relation.lean) |  | `residue_exists_mul_pow_inv_mem_range` | 55 |
| [`Step016_huu_unit_power_dependence`](Step016_huu_unit_power_dependence.lean) |  | `unit_pow_dependence` | 68 |
| [`Step017_hdep_huu_are_theorems`](Step017_hdep_huu_are_theorems.lean) | `prop:prelim-residue` | `ker_dependent`, `hUU` | 90 |
| [`Step018_huu_discharged`](Step018_huu_discharged.lean) | `lem:ramified-vanishing` | `ker_cup_eq_zero`, `ramified_vanishing_units'` | 78 |
| [`Step019_hens_residue_data_nine_fields`](Step019_hens_residue_data_nine_fields.lean) |  | `henselResidueDataOfKer`, `ramified_vanishing_ker_tame` | 92 |
| [`Step020_cup_pi_nonzero_injective`](Step020_cup_pi_nonzero_injective.lean) |  | `exists_cup_pi_ne_zero` | 65 |
| [`Step021_res_and_tame_u_pi_discharged`](Step021_res_and_tame_u_pi_discharged.lean) |  | `cupPi`, `cupPi_apply`, `kerCupPi`, `kerCupPi_apply` (+2 more) | 135 |
| [`Step022_ramified_vanishing_no_tame_symbol`](Step022_ramified_vanishing_no_tame_symbol.lean) |  | `henselResidueDataOfCup` | 85 |
| [`Step023_hens_residue_data_transport`](Step023_hens_residue_data_transport.lean) |  | `henselResidueDataTransport` | 91 |
| [`Step024_delta_two_refined`](Step024_delta_two_refined.lean) | `line:1050`, `line:1608` | `residuePhi`, `residuePhi_apply`, `residueSpan`, `cup_mem_residueSpan` (+8 more) | 352 |
| [`Step025_unit_norm_pth_power`](Step025_unit_norm_pth_power.lean) |  | `normUnits_mem_pow_of_val_eq_zero` | 114 |
| [`Step026_unit_norm_pth_power_from_valuation`](Step026_unit_norm_pth_power_from_valuation.lean) |  | `toAdd_zpow'`, `toAdd_val_zpow'`, `normUnits_mem_pow_of_valOfUnitOf_eq_zero` | 120 |
| [`Step027_norm_group_form`](Step027_norm_group_form.lean) |  | `mem_pow_of_mem_normGroup_of_valOfUnitOf_eq_zero` | 64 |
| [`Step028_residue_phi_injective`](Step028_residue_phi_injective.lean) |  | `adjoin_root_eq_top`, `residuePhi_injective_of_norm_form`, `tameResidueFacts_of_norm_form` | 115 |
| [`Step029_model_field_from_hypothesis`](Step029_model_field_from_hypothesis.lean) | `prop:prelim-residue` | `residuePhi_injective_of_norm_form'`, `tameResidueFacts_of_norm_form'` | 69 |
| [`Step030_r1_scaled_bridge`](Step030_r1_scaled_bridge.lean) |  | `kummerCup_smul_smul`, `cup_eq_zero_iff_mem_normGroup_of_scaled_bridge`, `residuePhi_injective_iff_norm_of_scaled_bridge`, `residuePhi_injective_of_norm_form_scaled` (+1 more) | 157 |
| [`Step031_r1_without_bridge_or_completeness`](Step031_r1_without_bridge_or_completeness.lean) |  | `scaled_bridge_uncond`, `valH1LinearGen_redEquiv1_smul`, `valLinOf_eq_zero_iff`, `residuePhi_injective_t1` (+2 more) | 221 |
| [`Step032_hskew_discharged`](Step032_hskew_discharged.lean) | `prop:prelim-residue` | `kummerCup_skew`, `exists_henselResidueData_uncond_noBridge'` | 88 |
| [`Step033_residue_sequence_exact_split`](Step033_residue_sequence_exact_split.lean) | `prop:prelim-residue` | `ker_val_eq_range_infl`, `exact_infl_val`, `res_surjective`, `isCompl_range_infl_span_pi` (+1 more) | 109 |
| [`Step034_delta_two_replaces_finite_residue`](Step034_delta_two_replaces_finite_residue.lean) |  | `tameResidueFacts_of_residueMap` | 102 |
| [`Step035_hens_residue_data_no_finite`](Step035_hens_residue_data_no_finite.lean) |  | `VKern`, `exists_henselResidueData_noFinite` | 49 |
| [`Step036_residue_cup_product_interface`](Step036_residue_cup_product_interface.lean) | `GS2017/lemma-residue-cup-product`, `line:1608`, `line:1636`, `line:1648` | `VKG`, `tameResidueFacts_Galo_of_residueMap`, `orth_eq_bot_noFinite`, `thm_ramified_1_noFinite` (+2 more) | 205 |
| [`Step037_exists_d_iff_tame_residue_facts`](Step037_exists_d_iff_tame_residue_facts.lean) |  | `exists_residueMap_iff_tameResidueFacts` | 63 |
| [`Step038_ker_v_finrank_pos`](Step038_ker_v_finrank_pos.lean) |  | `kc_two_ne_zero_G`, `kc_two_mem_ker`, `finrank_ker_valLinOf_pos` | 75 |
| [`Step039_residue_classes_linear_dependent`](Step039_residue_classes_linear_dependent.lean) |  | `residueUnitsEquiv`, `chi`, `chi_surjective`, `zmod7_cube_dependent_closed` (+1 more) | 76 |
| [`Step040_ker_v_finrank_le_one`](Step040_ker_v_finrank_le_one.lean) | `line:1648` | `zval_twoUnitF`, `kc_one`, `kc_inv`, `kc_eq_zero_of_residue_cube` (+3 more) | 151 |
| [`Step041_residue_map_single_hypothesis`](Step041_residue_map_single_hypothesis.lean) | `line:1023` | `UnitsCupVanish`, `tameResidueFacts_Galo_of_unitsCupVanish`, `exists_residueMap_of_unitsCupVanish`, `exists_henselResidueData_of_unitsCupVanish` (+2 more) | 170 |
| [`Step042_residue_span_subset_ker_res`](Step042_residue_span_subset_ker_res.lean) |  | `residueSpan_le_ker_res`, `disjoint_range_residuePhi`, `tameResidueFacts_of_data`, `faithfulR2_of_span_eq_bot` (+2 more) | 181 |
| [`Step043_units_mod_pth_powers_paper_level`](Step043_units_mod_pth_powers_paper_level.lean) | `line:992`, `prop:prelim-kummer-valuation` | `mem_subring_of_pow_mem`, `exists_unit_pow_eq`, `residue_pow_of_pow`, `unit_pow_iff_residue_pow_of_hensel` | 153 |
| [`Step044_residue_map_unramified_units`](Step044_residue_map_unramified_units.lean) | `GS2017/line:8160`, `GS2017/line:8163` | `continuous_smul_of_stabilizer_isOpen`, `knrUUnitsTopology`, `knrUUnitsDiscrete`, `knrUKerTopology` (+16 more) | 291 |
| [`Step045_residue_prop_two_literal`](Step045_residue_prop_two_literal.lean) | `line:1052` | `PaperTameResidueFormulas`, `paperFormulas_iff_obligation` | 87 |
| [`Step046_knr_residue_map_int`](Step046_knr_residue_map_int.lean) |  | `knrResidueMapInt`, `knrResidueMapInt_apply` | 70 |
| [`Step047_integral_bockstein_range`](Step047_integral_bockstein_range.lean) |  | `integralBockstein_available` | 76 |
| [`Step048_integral_bockstein_range_complete`](Step048_integral_bockstein_range_complete.lean) |  | `longExact_exact₁`, `integralBockstein_one_range` | 86 |
| [`Step049_integral_bockstein_usable`](Step049_integral_bockstein_usable.lean) |  | `integralBockstein_one_range_nsmul`, `h2KummerToUnits_range_available` | 69 |
| [`Step050_delta_two_additive`](Step050_delta_two_additive.lean) |  | `dimShiftAdd`, `knrProjCoeffAdd`, `kummerCoeffToKnrAdd`, `kummerResidueAdd` (+8 more) | 218 |
| [`Step051_h1_z_equiv_galo_v`](Step051_h1_z_equiv_galo_v.lean) | `line:1050` | `uliftZModCoeffIso`, `restrictScalarsH1`, `muPCoeffIso`, `h1ZModBridge` (+6 more) | 225 |
| [`Step052_delta_two_candidate_zero`](Step052_delta_two_candidate_zero.lean) | `GS2017/line:8160`, `GS2017/prop-units-cohomology` | `knrProjOn_kummerCoeffToKnrUnits`, `kummerCoeffToKnrUnits_mem_ker`, `kummerCoeffToUnits`, `kummerCoeffToUnits_apply` | 143 |
| [`Step053_exists_d_three_properties`](Step053_exists_d_three_properties.lean) | `line:1050` | `knrResidueObligation_of_three`, `knrResidueObligation_iff_exists_three`, `knrResidueObligation_of_reduced_regression` | 116 |
| [`Step054_delta_two_candidate_refuted`](Step054_delta_two_candidate_refuted.lean) |  | `resolutionMap_zero_eq`, `cochainsMap_zero_eq`, `map_zero_eq`, `coeffMap_zero_eq` (+9 more) | 216 |
| [`Step055_r2_exact_boundary`](Step055_r2_exact_boundary.lean) |  | `cup_self_eq_zero`, `residueSpan_eq_bot_of_isCyclic`, `tameResidueFacts_of_residueSpan_eq_bot`, `tameResidueFacts_of_isCyclic` (+3 more) | 196 |
| [`Step056_kummer_valuation_abstract_hensel`](Step056_kummer_valuation_abstract_hensel.lean) | `prop:prelim-kummer-valuation` | `residueUnits`, `residue_units_eq_one_iff`, `exists_pow_eq_of_residue_eq_one`, `principalUnit_mem_pow_range_of_eq_one` (+5 more) | 232 |
| [`Step057_residue_span_inflation`](Step057_residue_span_inflation.lean) |  | `muPQuot`, `muPQuot_ρ`, `trivialPairing`, `ResH1Type` (+10 more) | 273 |
| [`Step058_residue_span_canonical_carrier`](Step058_residue_span_canonical_carrier.lean) |  | `RInv`, `RInv_eq_top`, `RInvEquiv`, `qti_smul_eq_self` (+13 more) | 265 |
| [`Step059_mu_p_into_residue_units`](Step059_mu_p_into_residue_units.lean) |  | `geomSum_sub_eq`, `isUnit_of_mul_left`, `isUnit_sub_one_of_pow_eq_one`, `residueUnits_injective_on_pow_eq_one` (+1 more) | 169 |
| [`Step060_h_kappa_h2_zero`](Step060_h_kappa_h2_zero.lean) |  | `coeffIdHomK`, `inflH1`, `inflH2`, `cupK` (+6 more) | 204 |
| [`Step061_mu_p_in_residue_field`](Step061_mu_p_in_residue_field.lean) |  | `isPrimitiveRoot_residue`, `ch4TameSymbolHyp_of_subsingleton_H2_domain` | 147 |
| [`Step062_mu_p_residue_full_chain`](Step062_mu_p_residue_full_chain.lean) |  | `toAdd_eq_zero_of_pow_eq_one`, `mem_integer_of_pow_eq_one`, `exists_isPrimitiveRoot_integer`, `exists_isPrimitiveRoot_residue` (+1 more) | 155 |
| [`Step063_mu_p_residue_instance`](Step063_mu_p_residue_instance.lean) |  | `hasEnoughRootsOfUnity_residue`, `FbarValuationHyp'` | 102 |
| [`Step064_delta_two_definition`](Step064_delta_two_definition.lean) |  | `d_F5`, `hd_infl_d_F5`, `tameResidueFacts_of_hd_cup_pi` | 129 |
| [`Step065_partial_one_inputs`](Step065_partial_one_inputs.lean) |  | `explicitRes1_mem_H1ConjInvariants`, `res1V_mem_H1ConjInvariants`, `res1V_kummerClass_ne_zero_of_uniformizer`, `h1InertiaAddEquiv_self` (+1 more) | 165 |
| [`Step066_finrank_vkg_one_reduction`](Step066_finrank_vkg_one_reduction.lean) |  | `finrank_VKG_eq_one` | 74 |
| [`Step067_finrank_vkg_le_one`](Step067_finrank_vkg_le_one.lean) |  | `finrank_ker_le_one_of_exists_ne_zero`, `finrank_ker_le_one`, `finrank_VKG_le_one`, `finrank_VKG_eq_one_of_ne_zero` | 133 |
| [`Step068_infl_to_vkg_injective`](Step068_infl_to_vkg_injective.lean) |  | `inflToVAddHom_injective`, `inflToVKG_injective`, `exists_ne_zero_VKG_of_quot`, `finrank_VKG_eq_one_of_quot` | 107 |
| [`Step069_hcup_injectivity`](Step069_hcup_injectivity.lean) |  | `cupPiLin`, `projLin`, `exists_leftInverse_of_injective`, `injective_of_exists_leftInverse` | 136 |
| [`Step070_partial_one_pi_generator`](Step070_partial_one_pi_generator.lean) |  | `res1V_kummerClass_zmultiples_eq_top`, `res1V_kummerClass_spec` | 88 |
| [`Step071_delta_two_expansion`](Step071_delta_two_expansion.lean) |  | `deltaShift1_delta`, `delta_deltaShift1`, `deltaTwoShift_apply`, `deltaTwoShift_eq_of_delta_eq` | 111 |
| [`Step072_delta_two_factors_bijective`](Step072_delta_two_factors_bijective.lean) |  | `deltaShift1_injective`, `deltaShift1_surjective`, `deltaTwoShift_injective`, `deltaTwoShift_surjective` (+1 more) | 95 |
| [`Step073_delta_two_injective_reduction`](Step073_delta_two_injective_reduction.lean) |  | `deltaTwoCarrierInertia_injective_of_contM_injective`, `deltaTwoGaloBase'_injective_of_contM_injective` | 82 |
| [`Step074_delta_two_pi_cup_inf`](Step074_delta_two_pi_cup_inf.lean) |  | `h0Emb`, `cup01C`, `cup11A`, `h1BridgeQ_cup01` (+2 more) | 225 |
| [`Step075_cont_m_cup`](Step075_cont_m_cup.lean) |  | `contInvC_smul_eq_nsmul_val`, `h1Inertia_smul_eq_nsmul_val`, `quotient_smul_muPInv_trivial`, `quotient_smul_zmod_trivial` (+9 more) | 287 |
| [`Step076_res_bridges_explicit_continuous`](Step076_res_bridges_explicit_continuous.lean) |  | `e1_explicitRes1` | 63 |
| [`Step077_cont_delta_res_naturality`](Step077_cont_delta_res_naturality.lean) |  | `res_delta_zero_apply` | 65 |
| [`Step078_res_inertia_infl_image`](Step078_res_inertia_infl_image.lean) |  | `explicitRes0_explicitInfl0`, `e0_res_infl`, `h0Emb_res_infl` | 125 |
| [`Step079_cont_m_eq_explicit_res`](Step079_cont_m_eq_explicit_res.lean) |  | `contM_eq_explicitRes1`, `contM_eq_res1V_kummerClass` | 97 |
| [`Step080_cont_m_generator`](Step080_cont_m_generator.lean) |  | `contM_ne_zero`, `contM_zmultiples_eq_top` | 108 |
| [`Step081_explicit_cup01`](Step081_explicit_cup01.lean) |  | `zsie_symm_explicitH2OfDiscrete`, `zsie_symm_cup_eq`, `cup11A_eq_e2_cupLin`, `deltaTwoGaloBase'_cup_eq_neg_explicitCup01` | 177 |
| [`Step082_explicit_cup_nonzero`](Step082_explicit_cup_nonzero.lean) |  | `explicitCup01_ne_zero_of_leftInverse` | 100 |
| [`Step083_left_inverse_coeff_map`](Step083_left_inverse_coeff_map.lean) |  | `exists_leftInverse_coeff` | 109 |
| [`Step084_explicit_cup01_nonzero`](Step084_explicit_cup01_nonzero.lean) |  | `explicitCup01_contM_ne_zero` | 108 |
