# `L20261018/Ch2/Kummer` — sec. 2.2 · Kummer theory, cup products, the cyclic norm criterion

51 modules.  Part of the development's [index](../../README.md); see also [`DECLARATIONS.md`](../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../RENAME-MAP.tsv).

Source items formalised here: `cor:symbol-cup`, `prop:prelim-kummer-valuation`.

| module | source item | declarations | lines |
|---|---|---|---|
| [`Step001_cup_projection_res_right`](Step001_cup_projection_res_right.lean) |  | `explicitCup_projection_res_right` | 32 |
| [`Step002_projection_formula_continuous`](Step002_projection_formula_continuous.lean) |  | `continuousCup_projection_res_right` | 84 |
| [`Step003_triple_cup_product`](Step003_triple_cup_product.lean) |  | `V`, `H2`, `H3`, `cupH` (+6 more) | 112 |
| [`Step004_restriction_kummer_kernel`](Step004_restriction_kummer_kernel.lean) |  | `kummerRes_kummerMap_eq_one_iff`, `kummerRes_kummerIso_eq_one_iff` | 45 |
| [`Step005_bi_kummer_kernel_field`](Step005_bi_kummer_kernel_field.lean) |  | `le_mul_pow_of_kummerField_eq` | 84 |
| [`Step006_bi_kummer_kernel_intersection`](Step006_bi_kummer_kernel_intersection.lean) |  | `mem_sup_of_isPow_in_kummerField` | 158 |
| [`Step007_kummer_class_coefficient_bridge`](Step007_kummer_class_coefficient_bridge.lean) |  | `kummerCoeffLinearEquiv`, `primitiveRoot`, `primitiveRoot_spec`, `kummerH1Equiv` (+3 more) | 103 |
| [`Step008_bi_kummer_kernel_restriction`](Step008_bi_kummer_kernel_restriction.lean) |  | `KF`, `kummerRes_kummerMap_eq_one_iff_mem_sup` | 89 |
| [`Step009_pth_power_field_trivial`](Step009_pth_power_field_trivial.lean) |  | `mem_bot_of_pow_eq_one`, `adjoin_rootSet_eq_bot_of_isPow` | 80 |
| [`Step010_cup_fp_eq_galo_cup`](Step010_cup_fp_eq_galo_cup.lean) |  | `downCLM`, `upCLM`, `down_intertwining`, `up_intertwining` (+2 more) | 98 |
| [`Step011_cup_fp_eq_galo_cup_equiv`](Step011_cup_fp_eq_galo_cup_equiv.lean) |  | `hcompat`, `cupFp_coeffMap_eq_cup`, `cup_compat_statement` | 90 |
| [`Step012_symbol_cup`](Step012_symbol_cup.lean) | `cor:symbol-cup` | `kummerCupPairing_skew`, `kummerBrauerClass_swap`, `symbolAlg_brauerClass_eq_verbatim` | 95 |
| [`Step013_mu_p_equiv_zmod`](Step013_mu_p_equiv_zmod.lean) |  | `kummerCoeffEquivZMod`, `kummerCoeff_smul_eq_self` | 56 |
| [`Step014_mu_p_linear_equiv`](Step014_mu_p_linear_equiv.lean) |  | `kummerCoeffEquivZMod_map_smul`, `kummerCoeffLinearMap`, `kummerCoeffLinearEquiv` | 61 |
| [`Step015_primitive_root_scalar`](Step015_primitive_root_scalar.lean) |  | `zmodEquivRootsOfUnity_eq_comp_natCast`, `zmodEquivRootsOfUnity_eq_comp`, `zmodEquivRootsOfUnity_symm_eq_smul` | 84 |
| [`Step016_zeta_independence_carrier`](Step016_zeta_independence_carrier.lean) |  | `addEquiv_map_zmod_smul`, `addEquiv_symm_eq_smul`, `coeffMap_smul`, `unitRoot` (+8 more) | 208 |
| [`Step017_kummer_class_pow_identities`](Step017_kummer_class_pow_identities.lean) | `prop:prelim-kummer-valuation` | `p_smul_V_eq_zero`, `kummerClass_pow`, `kummerClass_pow_prime`, `kummerClass_mul_pow_eq` | 36 |
| [`Step018_bridge_kc_def`](Step018_bridge_kc_def.lean) |  | `bridgeKc`, `bridgeKc_one` | 31 |
| [`Step019_kummer_class_route_a_normal_form`](Step019_kummer_class_route_a_normal_form.lean) |  | `instContinuousSMulMuP`, `muP_explicitH1_eq_restrictScalars`, `h1ToVEquiv_apply_eq_muP`, `kummerClass_eq_muP_explicitH1` | 83 |
| [`Step020_route_b_normal_form`](Step020_route_b_normal_form.lean) |  | `muNRep_explicitH1_eq_restrictScalars` | 52 |
| [`Step021_bridge_first_segment`](Step021_bridge_first_segment.lean) |  | `kummerExplicit_eq`, `kummerClass_eq_h1ToVEquiv_kummerExplicit`, `h1ToVEquiv_kummerExplicit_eq` | 47 |
| [`Step022_pairing_compatibility`](Step022_pairing_compatibility.lean) |  | `zmodMulPairing_eq_muPairing` | 38 |
| [`Step023_cup_compatible_mu_p`](Step023_cup_compatible_mu_p.lean) |  | `cup_compat_muP` | 47 |
| [`Step024_r1_sigma_residual_is_t1_bridge`](Step024_r1_sigma_residual_is_t1_bridge.lean) |  | `redEquiv1_symm_kummerClass`, `scaled_bridge_of_bridgeKc`, `residuePhi_injective_of_bridgeKc` | 97 |
| [`Step025_t1_reduction_factor_separation`](Step025_t1_reduction_factor_separation.lean) |  | `eDouble`, `kce_eq_eDouble_comp`, `kummerCoeff_smul_trivial`, `muNRep_smul_trivial` | 94 |
| [`Step026_t1_coefficient_iso_composition`](Step026_t1_coefficient_iso_composition.lean) |  | `eDouble_comp_eq_kce` | 46 |
| [`Step027_t1_mu_n_rep_factorization`](Step027_t1_mu_n_rep_factorization.lean) |  | `instDistribMulActionAbsGaloisZMod`, `instContinuousSMulAbsGaloisZMod`, `eCoeffHom`, `eDoubleHom` (+7 more) | 268 |
| [`Step028_t1_explicit_map1_linear`](Step028_t1_explicit_map1_linear.lean) |  | `explicitMap1_eq_nsmul`, `instContinuousSMulTrivialFp`, `muHom`, `muHom_comp_kce` (+3 more) | 186 |
| [`Step029_t1_group_variable_cancel`](Step029_t1_group_variable_cancel.lean) |  | `kummerMapToTrivialFp_eq_merged`, `instContinuousSMulTrivialFpGen`, `cohomFpMap_ofDiscrete` | 163 |
| [`Step030_t1_bridge_gm_bypass`](Step030_t1_bridge_gm_bypass.lean) |  | `restrictEquiv_comp_symm`, `muHomAbs`, `muHomAbs_equivariant`, `cohomFpMap_symm_comp_restrict` (+1 more) | 209 |
| [`Step031_t1_model_comparison`](Step031_t1_model_comparison.lean) |  | `coeffMap_ofDiscrete`, `h1ToVEquiv_eq_muP`, `kummerClass_eq_muP` | 119 |
| [`Step032_t1_bridge_same_shape`](Step032_t1_bridge_same_shape.lean) |  | `explicitMap1_comp_coeff`, `downHom`, `bridgeKc_eq_muP` | 121 |
| [`Step033_t1_closed`](Step033_t1_closed.lean) |  | `instContinuousSMulMuPH223`, `zmod_smul_eq_val_nsmul`, `coeff_scalar`, `t1_closed_of_hζ` (+2 more) | 234 |
| [`Step034_hbridge_scalar_source`](Step034_hbridge_scalar_source.lean) |  | `exists_smul_kummerCoeffLinearEquiv` | 57 |
| [`Step035_hbridge_single_equation`](Step035_hbridge_single_equation.lean) |  | `hbridge_iff_eq_bridgeKc` | 62 |
| [`Step036_kc_scalar_from_coefficient`](Step036_kc_scalar_from_coefficient.lean) |  | `kummerH1EquivCanon` | 50 |
| [`Step037_kc_scalar_transfer`](Step037_kc_scalar_transfer.lean) |  | `smulHom`, `kummerH1Equiv_eq_smul_canon` | 90 |
| [`Step038_bridges_without_completeness`](Step038_bridges_without_completeness.lean) |  | `h1ToVEquiv_eq_muP'`, `kummerH1Equiv_apply_eq'`, `kummerClass_eq_thetaOne'`, `kummerClass_eq_muP'` | 86 |
| [`Step039_t1_without_completeness`](Step039_t1_without_completeness.lean) |  | `instContinuousSMulMuP320`, `bridgeKc_eq_muP'`, `zmod_smul_eq_val_nsmul'`, `coeff_scalar'` (+2 more) | 240 |
| [`Step040_theta_bridge_without_local_field`](Step040_theta_bridge_without_local_field.lean) |  | `theta1g`, `theta2g`, `theta1g_apply`, `theta2g_apply` | 57 |
| [`Step041_theta_bridge_true_hypothesis`](Step041_theta_bridge_true_hypothesis.lean) |  | `cup_compat_muP_zmod_lc`, `cup_compat_theta_locallyCompact`, `theta1_kummerClass_lc`, `cup_compat_theta_F` (+1 more) | 109 |
| [`Step042_mu_p_module_structure`](Step042_mu_p_module_structure.lean) |  | `muP`, `rootsOfUnity_nsmul_eq_zero`, `rootsOfUnityModule`, `zmod_smul_val` (+8 more) | 190 |
| [`Step043_kummer_bridge_on_h2`](Step043_kummer_bridge_on_h2.lean) |  | `muH1Equiv`, `muH2Equiv`, `galoBaseV_eq`, `galoBaseH2_eq` (+1 more) | 78 |
| [`Step044_kummer_coeff_category_entry`](Step044_kummer_coeff_category_entry.lean) |  | `natCard_kummerCoeff_available`, `kummerCoeffEquivMuNRep_available`, `muNRep_smul_trivial_available` | 67 |
| [`Step045_kummer_coeff_zmod_instance`](Step045_kummer_coeff_zmod_instance.lean) |  | `kummerCoeff_nsmul_eq_zero`, `restrictScalarsInt_available` | 60 |
| [`Step046_zmod_equiv_kummer_coeff`](Step046_zmod_equiv_kummer_coeff.lean) |  | `kummerCoeffMort` | 57 |
| [`Step047_kummer_coeff_bridge_chain_known`](Step047_kummer_coeff_bridge_chain_known.lean) |  | `kummerCoeffLinearEquiv_available`, `muPIso_available`, `muH2Equiv_available` | 75 |
| [`Step048_kummer_coeff_bridge_closed`](Step048_kummer_coeff_bridge_closed.lean) |  | `kummerCoeffMuRealEquiv`, `muKummerCoeff`, `kummerCoeffMuRealIso`, `kummerCoeffMuRealCohomologyIso` | 83 |
| [`Step049_two_cup_formulas_remaining`](Step049_two_cup_formulas_remaining.lean) |  | `KnrResidueObligation`, `ch4TameSymbolHyp_of_obligation` | 81 |
| [`Step050_h2_equiv_h2_z`](Step050_h2_equiv_h2_z.lean) |  | `kummerH2Bridge` | 52 |
| [`Step051_cup_steinberg_relation`](Step051_cup_steinberg_relation.lean) |  | `cupFp_kummerClass_eq_zero_of_add_eq_one`, `cup_bridgeKc_of_add_eq_one`, `cup_smul_smul`, `cup_kummerClass_of_add_eq_one` (+1 more) | 210 |
