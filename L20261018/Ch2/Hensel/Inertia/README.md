# `L20261018/Ch2/Hensel/Inertia` — sec. 2.4 · inertia, K_nr, the cohomological dimension of I

40 modules.  Part of the development's [index](../../../README.md); see also [`DECLARATIONS.md`](../../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../../RENAME-MAP.tsv).

Source items formalised here: `GS2017/cons-residue-map-finite-coefficients-2`, `GS2017/sec:cohomology-complete-dv`; 11 line anchors.

| module | source item | declarations | lines |
|---|---|---|---|
| [`Step001_inertia_exact_sequence_first`](Step001_inertia_exact_sequence_first.lean) |  | `inertiaSubgroup_normal`, `decompToResidue`, `decompQuotEquivRange`, `decompQuotToResidue_injective` | 66 |
| [`Step002_knr_definition`](Step002_knr_definition.lean) |  | `inertiaAbs`, `Knr`, `inertiaAbs_le_fixingSubgroup_Knr`, `Knr_def` | 65 |
| [`Step003_knr_galois_quotient`](Step003_knr_galois_quotient.lean) | `GS2017/sec:cohomology-complete-dv` | `inertiaAbs_le_decompositionSubgroup`, `inertiaAbs_normal_of_decomp_eq_top`, `isGalois_Knr`, `isGalois_Knr_of_decomp_eq_top` (+8 more) | 218 |
| [`Step004_knr_galois_zhat`](Step004_knr_galois_zhat.lean) | `GS2017/sec:cohomology-complete-dv` | `KnrLoc`, `inertiaLoc`, `isGalois_KnrLoc`, `normal_KnrLoc` (+13 more) | 175 |
| [`Step005_knr_explicit_laurent`](Step005_knr_explicit_laurent.lean) | `GS2017/line:8162`, `GS2017/line:8165` | `ZMod0`, `knrUnit`, `knrVal`, `knrUnit_coe` (+10 more) | 226 |
| [`Step006_knr_coefficient_action`](Step006_knr_coefficient_action.lean) | `GS2017/line:8156`, `GS2017/line:8160` | `knrMap`, `knrMap_apply`, `knrMap_coeff`, `knrMap_id` (+4 more) | 205 |
| [`Step007_knr_correct_carrier`](Step007_knr_correct_carrier.lean) | `GS2017/line:8152` | `coeffIncl`, `coeffIncl_coeff`, `FinInt`, `finInt_sup` (+5 more) | 134 |
| [`Step008_gs61_on_correct_knr`](Step008_gs61_on_correct_knr.lean) | `GS2017/line:8162`, `GS2017/line:8163` | `knrUnit_mem`, `knrUnitOn`, `knrUnitOn_coe`, `knrUnitIncl` (+13 more) | 193 |
| [`Step009_galois_preserves_knr`](Step009_galois_preserves_knr.lean) | `GS2017/line:8156`, `GS2017/line:8160` | `mapField`, `mapField_finite`, `coeffAlg`, `coeffIncl_knrMap` (+9 more) | 171 |
| [`Step010_knr_continuous_smul`](Step010_knr_continuous_smul.lean) | `GS2017/line:8160`, `GS2017/line:8162` | `knrMap_eq_self_of_mem_fixing`, `fixingSubgroup_le_stabilizer`, `isOpen_stabilizer`, `knrSubfieldTopologicalSpace` (+2 more) | 126 |
| [`Step011_kummer_coeff_to_knr`](Step011_kummer_coeff_to_knr.lean) | `GS2017/line:8152`, `GS2017/line:8160` | `rootsOfUnity_isIntegral`, `kummerSeries_mem_Knr`, `kummerUnitOn`, `kummerUnitOn_coe` (+1 more) | 128 |
| [`Step012_kummer_coeff_equivariant`](Step012_kummer_coeff_equivariant.lean) | `GS2017/line:8176` | `knrMap_single_zero`, `kummerCoeffToKnrUnits_equivariant`, `kummerCoeffToKnr`, `kummerResidueMap` | 112 |
| [`Step013_inertia_pro_p_sylow_data`](Step013_inertia_pro_p_sylow_data.lean) | `GS2017/line:9625`, `GS2017/line:9627` | `InertiaProPSylowData`, `cohomologicalDimensionAt_le_padicInt`, `cohomologicalDimensionAt_le_one`, `cdLE` (+5 more) | 157 |
| [`Step014_cd_p_inertia_instance`](Step014_cd_p_inertia_instance.lean) | `GS2017/cons-residue-map-finite-coefficients-2`, `GS2017/line:9627` | `inertia_cohomologicalDimensionAt_le_one`, `inertia_cdLE`, `inertia_subsingleton_Hq`, `inertia_subsingleton_H2_zmod` (+1 more) | 126 |
| [`Step015_cd_p_procyclic_criterion`](Step015_cd_p_procyclic_criterion.lean) | `serre-p67-prop7-cors.txt/line:8` | `padicEquiv_of_procyclic`, `inertiaProPSylowData_of_procyclic`, `cdLE_of_procyclic`, `subsingleton_H2_of_procyclic` (+2 more) | 132 |
| [`Step016_inertia_loc_carrier_alignment`](Step016_inertia_loc_carrier_alignment.lean) | `serre-p67-prop7-cors.txt/line:8` | `inertiaLoc_eq_map_inertiaSubgroup`, `map_inertiaSubgroup_eq_inertiaLoc` | 76 |
| [`Step017_tame_module_procyclic`](Step017_tame_module_procyclic.lean) | `serre-p67-prop7-cors.txt/line:8` | `residueChar`, `exists_generator_primeToPTateModule` | 68 |
| [`Step018_procyclic_l_part_sylow`](Step018_procyclic_l_part_sylow.lean) | `GS2017/line:9626` | `isProPSylow_closedZpowers_zpowHat_idem`, `padicEquiv_closedZpowers_zpowHat_idem`, `inertiaProPSylowData_of_procyclic_group`, `cdLE_of_procyclic_group` | 175 |
| [`Step019_tame_module_l_part_infinite`](Step019_tame_module_l_part_infinite.lean) |  | `TameModel`, `proj_surjective_primeToPTateModule`, `infinite_tameModel_pPart`, `inertiaProPSylowData_tameModel` | 168 |
| [`Step020_inertia_sylow_mod_ramification`](Step020_inertia_sylow_mod_ramification.lean) |  | `toTameInertia`, `toTameInertia_surjective`, `isProPSylow_map_toTameInertia`, `inf_wildInertia_eq_bot` (+1 more) | 155 |
| [`Step021_inertia_sylow_z_l`](Step021_inertia_sylow_z_l.lean) |  | `continuousMulEquivOfBijective`, `inertiaSubgroup_compactSpace`, `tameInertia_compactSpace`, `tameModelEquivTameInertia` (+4 more) | 246 |
| [`Step022_cd_p_inertia_unconditional`](Step022_cd_p_inertia_unconditional.lean) | `GS2017/line:9627` | `inertiaEquivInertiaLoc`, `InertiaProPSylowData.congrContinuousMulEquiv`, `inertiaProPSylowData_inertiaLoc`, `inertiaLoc_cohomologicalDimensionAt_le_one` (+4 more) | 166 |
| [`Step023_b1_hom_inertia_mu_p`](Step023_b1_hom_inertia_mu_p.lean) |  | `inertiaLoc_Hq_eq_zero`, `inertiaLoc_Hq_zmod_eq_zero`, `continuousZModDual_wildInertia_subsingleton` | 164 |
| [`Step024_hom_inertia_tame`](Step024_hom_inertia_tame.lean) |  | `wildInertia_le_ker_zmodDual`, `restrictTameInertia`, `restrictTameInertia_injective`, `restrictTameInertia_surjective` (+5 more) | 244 |
| [`Step025_h1_inertia_finite`](Step025_h1_inertia_finite.lean) |  | `hom_cont_eval_injective`, `finite_hom_cont_tameModel_zmod`, `natCard_hom_cont_tameModel_zmod_le`, `equivTameModelInertia` (+3 more) | 164 |
| [`Step026_hom_inertia_mu_p_eq_zmod`](Step026_hom_inertia_mu_p_eq_zmod.lean) |  | `exists_primitiveComponents`, `levelP`, `shiftedHom`, `shiftedHom_apply_zeta` (+6 more) | 260 |
| [`Step027_cd_l_inertia_vanishing`](Step027_cd_l_inertia_vanishing.lean) |  | `CohomologicalDimensionLE`, `GsInputHyp`, `gsInputHyp_of_cdLE`, `gsInputHyp_apply` | 95 |
| [`Step028_inertia_subgroup_galois`](Step028_inertia_subgroup_galois.lean) |  | `FbarValuationHyp₄`, `hstab_of_hval`, `inertia`, `mem_inertia` | 126 |
| [`Step029_inertia_normal`](Step029_inertia_normal.lean) |  | `inertia_normal` | 73 |
| [`Step030_inertia_maximal_ideal`](Step030_inertia_maximal_ideal.lean) |  | `mem_inertia_iff_sub_mem_maximalIdeal`, `mem_inertia_iff_residue_eq` | 104 |
| [`Step031_residue_action_well_defined`](Step031_residue_action_well_defined.lean) |  | `residue_action_welldef` | 95 |
| [`Step032_residue_action_kernel`](Step032_residue_action_kernel.lean) |  | `subringAct`, `subringAct_coe`, `subringAct_comp_self`, `subringAct_self_comp` (+11 more) | 218 |
| [`Step033_unramified_kummer_hyp`](Step033_unramified_kummer_hyp.lean) |  | `UnramifiedKummer`, `unramifiedKummer_of_subsingleton`, `residueSpan_le_range_infl2Res_of_kummer` | 86 |
| [`Step034_inertia_restriction_res1`](Step034_inertia_restriction_res1.lean) |  | `explicitRes1_explicitCoeff1Equiv_comp`, `res1V`, `res1V_apply`, `res1V_kummerClass_eq` | 136 |
| [`Step035_ker_v_eq_ker_res1`](Step035_ker_v_eq_ker_res1.lean) |  | `explicitRes1_inertiaLoc_eq_zero_iff`, `explicitRes1_inertiaLoc_kummerMap_eq_zero_iff`, `kummerCoeffInertiaEquiv`, `kummerCoeffInertiaEquiv_apply` (+4 more) | 247 |
| [`Step036_unramified_kummer_theorem`](Step036_unramified_kummer_theorem.lean) |  | `instSMulQuotZMod`, `instMulActionQuotZMod`, `instDistribMulActionQuotZMod`, `instSMulCommClassQuotZModInt` (+12 more) | 331 |
| [`Step037_unramified_kummer_paper_level`](Step037_unramified_kummer_paper_level.lean) |  | `unitsCoe`, `unitsCoe_apply`, `exists_valuationRing_unit_of_val_eq_one`, `val_eq_one_of_mem_unitFiltration_zero` (+4 more) | 230 |
| [`Step038_h1_inertia_one_dim`](Step038_h1_inertia_one_dim.lean) |  | `ne_of_coprime`, `natCard_hom_cont_inertiaLoc_eq`, `natCard_h1Inertia_eq` | 80 |
| [`Step039_h1_inertia_zmod`](Step039_h1_inertia_zmod.lean) |  | `zmodLinearEquivOfCardPrime`, `h1InertiaLinearEquiv` | 114 |
| [`Step040_tame_character_galois_invariant`](Step040_tame_character_galois_invariant.lean) |  | `exists_primitiveRoot_alg`, `absoluteGaloisGroup_fixes_pow_eq_one`, `zmodEquivMuP`, `tamePCharHom` (+7 more) | 230 |
