# `L20261018/Infra/Cohomology/Coinduced` — sec. 2.3 · coinduced modules, invariants, GS (6.17)

41 modules.  Part of the development's [index](../../../README.md); see also [`DECLARATIONS.md`](../../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../../RENAME-MAP.tsv).

| module | paper | declarations | lines |
|---|---|---|---|
| [`Step001_coind_subgroup_acyclic_hyp`](Step001_coind_subgroup_acyclic_hyp.lean) |  | `CoindSubgroupAcyclic`, `coindSubgroupAcyclic_bot`, `coindShortExactSubgroup`, `subsingleton_cohomology_quot_subgroup` | 124 |
| [`Step002_coind_subgroup_acyclic_carrier`](Step002_coind_subgroup_acyclic_carrier.lean) |  | `inertia_Q_subsingleton_Hq` | 104 |
| [`Step003_coind_subgroup_acyclic_one`](Step003_coind_subgroup_acyclic_one.lean) |  | `CoindSubgroupAcyclicOne`, `coindSubgroupAcyclicOne_bot`, `subsingleton_H1_quot_subgroup` | 108 |
| [`Step004_finite_index_coset_decomposition`](Step004_finite_index_coset_decomposition.lean) |  | `cosRep`, `hCoord`, `cosRep_mul_hCoord`, `mk_mul_coe` (+15 more) | 240 |
| [`Step005_closed_subgroup_acyclicity`](Step005_closed_subgroup_acyclicity.lean) |  | `finiteIndex_of_isOpen`, `coindSubgroupAcyclicOne`, `subsingleton_H1_quot_subgroup_of_isClosed` | 99 |
| [`Step006_inf_h1_iso_closed_subgroup`](Step006_inf_h1_iso_closed_subgroup.lean) |  | `infl1_surjective_of_H1_subsingleton`, `infl1AddEquiv_of_H1_subsingleton`, `subsingleton_H1_of_continuousCohomology`, `infl1AddEquiv_of_coindAcyclic` | 106 |
| [`Step007_delta_zero_quotient_morphism`](Step007_delta_zero_quotient_morphism.lean) |  | `quotientConjAction_mk_smul`, `delta_zero_conjNormal`, `delta_zero_quotientConj` | 102 |
| [`Step008_delta_two_first_factors`](Step008_delta_two_first_factors.lean) |  | `deltaShift1`, `h1BridgeQ`, `inflStep`, `inflStep_explicitInfl1` (+1 more) | 115 |
| [`Step009_c2_f_interface`](Step009_c2_f_interface.lean) |  | `contM_add`, `contM_zero`, `contMHom`, `contM_coeffMap` | 77 |
| [`Step010_delta_two_carrier_assembly`](Step010_delta_two_carrier_assembly.lean) |  | `deltaTwoCarrier` | 58 |
| [`Step011_hc_inertia_discharged`](Step011_hc_inertia_discharged.lean) |  | `isPPrimaryTorsion_zmod_p`, `inertiaLoc_subsingleton_H1_contC`, `deltaTwoCarrierInertia` | 85 |
| [`Step012_coinduced_invariants_forward`](Step012_coinduced_invariants_forward.lean) |  | `coindBot_apply_mul_of_mem`, `coindInvFun`, `coindInvFun_isLocallyConstant`, `coindBot_apply_out` | 85 |
| [`Step013_coinduced_invariants_backward`](Step013_coinduced_invariants_backward.lean) |  | `coindRevFun`, `coindRevFun_isLocallyConstant`, `coindRev`, `mk_mul_coe_I` (+6 more) | 156 |
| [`Step014_coinduced_invariants`](Step014_coinduced_invariants.lean) |  | `coindBotInvariantsEquiv_smul`, `coindBotInvariantsIntLinearEquiv`, `continuousSMul_bot_quotient`, `subsingleton_H_quot_coindBot_invariants` | 122 |
| [`Step015_gs617_compatibility_square`](Step015_gs617_compatibility_square.lean) |  | `delta_map_quotient_T` | 87 |
| [`Step016_gs617_ses1`](Step016_gs617_ses1.lean) |  | `inclI`, `inclI_quotient_smul`, `TBI`, `range_stable` (+1 more) | 121 |
| [`Step017_ses1_delta_one_iso`](Step017_ses1_delta_one_iso.lean) |  | `delta_injective_sesCoind1`, `delta_surjective_sesCoind1`, `delta_bijective_sesCoind1`, `deltaAddEquiv_sesCoind1` (+2 more) | 163 |
| [`Step018_iota_delta_zero_zero`](Step018_iota_delta_zero_zero.lean) |  | `projI`, `projI_apply`, `projI_quotient_smul`, `projI_comp_inclI` (+6 more) | 184 |
| [`Step019_cont_m_iota_zero`](Step019_cont_m_iota_zero.lean) |  | `delta_zero_comp_projRestrCoeff`, `contM_comp_projI`, `contM_comp_iota` | 87 |
| [`Step020_map_phi_decomposition`](Step020_map_phi_decomposition.lean) |  | `coeffMap_comp_map_quotientMk` | 68 |
| [`Step021_h1_bridge_coeff_comm`](Step021_h1_bridge_coeff_comm.lean) |  | `h1BridgeQ_coeffMap`, `h1BridgeQ_comp_coeffMap` | 94 |
| [`Step022_h1_bridge_infl_comm`](Step022_h1_bridge_infl_comm.lean) |  | `h1BridgeQ_infl` | 99 |
| [`Step023_cont_m_coeff_map`](Step023_cont_m_coeff_map.lean) |  | `iotaHom`, `iotaHom_comp_eq_zero` | 70 |
| [`Step024_explicit_coeff_one_zero`](Step024_explicit_coeff_one_zero.lean) |  | `explicitCoeff1_eq_zero_of_apply_eq_zero`, `explicitCoeff1_zero`, `coeffMap_comp_coeffMap_eq_zero` | 95 |
| [`Step025_square_elimination`](Step025_square_elimination.lean) |  | `deltaAddEquivOfSub`, `deltaAddEquivOfSub_apply`, `delta_inv_comp_infl_eq` | 120 |
| [`Step026_delta_two_inf_two_zero`](Step026_delta_two_inf_two_zero.lean) |  | `fCG`, `fCG_compat`, `map_fCG_apply`, `deltaShift1_eq_deltaAddEquivOfSub` (+1 more) | 238 |
| [`Step027_continuous_smul_criterion`](Step027_continuous_smul_criterion.lean) |  | `continuous_smul_of_forall_continuous` | 65 |
| [`Step028_delta_two_carrier_inertia`](Step028_delta_two_carrier_inertia.lean) |  | `deltaTwoCarrierInertia_comp_infl_eq_zero` | 99 |
| [`Step029_second_carrier_square`](Step029_second_carrier_square.lean) |  | `eQ2`, `h2ToGaloBase`, `infl2Res_eQ2` | 103 |
| [`Step030_coefficient_bridge_m_inv`](Step030_coefficient_bridge_m_inv.lean) |  | `mem_fixedPoints_zmod`, `coeffSubAddHom`, `coeffSubAddHom_apply` | 56 |
| [`Step031_coefficient_bridge_explicit_model`](Step031_coefficient_bridge_explicit_model.lean) |  | `subtype_comp_coeffSubAddHom`, `coeffSubAddHom_smul`, `explicitMap2_id_eq_subtype_comp` | 120 |
| [`Step032_a1_last_step`](Step032_a1_last_step.lean) |  | `explicitMap2_quot_subtype_eq_comp` | 90 |
| [`Step033_delta_two_infl_zero_carrier`](Step033_delta_two_infl_zero_carrier.lean) |  | `explicitMap2_subtype_comp_coeff`, `explicitMap2_quot_id_eq_subtype_comp` | 98 |
| [`Step034_delta_two_map_phi_zero`](Step034_delta_two_map_phi_zero.lean) |  | `deltaTwoCarrierInertia_map_pair_id_eq_zero` | 111 |
| [`Step035_delta_two_cup_y_z_zero`](Step035_delta_two_cup_y_z_zero.lean) |  | `deltaTwoGaloBase'`, `deltaTwoGaloBase'_apply`, `deltaTwoGaloBase'_h2ToGaloBase`, `deltaTwoGaloBase'_infl2Res_eq_zero` (+1 more) | 142 |
| [`Step036_res_h1_type_equiv_vkg`](Step036_res_h1_type_equiv_vkg.lean) |  | `explicitMap1_subtype_comp_coeff`, `res1V_h1ToVEquiv`, `explicitMap1_quot_id_eq_infl_comp_coeff`, `explicitMap1_quot_id_injective` (+5 more) | 245 |
| [`Step037_h0_leibniz_parts`](Step037_h0_leibniz_parts.lean) |  | `contC_nsmul_eq_zero`, `contCModule`, `contC_smul_eq_nsmul_val`, `contC_smul_comm_G` (+10 more) | 232 |
| [`Step038_h0_leibniz`](Step038_h0_leibniz.lean) |  | `coindSES_delta_one_eq_explicit`, `coindSES_delta_zero_eq_explicit`, `contLeibniz_cup01` | 174 |
| [`Step039_delta_zero_surjective`](Step039_delta_zero_surjective.lean) |  | `contC_exists_delta_zero_eq`, `contC_exists_delta_zero_eq_of_H1` | 81 |
| [`Step040_e_zero_surjective_leibniz`](Step040_e_zero_surjective_leibniz.lean) |  | `h0Iso_surjective`, `contLeibniz_cup01_cont`, `contC_exists_cup_preimage` | 104 |
| [`Step041_infl_inverse_cup`](Step041_infl_inverse_cup.lean) |  | `inflStep_explicitCup01`, `h0_exists_preimage`, `inflStep_cup01_infl` | 171 |
