# `L20261018/Infra/Cohomology/Boundary` — sec. 2.3 · the Hochschild-Serre boundary map, assembled

35 modules.  Part of the development's [index](../../../README.md); see also [`DECLARATIONS.md`](../../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../../RENAME-MAP.tsv).

Source items formalised here: 4 line anchors.

| module | source item | declarations | lines |
|---|---|---|---|
| [`Step001_acyclicity_short_exact`](Step001_acyclicity_short_exact.lean) |  | `subsingleton_cohomology_three_of_acyclic`, `subsingleton_cohomology_three_of_coind` | 90 |
| [`Step002_coinduced_embedding`](Step002_coinduced_embedding.lean) |  | `coindIncl`, `coindIncl_apply`, `coindIncl_injective`, `coindIncl_equivariant` | 78 |
| [`Step003_coinduced_quotient`](Step003_coinduced_quotient.lean) |  | `coindSub`, `coindSub_stable`, `coindQuot`, `proj` (+3 more) | 98 |
| [`Step004_coinduced_ses_acyclic`](Step004_coinduced_ses_acyclic.lean) |  | `Q`, `smul_mk`, `proj_equivariant`, `coindShortExact` (+1 more) | 94 |
| [`Step005_coinduced_invariants_recon`](Step005_coinduced_invariants_recon.lean) |  | `gs_coind_invariants_restrict`, `gs_coind_invariants_quotient` | 69 |
| [`Step006_delta_two_dimension_shift`](Step006_delta_two_dimension_shift.lean) |  | `coindBotSES`, `coindBot_dimensionShift`, `coindBot_dimensionShift_two` | 65 |
| [`Step007_delta_two_gating`](Step007_delta_two_gating.lean) |  | `isZero_res_dimensionShiftUp`, `isZero_res_dimensionShiftUp_one`, `isZero_res_dimensionShiftUp_of_cd` | 82 |
| [`Step008_delta_two_inflation_iso`](Step008_delta_two_inflation_iso.lean) |  | `isIso_HInfRes_dimensionShiftUp`, `inflationIso_dimensionShiftUp`, `inflationIso_dimensionShiftUp_hom`, `inflationIso_dimensionShiftUp_oneH` (+1 more) | 86 |
| [`Step009_delta_two_third_segment`](Step009_delta_two_third_segment.lean) |  | `deltaZero_coindBot`, `deltaZero_coindBot_eq`, `epi_deltaZero_coindBot` | 70 |
| [`Step010_conj_map`](Step010_conj_map.lean) |  | `conjSubtypeHom`, `conjSubtypeHom_coe` | 71 |
| [`Step011_conj_coeff_hom`](Step011_conj_coeff_hom.lean) |  | `conjCoeffHom`, `conjMap` | 68 |
| [`Step012_inner_conj_trivial_hyp`](Step012_inner_conj_trivial_hyp.lean) |  | `InnerConjTrivial`, `innerConjTrivial_iff`, `innerConjTrivial_of_subsingleton` | 68 |
| [`Step013_inner_conj_trivial_in`](Step013_inner_conj_trivial_in.lean) |  | `innerConjTrivialIn`, `innerConjTrivialIn_iff`, `innerConjTrivialIn_of_subsingleton`, `innerConjTrivialIn_of_forall` | 76 |
| [`Step014_conj_action_foundations`](Step014_conj_action_foundations.lean) |  | `conjCoeffHom_apply`, `conjSubtypeHom_one`, `conjSubtypeHom_mul`, `conjMap_comp` | 67 |
| [`Step015_rep_quotient_structure`](Step015_rep_quotient_structure.lean) | `GS2017/line:9497` | `conjCoeffHom_comp_toLinearMap`, `conjMap_mul`, `conjMap_one`, `conjEndHom` (+6 more) | 174 |
| [`Step016_delta_zero_naturality`](Step016_delta_zero_naturality.lean) | `GS2017/line:3585` | `dimShiftSES_S`, `dimShiftSES_S_eq`, `cochainSES_S`, `cochainSES_S_eq` (+5 more) | 164 |
| [`Step017_h0_conj_compatibility`](Step017_h0_conj_compatibility.lean) | `GS2017/line:3580` | `cochainsMap_apply`, `H0Iso_inv_eq_pi`, `iCocycles_cocyclesMap`, `iCocycles_cocyclesIso₀_inv` (+1 more) | 136 |
| [`Step018_delta_two_conditional`](Step018_delta_two_conditional.lean) | `GS2017/line:9498` | `quotientToInvariants_ρ_mk`, `deltaZeroBar`, `deltaTwo`, `deltaTwo_eq` (+2 more) | 143 |
| [`Step019_prism_identity_n1`](Step019_prism_identity_n1.lean) |  | `conj_one_cochain`, `conj_one_cochain_sub` | 102 |
| [`Step020_conj_one_cocycle`](Step020_conj_one_cocycle.lean) |  | `conj_ρ_comm`, `conj_isCocycle`, `conjCocycle`, `conjCocycle_sub_mem` (+1 more) | 117 |
| [`Step021_n1_reduction`](Step021_n1_reduction.lean) |  | `iCycles_cyclesMap`, `conjMap_one_eq_one_of`, `innerConjTrivialIn_one_of` | 105 |
| [`Step022_coboundary_explicit_fin`](Step022_coboundary_explicit_fin.lean) |  | `d_zero_one_apply`, `d_one_two_apply` | 78 |
| [`Step023_compressed_cocycle`](Step023_compressed_cocycle.lean) |  | `compressed_mem_cocycles` | 92 |
| [`Step024_prism_identity_on_cycles`](Step024_prism_identity_on_cycles.lean) |  | `cochainsMap_one_sub_apply` | 90 |
| [`Step025_inner_conj_trivial_in_discharged`](Step025_inner_conj_trivial_in_discharged.lean) |  | `cyclesMap_one_sub_eq_toCycles`, `cyclesMap_one_comp_homologyπ`, `innerConjTrivialIn_one`, `deltaTwoFree` (+1 more) | 156 |
| [`Step026_dimension_shift_from_long_exact`](Step026_dimension_shift_from_long_exact.lean) |  | `delta_injective_of_subsingleton`, `delta_surjective_of_subsingleton`, `delta_bijective_of_subsingleton`, `deltaAddEquiv_of_subsingleton` (+1 more) | 154 |
| [`Step027_coinduced_ses_h1_h2`](Step027_coinduced_ses_h1_h2.lean) |  | `coindRange`, `coindRange_stable`, `coindCoker`, `coindCokerAction` (+4 more) | 132 |
| [`Step028_inflation_h1_iso`](Step028_inflation_h1_iso.lean) |  | `explicitInfl1_surjective_of_subsingleton`, `explicitInfl1_bijective_of_subsingleton`, `explicitInfl1AddEquiv_of_subsingleton`, `h1_inflation_addEquiv_of_subsingleton` (+2 more) | 155 |
| [`Step029_conj_action_on_hn`](Step029_conj_action_on_hn.lean) |  | `cohomologyConjAction`, `cohomologyConjAction_of_mem` | 101 |
| [`Step030_conj_action_descends`](Step030_conj_action_descends.lean) |  | `conjEndQuotient`, `quotientConjAction` | 87 |
| [`Step031_quotient_action_explicit_model`](Step031_quotient_action_explicit_model.lean) |  | `h1ContEquivH`, `quotientConjActionH1` | 91 |
| [`Step032_delta_zero_explicit_model`](Step032_delta_zero_explicit_model.lean) |  | `residueCoeff` | 70 |
| [`Step033_subgroup_acyclicity_gap`](Step033_subgroup_acyclicity_gap.lean) |  | `subsingleton_of_exact_delta`, `subsingleton_of_exact_delta'` | 93 |
| [`Step034_hcd_empty_hypothesis`](Step034_hcd_empty_hypothesis.lean) |  | `isIso_HInfRes_dimensionShift_zero_of_h2`, `inflationIso_dimensionShiftUp_zero`, `deltaTwo_firstHalf'_of_h2` | 89 |
| [`Step035_delta_two_hypotheses_cleared`](Step035_delta_two_hypotheses_cleared.lean) |  | `isZero_h2_of_hcd`, `deltaTwo_minimal`, `deltaTwo_minimal_eq`, `deltaTwo_minimal_type_lock` (+2 more) | 145 |
