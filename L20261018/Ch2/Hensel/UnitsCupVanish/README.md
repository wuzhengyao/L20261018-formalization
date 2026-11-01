# `L20261018/Ch2/Hensel/UnitsCupVanish` — sec. 2.4 · the named hypothesis `UnitsCupVanish` and its discharge

41 modules.  Part of the development's [index](../../../README.md); see also [`DECLARATIONS.md`](../../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../../RENAME-MAP.tsv).

| module | source item | declarations | lines |
|---|---|---|---|
| [`Step001_units_cup_vanish_complete`](Step001_units_cup_vanish_complete.lean) |  | `kummerClass_isUnit_proof_irrel`, `unitsCupVanish_complete`, `unitsCupVanish_of_residueSpan_eq_bot` | 132 |
| [`Step002_units_cup_vanish_reduction`](Step002_units_cup_vanish_reduction.lean) |  | `normGroup`, `pow_mem_normGroup`, `PowClassGen`, `mem_normGroup_of_powClassGen` (+1 more) | 119 |
| [`Step003_norm_group_adjoin_root`](Step003_norm_group_adjoin_root.lean) |  | `norm_root_X_pow_sub_C`, `norm_root_eq`, `norm_root_eq'`, `root_ne_zero_of_ne_zero` (+3 more) | 147 |
| [`Step004_capelli_criterion`](Step004_capelli_criterion.lean) |  | `X_pow_sub_C_irreducible_iff_of_odd`, `capelli_irreducible_iff`, `capelli_irreducible_of_not_pow`, `not_pow_of_irreducible` (+1 more) | 99 |
| [`Step005_units_cup_vanish_final_form`](Step005_units_cup_vanish_final_form.lean) |  | `kummerClass_pow_eq_zero`, `cup_unit_eq_zero_of_pow`, `cup_unit_eq_zero_of_powClassGen`, `unitsCupVanish_of_powClassGen` | 126 |
| [`Step006_principal_units_pow_hensel`](Step006_principal_units_pow_hensel.lean) |  | `pow_surj_on_one_add_maximalIdeal`, `pow_surj_on_one_add_maximalIdeal_ofF` | 101 |
| [`Step007_units_surject_residue`](Step007_units_surject_residue.lean) |  | `exists_unit_residue_eq`, `one_add_subset_pow` | 97 |
| [`Step008_residue_field_units_cyclic`](Step008_residue_field_units_cyclic.lean) |  | `isCyclic_units_of_finite`, `natCard_units_of_finite` | 66 |
| [`Step009_units_group_lemma`](Step009_units_group_lemma.lean) |  | `orderOf_eq_prime_of_pow_eq_one`, `zpowers_eq_top_of_pow_eq_one` | 80 |
| [`Step010_bezout_arithmetic_core`](Step010_bezout_arithmetic_core.lean) |  | `exists_dvd_sub_mul`, `exists_pow_mul_pow_of_isCyclic` | 96 |
| [`Step011_units_transport_steps`](Step011_units_transport_steps.lean) |  | `exists_unitOf_of_val_eq_one`, `exists_pow_of_residue_eq_one` | 86 |
| [`Step012_units_cup_vanish_unconditional`](Step012_units_cup_vanish_unconditional.lean) |  | `rho`, `coe_rho`, `exists_unit_rho_eq`, `exists_pow_of_rho_eq_one` (+4 more) | 140 |
| [`Step013_exists_d_and_ch4_unconditional`](Step013_exists_d_and_ch4_unconditional.lean) |  | `exists_henselResidueData`, `orth_eq_bot_of_discrete_valuation''`, `thm_ramified_1_of_discrete_valuation''`, `corollary_4_4_of_discrete_valuation''` | 143 |
| [`Step014_units_cup_vanish_true_statement`](Step014_units_cup_vanish_true_statement.lean) |  | `coe_rho'`, `hcyc_of_divisible`, `hcyc_of_finite`, `exists_unit_rho_eq'` (+10 more) | 284 |
| [`Step015_b_reduced_to_disjoint`](Step015_b_reduced_to_disjoint.lean) |  | `exists_residueMap_of_disjoint`, `tameResidueFacts_of_disjoint`, `orth_eq_bot_of_disjoint`, `thm_ramified_1_of_disjoint` | 159 |
| [`Step016_b_pinned_to_equivalence`](Step016_b_pinned_to_equivalence.lean) |  | `disjoint_of_exists_residueMap`, `disjoint_of_residueSpan_eq_bot`, `disjoint_iff_exists_residueMap` | 155 |
| [`Step017_one_dimensionality_is_the_engine`](Step017_one_dimensionality_is_the_engine.lean) |  | `residueSpan_eq_bot_of_dependent`, `disjoint_of_dependent`, `exists_residueMap_of_dependent` | 124 |
| [`Step018_b_logical_tension`](Step018_b_logical_tension.lean) |  | `disjoint_iff_forall`, `phi_apply_eq_zero_of_residueSpan_eq_top`, `residueSpan_ne_top_of_exists_phi_ne_zero` | 101 |
| [`Step019_b_tension_resolved`](Step019_b_tension_resolved.lean) |  | `valOfUnitOf_eq_zero_of_val_eq_one`, `kummerClass_mem_ker_of_val_eq_one`, `ker_valLin_contains_zeta` | 89 |
| [`Step020_tg_definition`](Step020_tg_definition.lean) |  | `TgSection`, `sσ`, `hpart`, `s_mul_hpart` (+4 more) | 158 |
| [`Step021_tg_compatibility`](Step021_tg_compatibility.lean) |  | `conjH`, `x_one_eq_zero`, `hpart_section`, `hpart_conj` (+4 more) | 172 |
| [`Step022_nsw_y_exists`](Step022_nsw_y_exists.lean) |  | `ConjInvariant`, `conjH_one`, `exists_tgCompat_normalized`, `exists_tgLift` | 147 |
| [`Step023_partial_y_coset_dependence`](Step023_partial_y_coset_dependence.lean) |  | `d1_tgLift_snd`, `d1_tgLift_h_mem`, `d1_tgLift_fst` | 97 |
| [`Step024_partial_y_ah_valued`](Step024_partial_y_ah_valued.lean) |  | `d1_tgLift_mem_fixed`, `exists_tg_partial` | 107 |
| [`Step025_descent_lemma_well_defined`](Step025_descent_lemma_well_defined.lean) |  | `d1_z_h_zero`, `tgLift_z_right_invariant`, `tgLift_z_mem_fixed` | 96 |
| [`Step026_partial_y_descent`](Step026_partial_y_descent.lean) |  | `d1_tgLift_quot_compat`, `tgCocycle` | 86 |
| [`Step027_tg_additive_component`](Step027_tg_additive_component.lean) |  | `conjInvariant_add`, `tgLift_hii_add`, `tgLift_hiii_add`, `tgCocycle_add` | 106 |
| [`Step028_tg_cochain_internal_check`](Step028_tg_cochain_internal_check.lean) |  | `tgCocycle_sec_indep`, `tgCocycle_cocycle` | 114 |
| [`Step029_first_segment_exactness`](Step029_first_segment_exactness.lean) |  | `tgCocycle_eq_zero_of_cocycle`, `d1_sub_apply`, `tgLift_hright_sub`, `tgLift_hleft_sub` (+1 more) | 92 |
| [`Step030_tg_well_defined_complete`](Step030_tg_well_defined_complete.lean) |  | `tgLift_z_quot_eq`, `coe_quot_smul'`, `coe_quot_smul`, `tgCocycle_sub_eq` | 109 |
| [`Step031_tg_normal_form`](Step031_tg_normal_form.lean) |  | `tgYs`, `tgYs_one`, `tgYs_restrict`, `tgYs_hii` (+4 more) | 100 |
| [`Step032_tg_section_exists`](Step032_tg_section_exists.lean) |  | `tgSectionOf`, `tgSection_nonempty` | 61 |
| [`Step033_inertia_fixed_unit_pth_root`](Step033_inertia_fixed_unit_pth_root.lean) |  | `geomSum_sub_eq'`, `isUnit_of_mul_left'`, `isUnit_sub_one_of_pow_eq_one'`, `eq_one_of_pow_eq_one_of_residueUnits_eq_one` (+2 more) | 274 |
| [`Step034_n4_paper_form`](Step034_n4_paper_form.lean) |  | `val_eq_one_of_inv_mem`, `isUnit_mk_of_inv_mem`, `algebraMap_mem_integralClosure`, `val_algMap_eq_one` (+2 more) | 193 |
| [`Step035_kummer_cocycle_properties`](Step035_kummer_cocycle_properties.lean) |  | `kummerCocycle`, `kummerCocycle_apply`, `kummerCocycle_mul`, `kummerCocycle_pow_eq_one` (+2 more) | 126 |
| [`Step036_integral_closure_ring_map`](Step036_integral_closure_ring_map.lean) |  | `algebraMap_mem_valuationSubring`, `toValuationSubring`, `toValuationSubring_coe`, `residueFieldMap` (+1 more) | 109 |
| [`Step037_cocycle_unit_valued`](Step037_cocycle_unit_valued.lean) |  | `kummerUnit`, `kummerUnit_coe`, `kummerUnit_pow_eq_one`, `kummerUnit_eq_one_of_mem_inertia` | 141 |
| [`Step038_cocycle_constant_on_cosets`](Step038_cocycle_constant_on_cosets.lean) |  | `kummerCocycle_mul_right_mem_inertia`, `kummerCocycle_eq_of_mul_mem_inertia` | 83 |
| [`Step039_cocycle_descends`](Step039_cocycle_descends.lean) |  | `kummerCocycleQuot` | 71 |
| [`Step040_cocycle_on_quotient`](Step040_cocycle_on_quotient.lean) |  | `kummerCocycleQuot_mk`, `kummerCocycleQuot_one`, `kummerCocycleQuot_mul`, `kummerCocycleQuot_mul_quot` (+5 more) | 248 |
| [`Step041_res_inertia_kummer_class_zero`](Step041_res_inertia_kummer_class_zero.lean) |  | `unitBase`, `rootUnit`, `unitBase_coe`, `rootUnit_coe` (+8 more) | 214 |
