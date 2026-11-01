# `L20261018/Ch2/Hensel/Valuation` — sec. 2.4 · valuations, integrality, the uniformizer, Hensel

40 modules.  Part of the development's [index](../../../README.md); see also [`DECLARATIONS.md`](../../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../../RENAME-MAP.tsv).

Source items formalised here: `prop:prelim-kummer-valuation`; 5 line anchors.

| module | source item | declarations | lines |
|---|---|---|---|
| [`Step001_residue_valuation_without_completeness`](Step001_residue_valuation_without_completeness.lean) | `line:1608`, `line:1636`, `line:1648`, `prop:prelim-kummer-valuation` | `valOfUnitOf`, `valOfUnitOf_mul`, `valOfUnitOf_one`, `valOfUnitOf_eq_of_kummerClass_eq` (+9 more) | 264 |
| [`Step002_principal_units_without_completeness`](Step002_principal_units_without_completeness.lean) | `line:1017`, `line:1622` | `principalUnit_pow_surjective_of_hensel`, `sub_one_mem_maximalIdeal_of_residue_eq_one`, `unit_pow_of_residue_pow_of_hensel`, `residuePhi_injective_iff_kummer` | 216 |
| [`Step003_r1_norm_form`](Step003_r1_norm_form.lean) |  | `cup_eq_zero_iff_redequiv`, `cup_eq_zero_iff_mem_normGroup_of_bridge`, `residuePhi_injective_iff_norm_of_bridge` | 123 |
| [`Step004_adjoin_root_degree_p`](Step004_adjoin_root_degree_p.lean) |  | `pow_ne_uniformizer_unit`, `pow_ne_uniformizer`, `irreducible_X_pow_sub_C_uniformizer`, `finrank_eq_prime_of_root_uniformizer` | 101 |
| [`Step005_eisenstein_uniformizer`](Step005_eisenstein_uniformizer.lean) |  | `ValFiltrationCompat`, `uniformizer_mem_maximalIdeal`, `uniformizer_notMem_maximalIdeal_sq`, `isEisensteinAt_uniformizer` | 107 |
| [`Step006_residue_map_subring`](Step006_residue_map_subring.lean) |  | `residueAtRoot`, `residueAtRoot_root`, `residueAtRoot_C`, `residueAtRoot_surjective` | 85 |
| [`Step007_integer_clear_denominators`](Step007_integer_clear_denominators.lean) |  | `ValIntegralityCompat`, `exists_uniformizer_pow_mul_mem_integer` | 76 |
| [`Step008_adjoin_root_model`](Step008_adjoin_root_model.lean) |  | `norm_root_uniformizer_adjoinRoot`, `finrank_adjoinRoot_uniformizer` | 61 |
| [`Step009_norm_residue_basic`](Step009_norm_residue_basic.lean) |  | `norm_algebraMap_adjoinRoot` | 48 |
| [`Step010_power_basis_s`](Step010_power_basis_s.lean) |  | `root_pow_eq_of`, `root_pow_mul`, `powerBasis_root_gen` | 75 |
| [`Step011_uniformizer_clear_denominators`](Step011_uniformizer_clear_denominators.lean) |  | `uniformizer_mem_integer`, `uniformizer_pow_mul_mem_integer_mono` | 58 |
| [`Step012_coordinate_decomposition`](Step012_coordinate_decomposition.lean) |  | `exists_coeff_adjoinRoot` | 84 |
| [`Step013_normalization_integral`](Step013_normalization_integral.lean) |  | `exists_pow_root_mul_coeff_mem` | 72 |
| [`Step014_reduced_power_formula`](Step014_reduced_power_formula.lean) |  | `root_pow_eq`, `root_pow_eq_of_lt` | 58 |
| [`Step015_norm_s_eq_zero`](Step015_norm_s_eq_zero.lean) |  | `nontrivial_adjoinRoot_X_pow`, `norm_root_eq_zero_adjoinRoot` | 55 |
| [`Step016_explicit_basis_powers`](Step016_explicit_basis_powers.lean) |  | `basis_root_pow` | 52 |
| [`Step017_repr_computations`](Step017_repr_computations.lean) |  | `basis_repr_root_pow`, `basis_repr_smul_root_pow` | 59 |
| [`Step018_left_mul_matrix_entrywise`](Step018_left_mul_matrix_entrywise.lean) |  | `sumCoeff`, `sumCoeffShift`, `sumCoeff_mul_basis`, `repr_smul_coeff` | 69 |
| [`Step019_left_mul_matrix_sum`](Step019_left_mul_matrix_sum.lean) |  | `leftMulMatrix_apply_eq` | 43 |
| [`Step020_left_mul_matrix_shape`](Step020_left_mul_matrix_shape.lean) |  | `leftMulMatrix_entry_of_le`, `leftMulMatrix_entry_of_lt` | 118 |
| [`Step021_val_compat_elementwise`](Step021_val_compat_elementwise.lean) |  | `ValCompat`, `ValCompat`, `valCompat_uniformizer_mem_integer`, `valCompat_uniformizer_mem_maximalIdeal` (+2 more) | 108 |
| [`Step022_norm_congruence`](Step022_norm_congruence.lean) |  | `coeffMatrix`, `residueCoeffMatrix`, `residue_uniformizer_image_eq_zero`, `residue_det_coeffMatrix` (+3 more) | 147 |
| [`Step023_maximal_ideal_eq_pi`](Step023_maximal_ideal_eq_pi.lean) |  | `exists_mul_uniformizer_of_mem_maximalIdeal` | 60 |
| [`Step024_normalization_sum_coeff`](Step024_normalization_sum_coeff.lean) |  | `sum_range_eq_sumCoeff`, `exists_pow_root_mul_coeff_mem_sumCoeff` | 78 |
| [`Step025_norm_smul_uniformizer`](Step025_norm_smul_uniformizer.lean) |  | `monic_X_pow_sub_C_uniformizer`, `free_adjoinRoot_uniformizer_f`, `finite_adjoinRoot_uniformizer_f`, `nontrivial_adjoinRoot_uniformizer_f` (+1 more) | 73 |
| [`Step026_coefficient_in_maximal_ideal`](Step026_coefficient_in_maximal_ideal.lean) |  | `coeff_zero_mem_maximalIdeal` | 77 |
| [`Step027_leading_term_split`](Step027_leading_term_split.lean) |  | `sum_range_split`, `sum_range_split_adjoinRoot` | 69 |
| [`Step028_reindex_eliminate_s`](Step028_reindex_eliminate_s.lean) |  | `sum_range_split_last`, `root_mul_eq_zero_iff`, `root_mul_left_cancel`, `sumCoeff_eq_root_mul` | 167 |
| [`Step029_integrality_criterion`](Step029_integrality_criterion.lean) |  | `exists_coeff_of_norm_mem_integer` | 127 |
| [`Step030_val_compat_order_function`](Step030_val_compat_order_function.lean) |  | `addVal_ne_top_iff`, `znat`, `znat_zero`, `znat_one` (+3 more) | 77 |
| [`Step031_val_compat_well_defined`](Step031_val_compat_well_defined.lean) |  | `exists_num_den`, `znat_sub_eq_of_mul_eq` | 82 |
| [`Step032_val_compat_multiplicative`](Step032_val_compat_multiplicative.lean) |  | `num_ne_zero_of_mul_eq`, `exists_num_den'`, `numDen`, `numDen_spec` (+5 more) | 108 |
| [`Step033_val_compat_exists`](Step033_val_compat_exists.lean) |  | `toAdd_vCompatHom`, `zval_eq_znat`, `mem_integer_vCompat`, `mem_maximalIdeal_vCompat` (+2 more) | 111 |
| [`Step034_discharge_pi_hypotheses`](Step034_discharge_pi_hypotheses.lean) |  | `zval_pow`, `zval_uniformizer`, `not_pow_of_zval_eq_one` | 85 |
| [`Step035_uniformizer_constructed`](Step035_uniformizer_constructed.lean) |  | `exists_uniformizer_not_pow` | 59 |
| [`Step036_exists_unit_rep_val_lin`](Step036_exists_unit_rep_val_lin.lean) |  | `zval_pow`, `exists_unit_rep_F` | 82 |
| [`Step037_nu_pth_root_zero`](Step037_nu_pth_root_zero.lean) |  | `eq_one_of_pow_eq_one`, `unitVal_root_eq_one`, `FbarValuationHyp₂` | 111 |
| [`Step038_valuation_extension_bridge`](Step038_valuation_extension_bridge.lean) |  | `unitValOf`, `unitValOf_apply`, `unitValOf_eq_one_iff` | 85 |
| [`Step039_integral_closure_stable`](Step039_integral_closure_stable.lean) |  | `isIntegral_algEquiv`, `mem_integralClosure_algEquiv`, `FbarValuationHyp₃` | 96 |
| [`Step040_integral_closure_value_preserving`](Step040_integral_closure_value_preserving.lean) |  | `valSubring_stable`, `inertiaSet`, `one_mem_inertiaSet` | 98 |
