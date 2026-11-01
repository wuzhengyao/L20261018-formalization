# `L20261018/Witness` — concrete witnesses (Q_7, F_7((t)), ...) for the nonemptiness obligations

40 modules.  Part of the development's [index](../README.md); see also [`DECLARATIONS.md`](../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../RENAME-MAP.tsv).

Paper items formalised here: `prop:prelim-residue`; 3 raw line anchors.

| module | paper | declarations | lines |
|---|---|---|---|
| [`Step001_bi_kummer_data_nonempty`](Step001_bi_kummer_data_nonempty.lean) |  | `toyCup`, `toyBiKummer`, `biKummerData_nonempty`, `HasNonzeroKummerCup` (+1 more) | 102 |
| [`Step002_nonzero_local_symbol_reduction`](Step002_nonzero_local_symbol_reduction.lean) |  | `cup_ne_zero_of_localSymbol_ne_zero`, `cup_kummerClass_ne_zero_of_localSymbol_ne_zero`, `cupFp_ne_zero_of_localSymbol_ne_zero` | 79 |
| [`Step003_nondegenerate_nonzero_cup`](Step003_nondegenerate_nonzero_cup.lean) |  | `exists_localSymbol_ne_zero_of_notMem_powerSubgroup`, `exists_cupFp_ne_zero_of_notMem_powerSubgroup`, `toAdd_pow`, `notMem_powerSubgroup_of_isUniformizer` (+2 more) | 124 |
| [`Step004_val_filtration_compat_empty`](Step004_val_filtration_compat_empty.lean) |  | `valFiltrationCompat_false` | 51 |
| [`Step005_val_compat_qp`](Step005_val_compat_qp.lean) |  | `padicUnitV`, `padicUnitV_uniformizer` | 54 |
| [`Step006_val_compat_complete_field`](Step006_val_compat_complete_field.lean) |  | `valCompat_mem_integer_of_localField`, `valCompat_mem_maximalIdeal_of_localField`, `valCompat_of_localField` | 83 |
| [`Step007_l1_witness_q7`](Step007_l1_witness_q7.lean) |  | `seven_mem_maximalIdeal`, `five_isUnit`, `exists_root_X_sq_add_X_add_one`, `exists_primitiveRoot_three_Q7` (+6 more) | 159 |
| [`Step008_tame_residue_facts_q7`](Step008_tame_residue_facts_q7.lean) | `prop:prelim-residue` | `HenselResidueData.tame_pi_u_of_skew`, `HenselResidueDataCore`, `tame_pi_u`, `toHenselResidueData` (+2 more) | 180 |
| [`Step009_q7_non_cube_unit`](Step009_q7_non_cube_unit.lean) |  | `not_exists_cube_two_Q7`, `kummerClass_two_ne_zero_Q7` | 82 |
| [`Step010_q7_nonzero_cup`](Step010_q7_nonzero_cup.lean) |  | `znat_eq_zero_of_isUnit`, `zval_unit_eq_zero`, `two_isUnit_O`, `kc_two_mem_ker_Q7` | 94 |
| [`Step011_q7_v_finite_dimensional`](Step011_q7_v_finite_dimensional.lean) |  | `finite_powerClassQuotient_Q7`, `finite_H1_kummerCoeff_Q7`, `finite_H1_zmod_Q7`, `finite_galoBaseV_Q7` (+1 more) | 84 |
| [`Step012_q7_exists_nonzero_cup`](Step012_q7_exists_nonzero_cup.lean) |  | `twoUnit`, `kc_two_ne_zero_muNRep_Q7`, `exists_galoCup_ne_zero_Q7` | 117 |
| [`Step013_q7_ramified_vanishing_witness`](Step013_q7_ramified_vanishing_witness.lean) |  | `q7Pi`, `q7Pi_zval`, `q7Pi_notpow`, `q7Pi_hπ` (+11 more) | 155 |
| [`Step014_q7_val_compat`](Step014_q7_val_compat.lean) |  | `valCompat_normalizedValuation_Q7`, `normalizedValuation_seven_Q7` | 84 |
| [`Step015_q7_hk1`](Step015_q7_hk1.lean) |  | `seven_not_cube_Q7`, `seven_irred_Q7`, `finrank_ker_valLinOf_Q7` | 89 |
| [`Step016_d_witness_finite_residue`](Step016_d_witness_finite_residue.lean) | `line:1023` | `exists_residueMap_of_finite` | 60 |
| [`Step017_laurent_series_valuative_rel`](Step017_laurent_series_valuative_rel.lean) |  | `instValuativeRel` | 33 |
| [`Step018_f7_valuative_rel`](Step018_f7_valuative_rel.lean) |  | — | 31 |
| [`Step019_f7_two_order_three`](Step019_f7_two_order_three.lean) |  | `two_pow_three_zmod7`, `two_ne_one_zmod7`, `two_sq_ne_one_zmod7` | 28 |
| [`Step020_f7_mu3_primitive_root`](Step020_f7_mu3_primitive_root.lean) |  | `isPrimitiveRoot_two_zmod7`, `hasEnoughRootsOfUnity_zmod7_three` | 41 |
| [`Step021_f7t_mu3_transport`](Step021_f7t_mu3_transport.lean) |  | `C_injective_zmod7`, `isPrimitiveRoot_C_two`, `hasEnoughRootsOfUnity_laurentSeries_zmod7_three`, `three_ne_zero_laurentSeries` (+1 more) | 59 |
| [`Step022_f7t_hensel_finite_residue`](Step022_f7t_hensel_finite_residue.lean) |  | `mem_O_iff`, `mem_O_iff_exists_powerSeries`, `powerSeriesToO`, `powerSeriesToO_coe` (+9 more) | 167 |
| [`Step023_f7t_dvr_val_compat`](Step023_f7t_dvr_val_compat.lean) |  | `isPrincipalIdealRing_O`, `isDiscreteValuationRing_O`, `ofPowerSeries_X_ne_zero`, `pi` (+10 more) | 184 |
| [`Step024_f7t_not_cube`](Step024_f7t_not_cube.lean) |  | `ofPowerSeries_C_eq`, `two_mem_O`, `twoO`, `rho` (+5 more) | 109 |
| [`Step025_f7t_hne_hval`](Step025_f7t_hne_hval.lean) | `line:1608` | `zetaF`, `zetaF_spec`, `two_ne_zero_laurentSeries`, `twoUnitF` (+12 more) | 198 |
| [`Step026_f7t_principal_units_cube`](Step026_f7t_principal_units_cube.lean) |  | `mF`, `henselPoly`, `monic_henselPoly`, `eval_zero_henselPoly` (+2 more) | 108 |
| [`Step027_f7t_unit_cube_from_residue`](Step027_f7t_unit_cube_from_residue.lean) |  | `mF'`, `unitsToF`, `unitsResidue`, `isCube_of_residue_cube` (+1 more) | 106 |
| [`Step028_f7t_same_cube_class`](Step028_f7t_same_cube_class.lean) |  | `mF''`, `finite_residueUnits`, `unitsResidue_surjective`, `powerClass_eq_of_unitsResidue_eq` | 88 |
| [`Step029_f7t_zval_powers`](Step029_f7t_zval_powers.lean) |  | `zval_pi_pow`, `zval_inv`, `zval_pi_zpow`, `exists_unit_of_zval_eq_zero` | 81 |
| [`Step030_f7t_pi_power_decomposition`](Step030_f7t_pi_power_decomposition.lean) |  | `pi_decomp` | 73 |
| [`Step031_f7t_finite_cube_classes`](Step031_f7t_finite_cube_classes.lean) |  | `mk_eq_of_eq_cube_mul`, `sigma`, `sigma_surjective`, `finite_powerClassQuotient` | 85 |
| [`Step032_f7t_v_finite_dimensional`](Step032_f7t_v_finite_dimensional.lean) | `line:1608` | `finite_H1_kummerCoeff_F`, `finite_H1_zmod_F`, `finite_galoBaseV_F`, `finiteDimensional_galoBaseV_F` (+1 more) | 87 |
| [`Step033_f7t_mun_rep_cup_nonzero`](Step033_f7t_mun_rep_cup_nonzero.lean) |  | `piT`, `val_kc_pi`, `hcupT_pi` | 105 |
| [`Step034_f7t_galo_cup_nonzero`](Step034_f7t_galo_cup_nonzero.lean) |  | `hcupG_F`, `hne43_F`, `hval43_F` | 97 |
| [`Step035_f7t_thm_ramified_witness`](Step035_f7t_thm_ramified_witness.lean) |  | `finiteIndex_cubes_F` | 64 |
| [`Step036_f7t_thm_ramified_witness_paper_objects`](Step036_f7t_thm_ramified_witness_paper_objects.lean) | `line:1636` | `inst_finiteRelIndex_top_F`, `Efield_top_eq_F`, `inst_finiteDimensional_Efield_top_F`, `inst_isGalois_Efield_top_F` (+3 more) | 120 |
| [`Step037_f7t_hval_and_corollary`](Step037_f7t_hval_and_corollary.lean) |  | `hval44_F`, `corollary_4_4_F_of_hK1` | 87 |
| [`Step038_val_compat_nonempty`](Step038_val_compat_nonempty.lean) |  | `valCompat_normalizedValuation`, `valCompat_witness_padic`, `nonempty_valCompat` | 120 |
| [`Step039_tsen_hyp_nonempty`](Step039_tsen_hyp_nonempty.lean) |  | `tsenHyp_of_subsingleton_galois`, `tsenHyp_of_isSepClosed`, `subsingleton_H2_of_isSepClosed`, `subsingleton_H2_complex` | 106 |
| [`Step040_tame_symbol_hyp_witness`](Step040_tame_symbol_hyp_witness.lean) |  | `ch4TameSymbolHyp_viaResidue`, `disjoint_viaResidue` | 140 |
