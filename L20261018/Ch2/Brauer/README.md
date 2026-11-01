# `L20261018/Ch2/Brauer` — sec. 2.1 · central simple algebras, Brauer group, crossed and symbol algebras

35 modules.  Part of the development's [index](../../README.md); see also [`DECLARATIONS.md`](../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../RENAME-MAP.tsv).

| module | paper | declarations | lines |
|---|---|---|---|
| [`Step001_index_le_degree`](Step001_index_le_degree.lean) |  | `instIsInvariant`, `deg_crossedProduct`, `index_crossedProduct_le`, `index_crossedProduct_le_of_finrank` | 66 |
| [`Step002_reduced_norm_maximal_subfield`](Step002_reduced_norm_maximal_subfield.lean) |  | `alone.`, `mulRight`, `mulRight_inc`, `toMatrix_mulRight_inc` (+5 more) | 110 |
| [`Step003_reduced_norm_any_crossed_product`](Step003_reduced_norm_any_crossed_product.lean) |  | `nrdOfIso`, `nrdOfIso_independent`, `exists_nrdOfIso_eq_norm`, `norm_image_le_nrdOfIso_image` | 91 |
| [`Step004_degenerate_crossed_product_trivial`](Step004_degenerate_crossed_product_trivial.lean) |  | `crossedProductClass_eq_one_of_subsingleton_aut`, `subsingleton_algEquiv_bot`, `crossedProductClass_eq_one_of_eq_bot`, `crossedProductClass_rootSet_eq_one` | 109 |
| [`Step005_symbol_algebra_normal_form`](Step005_symbol_algebra_normal_form.lean) |  | `Fr`, `gen`, `rel`, `SymbolAlg` (+26 more) | 479 |
| [`Step006_symbol_algebra_degenerate`](Step006_symbol_algebra_degenerate.lean) |  | `Xmat`, `Ymat`, `of_apply`, `Ymat_apply_of_ne_zero` (+28 more) | 539 |
| [`Step007_brauer_interfaces`](Step007_brauer_interfaces.lean) |  | `isCentral_of_algEquiv`, `isSimpleRing_of_algEquiv`, `mk_matrix_eq_one` | 79 |
| [`Step008_matrix_elimination_degree`](Step008_matrix_elimination_degree.lean) |  | `mk_matrix_eq`, `nonempty_algEquiv_of_matrix_algEquiv`, `matrixFinOneAlgEquiv`, `eq_one_of_sq_mul_finrank_eq` (+2 more) | 183 |
| [`Step009_h_nrd_from_field_norm_algebra`](Step009_h_nrd_from_field_norm_algebra.lean) |  | `exists_nrdOfIso_eq_norm_of_mk_eq`, `norm_range_subset_nrd_range_of_mk_eq` | 63 |
| [`Step010_index_brauer_invariant`](Step010_index_brauer_invariant.lean) |  | `index_matrix`, `index_eq_of_algEquiv_matrix`, `index_eq_of_mk_eq` | 75 |
| [`Step011_kummer_extension_generator`](Step011_kummer_extension_generator.lean) |  | `irreducible`, `L`, `α`, `α_pow` (+6 more) | 86 |
| [`Step012_carry_cocycle_arithmetic`](Step012_carry_cocycle_arithmetic.lean) |  | `carry_left`, `carry_right`, `carry_assoc` | 46 |
| [`Step013_carry_cocycle_index`](Step013_carry_cocycle_index.lean) |  | `bL`, `smul_bL`, `expEquiv`, `carryExp` (+3 more) | 74 |
| [`Step014_carry_cocycle_two_cocycle`](Step014_carry_cocycle_two_cocycle.lean) |  | `smul_pow_bL`, `carryFun`, `carryCocycle` | 76 |
| [`Step015_crossed_product_generators`](Step015_crossed_product_generators.lean) |  | `X`, `X_pow`, `Y`, `Y_mul_X` (+1 more) | 53 |
| [`Step016_power_formula_telescope`](Step016_power_formula_telescope.lean) |  | `basis_one_eq_one`, `basis_pow` | 45 |
| [`Step017_carry_exp_gen_pow`](Step017_carry_exp_gen_pow.lean) |  | `gen`, `carryExp_gen`, `carryExp_gen_pow`, `carryExp_gen_pow_of_lt` | 63 |
| [`Step018_product_cocycle_sum`](Step018_product_cocycle_sum.lean) |  | `ofAdd_one_pow`, `sum_div_range`, `gen_pow_eq_one` | 61 |
| [`Step019_y_pow_eq_b`](Step019_y_pow_eq_b.lean) |  | `carryFun_one_one`, `prod_carryFun`, `Y_pow` | 72 |
| [`Step020_adjoin_surjectivity_blocks`](Step020_adjoin_surjectivity_blocks.lean) |  | `adjoin_alpha`, `inc_mem_adjoin` | 59 |
| [`Step021_adjoin_top`](Step021_adjoin_top.lean) |  | `cYC`, `genSet`, `inc_mem_adjoin_gen`, `basis_mem_adjoin_gen` | 83 |
| [`Step022_adjoin_top_assembly`](Step022_adjoin_top_assembly.lean) |  | `ofAdd_one_pow_eq`, `gen_pow_carryExp`, `adjoin_genSet_eq_top` | 69 |
| [`Step023_symbol_alg_equiv_crossed_product`](Step023_symbol_alg_equiv_crossed_product.lean) |  | `gen_alpha`, `nonempty_algEquiv_crossedProduct` | 94 |
| [`Step024_index_le_degree_symbol`](Step024_index_le_degree_symbol.lean) |  | `index_symbolAlg_le` | 60 |
| [`Step025_crossed_product_class_inflation`](Step025_crossed_product_class_inflation.lean) |  | `inflateZ2_eq_relBrCocycle`, `brauerGroupEquivBr_crossedProductClass` | 84 |
| [`Step026_carry_cocycle_class_cyclic`](Step026_carry_cocycle_class_cyclic.lean) |  | `mem_zpowers_gen`, `orderOf_gen`, `cohomologyClass_carryCocycle` | 87 |
| [`Step027_adjoin_root_to_intermediate_field`](Step027_adjoin_root_to_intermediate_field.lean) |  | `emb`, `e`, `coe_e`, `e_autCongr_apply` (+23 more) | 327 |
| [`Step028_h2_to_brauer_carrier`](Step028_h2_to_brauer_carrier.lean) |  | `cohomEquiv_eq_coeffMap`, `cE`, `cE_cup`, `gE` (+11 more) | 212 |
| [`Step029_index_function_h2`](Step029_index_function_h2.lean) |  | `brauerOfH2`, `DivisionRep`, `nonempty_divisionRep`, `divisionRep` (+4 more) | 126 |
| [`Step030_index_le_degree_instances`](Step030_index_le_degree_instances.lean) |  | `fact_irreducible_of_notMem_pow`, `isCentral_symbolAlg`, `isSimpleRing_symbolAlg`, `finiteDimensional_symbolAlg` (+1 more) | 119 |
| [`Step031_brauer_of_h2_smul`](Step031_brauer_of_h2_smul.lean) |  | `cEL`, `cEL_toAddEquiv`, `redLin`, `redLin1` (+6 more) | 122 |
| [`Step032_brauer_image_p_torsion`](Step032_brauer_image_p_torsion.lean) |  | `p_smul_brOfH2` | 35 |
| [`Step033_index_unit_scalar_invariant`](Step033_index_unit_scalar_invariant.lean) |  | `index_dvd_finrank_of_isSplittingField_division`, `index_dvd_finrank_of_isSplittingField`, `isSplittingField_of_mk_eq`, `index_eq_of_mk_eq_pow` | 192 |
| [`Step034_index_zeta_independent`](Step034_index_zeta_independent.lean) |  | `brauerOfH2_eq_pow`, `brauerOfH2_pow_prime`, `indOfH2_independent` | 95 |
| [`Step035_symbol_algebra_tensor_class`](Step035_symbol_algebra_tensor_class.lean) |  | `brauerClass_tensorSymbol` | 42 |
