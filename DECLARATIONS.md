# Declaration index — every declaration, its module and line

Generated from the sources by `scripts/gen-declarations.py`.  Use this page to locate a result: `Ctrl-F` the declaration name (or a keyword) here, then open the module named in the second column.

**2636 declarations in 576 modules.**

Notes: 38 further declarations are anonymous instances (`instance : Foo`), which have no name to look up and so are only counted; the historical anchored scan of 2026-11-08 indexed 2607 of them, losing the 29 that are preceded by an attribute such as `@[simp]`.

## Where to look

The module names carry the theme; the directory part follows the paper's own structure (`Ch2` = preliminaries, `Ch3`, `Ch4`), with `Infra/` for the general tooling that no single paper statement owns.  The `paper` column of the index gives the `@source` locator attached to the module, when the module carries one (108 modules do).

| directory | modules | declarations | theme |
|---|---|---|---|
| `Ch2/Brauer/` | 35 | 228 | sec. 2.1 -- central simple algebras, Brauer group, crossed and symbol algebras |
| `Ch2/Hensel/Inertia/` | 40 | 277 | sec. 2.4 -- inertia, K_nr, the cohomological dimension of I |
| `Ch2/Hensel/ResidueMap/` | 84 | 362 | sec. 2.4 -- the residue map, its exact sequence, (R1) and (R2) |
| `Ch2/Hensel/TameSymbol/` | 16 | 104 | sec. 2.4 -- the tame symbol and the Merkurjev-Suslin closure |
| `Ch2/Hensel/UnitsCupVanish/` | 41 | 184 | sec. 2.4 -- the named hypothesis `UnitsCupVanish` and its discharge |
| `Ch2/Hensel/Valuation/` | 40 | 129 | sec. 2.4 -- valuations, integrality, the uniformizer, Hensel |
| `Ch2/Kummer/` | 51 | 183 | sec. 2.2 -- Kummer theory, cup products, the cyclic norm criterion |
| `Ch2/Rost/` | 2 | 18 | sec. 2.5 -- Rost invariant, Suslin groups, cohomological dimension |
| `Ch3/BiKummer/` | 17 | 72 | sec. 3.1 -- the bi-Kummer structure, the rank barrier, the norm image |
| `Ch3/NormImage/` | 22 | 89 | sec. 3.2 -- the short exact sequence of the norm image, the dimension formula |
| `Ch4/` | 48 | 216 | sec. 4 -- Hensel valuations and ramification in the first slot |
| `Core/` | 2 | 44 | carriers of the paper's objects; the master abstract statements |
| `Infra/Algebra/` | 3 | 8 | general algebra: linear algebra, group theory, adjoin-root tooling |
| `Infra/Cohomology/` | 10 | 41 | general cohomology infrastructure; no single paper statement owns it |
| `Infra/Cohomology/Boundary/` | 35 | 135 | sec. 2.3 -- the Hochschild-Serre boundary map, assembled |
| `Infra/Cohomology/Coinduced/` | 41 | 164 | sec. 2.3 -- coinduced modules, invariants, GS (6.17) |
| `Infra/Cohomology/Conjugation/` | 14 | 51 | sec. 2.3/2.4 -- conjugation invariance of H^1(I, mu_p) |
| `Infra/Cohomology/ResidueLES/` | 33 | 138 | sec. 2.4 -- the continuous residue long exact sequence |
| `Infra/Galois/` | 2 | 5 | absolute Galois group carriers and subgroup plumbing |
| `Witness/` | 40 | 188 | concrete witnesses (Q_7, F_7((t)), ...) for the nonemptiness obligations |

## Index

| declaration | module | line | paper |
|---|---|---|---|
| `Bex` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 165 | `label:thm:hs-tate-exact-sequences` |
| `Bex_Phi_eq_commonCupMap` | `L20261018.Ch4.Step007_corollary_four_four_no_d` | 122 | `line:1646` |
| `Bex_Phi_theta` | `L20261018.Ch4.Step008_rank_contradiction_single_phi` | 51 | `line:1646` |
| `Bex_Phi_theta_free` | `L20261018.Ch4.Step018_single_carrier_thm_ramified` | 43 | `line:1636; line:1637` |
| `Bex_U_toAddSubgroup` | `L20261018.Ch3.NormImage.Step015_three_six_assembly_u_alignment` | 61 |  |
| `Bex_Uperp_eq_orth` | `L20261018.Ch4.Step003_ramified_vanishing_paper_objects` | 155 | `label:lem:ramified-vanishing; label:prop:prelim-residue` |
| `BiKummerData` | `L20261018.Core.Step001_bi_kummer_data` | 15 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `C_injective_zmod7` | `L20261018.Witness.Step021_f7t_mu3_transport` | 29 |  |
| `Ch4TameSymbolHyp` | `L20261018.Ch2.Hensel.TameSymbol.Step003_ch4_tame_symbol_hyp` | 60 |  |
| `CohomologicalDimensionLE` | `L20261018.Ch2.Hensel.Inertia.Step027_cd_l_inertia_vanishing` | 13 |  |
| `CohomologicalDimensionLE` | `L20261018.Ch2.Rost.Step002_tsen_cd_p_le_one` | 25 |  |
| `CoindSubgroupAcyclic` | `L20261018.Infra.Cohomology.Coinduced.Step001_coind_subgroup_acyclic_hyp` | 73 |  |
| `CoindSubgroupAcyclicOne` | `L20261018.Infra.Cohomology.Coinduced.Step003_coind_subgroup_acyclic_one` | 52 |  |
| `Conj1Trivial` | `L20261018.Infra.Cohomology.Conjugation.Step008_conj1_trivial_hyp` | 71 |  |
| `ConjInvariant` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step022_nsw_y_exists` | 56 |  |
| `D_class_eq_cup_sum` | `L20261018.Ch4.Step025_d_class_eq_cup_sum` | 42 |  |
| `DivisionRep` | `L20261018.Ch2.Brauer.Step029_index_function_h2` | 52 |  |
| `DivisionRep.index` | `L20261018.Ch2.Brauer.Step029_index_function_h2` | 75 |  |
| `E` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 305 |  |
| `E_apply` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 307 |  |
| `E_apply_eq` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 431 |  |
| `E_conj_apply` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 425 |  |
| `E_mul_apply` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 411 |  |
| `E_self_eq_diagonal` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 311 |  |
| `Efield` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 161 | `label:thm:hs-tate-exact-sequences` |
| `Efield_top_eq_F` | `L20261018.Witness.Step036_f7t_thm_ramified_witness_paper_objects` | 50 | `line:1636` |
| `F5_uncond` | `L20261018.Infra.Cohomology.Conjugation.Step014_f5_landing` | 121 |  |
| `FbarValuationHyp` | `L20261018.Ch2.Hensel.ResidueMap.Step062_mu_p_residue_full_chain` | 142 |  |
| `FbarValuationHyp'` | `L20261018.Ch2.Hensel.ResidueMap.Step063_mu_p_residue_instance` | 94 |  |
| `FbarValuationHyp₂` | `L20261018.Ch2.Hensel.Valuation.Step037_nu_pth_root_zero` | 98 |  |
| `FbarValuationHyp₃` | `L20261018.Ch2.Hensel.Valuation.Step039_integral_closure_stable` | 86 |  |
| `FbarValuationHyp₄` | `L20261018.Ch2.Hensel.Inertia.Step028_inertia_subgroup_galois` | 56 |  |
| `FinInt` | `L20261018.Ch2.Hensel.Inertia.Step007_knr_correct_carrier` | 82 | `line:8152` |
| `FqD` | `L20261018.Witness.Step025_f7t_hne_hval` | 93 | `line:1608` |
| `FqD_val` | `L20261018.Witness.Step025_f7t_hne_hval` | 105 | `line:1608` |
| `Fr` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 74 |  |
| `GsInputHyp` | `L20261018.Ch2.Hensel.Inertia.Step027_cd_l_inertia_vanishing` | 65 |  |
| `H0Iso_inv_eq_pi` | `L20261018.Infra.Cohomology.Boundary.Step017_h0_conj_compatibility` | 66 | `line:3580` |
| `H0_conj` | `L20261018.Infra.Cohomology.Boundary.Step017_h0_conj_compatibility` | 103 | `line:3580` |
| `H0ex` | `L20261018.Ch3.NormImage.Step019_three_six_short_names` | 27 |  |
| `H1π_conjCocycle` | `L20261018.Infra.Cohomology.Boundary.Step020_conj_one_cocycle` | 105 |  |
| `H2` | `L20261018.Ch2.Kummer.Step003_triple_cup_product` | 48 |  |
| `H2` | `L20261018.Core.Step001_bi_kummer_data` | 665 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `H3` | `L20261018.Ch2.Kummer.Step003_triple_cup_product` | 51 |  |
| `HasNonzeroKummerCup` | `L20261018.Witness.Step001_bi_kummer_data_nonempty` | 92 |  |
| `HasNonzeroKummerCupSomewhere` | `L20261018.Witness.Step001_bi_kummer_data_nonempty` | 98 |  |
| `HenselResidueData` | `L20261018.Ch4.Step003_ramified_vanishing_paper_objects` | 52 | `label:lem:ramified-vanishing; label:prop:prelim-residue` |
| `HenselResidueData.ker_val_eq_range_infl` | `L20261018.Ch4.Step012_ramified_vanishing_paper_route` | 53 | `line:1608` |
| `HenselResidueData.ker_val_eq_range_infl_free` | `L20261018.Ch4.Step014_ramified_vanishing_hensel_level` | 157 | `line:1608` |
| `HenselResidueData.tame_pi_u_of_skew` | `L20261018.Witness.Step008_tame_residue_facts_q7` | 57 | `label:prop:prelim-residue` |
| `HenselResidueData.toCore` | `L20261018.Witness.Step008_tame_residue_facts_q7` | 130 | `label:prop:prelim-residue` |
| `HenselResidueDataCore` | `L20261018.Witness.Step008_tame_residue_facts_q7` | 73 | `label:prop:prelim-residue` |
| `InertiaProPSylowData` | `L20261018.Ch2.Hensel.Inertia.Step013_inertia_pro_p_sylow_data` | 70 | `line:9625; line:9627` |
| `InertiaProPSylowData.congrContinuousMulEquiv` | `L20261018.Ch2.Hensel.Inertia.Step022_cd_p_inertia_unconditional` | 75 | `line:9627` |
| `InnerConjTrivial` | `L20261018.Infra.Cohomology.Boundary.Step012_inner_conj_trivial_hyp` | 41 |  |
| `IsSplit` | `L20261018.Ch3.BiKummer.Step014_splitting_field` | 40 |  |
| `K2` | `L20261018.Ch3.NormImage.Step002_five_term_mg_k2_data` | 37 |  |
| `K2ex` | `L20261018.Ch3.NormImage.Step019_three_six_short_names` | 32 |  |
| `K2sub` | `L20261018.Ch3.NormImage.Step012_three_six_k2_submodule` | 47 |  |
| `KF` | `L20261018.Ch2.Kummer.Step008_bi_kummer_kernel_restriction` | 31 |  |
| `Knr` | `L20261018.Ch2.Hensel.Inertia.Step002_knr_definition` | 48 |  |
| `KnrLoc` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 74 | `label:sec:cohomology-complete-dv` |
| `KnrResidueObligation` | `L20261018.Ch2.Kummer.Step049_two_cup_formulas_remaining` | 59 |  |
| `KnrResidueReduced` | `L20261018.Ch2.Hensel.ResidueMap.Step051_h1_z_equiv_galo_v` | 175 | `line:1050` |
| `KnrSubfield` | `L20261018.Ch2.Hensel.Inertia.Step007_knr_correct_carrier` | 117 | `line:8152` |
| `KnrUnits` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 147 | `line:8162; line:8165` |
| `KnrUnits'` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 114 | `line:8162; line:8163` |
| `Knr_def` | `L20261018.Ch2.Hensel.Inertia.Step002_knr_definition` | 58 |  |
| `Knr_eq_KnrLoc` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 134 | `label:sec:cohomology-complete-dv` |
| `Knr_eq_fixedField` | `L20261018.Ch2.Hensel.Inertia.Step003_knr_galois_quotient` | 118 | `label:sec:cohomology-complete-dv` |
| `L` | `L20261018.Ch2.Brauer.Step011_kummer_extension_generator` | 32 |  |
| `M` | `L20261018.Ch3.NormImage.Step003_norm_image_def` | 28 |  |
| `MG` | `L20261018.Ch3.NormImage.Step002_five_term_mg_k2_data` | 22 |  |
| `MGsub` | `L20261018.Ch3.NormImage.Step011_three_six_h1_module` | 44 |  |
| `MerkurjevSuslin` | `L20261018.Ch2.Hensel.TameSymbol.Step015_tame_symbol_hyp_from_merkurjev_suslin` | 136 |  |
| `NG` | `L20261018.Ch3.NormImage.Step003_norm_image_def` | 44 |  |
| `NGsub` | `L20261018.Ch3.NormImage.Step011_three_six_h1_module` | 52 |  |
| `Ncor` | `L20261018.Ch3.NormImage.Step003_norm_image_def` | 40 |  |
| `Nsub` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 177 | `label:thm:hs-tate-exact-sequences` |
| `Nsub_coe` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 231 | `label:thm:hs-tate-exact-sequences` |
| `Nsub_le_Uperp` | `L20261018.Ch3.NormImage.Step016_three_six_hnu` | 30 |  |
| `Nsub_toAddSubgroup` | `L20261018.Ch3.NormImage.Step015_three_six_assembly_u_alignment` | 52 |  |
| `PaperTameResidueFormulas` | `L20261018.Ch2.Hensel.ResidueMap.Step045_residue_prop_two_literal` | 59 | `line:1052` |
| `Phi` | `L20261018.Core.Step001_bi_kummer_data` | 48 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `Phi_a1` | `L20261018.Core.Step001_bi_kummer_data` | 113 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `Phi_a2` | `L20261018.Core.Step001_bi_kummer_data` | 116 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `Phi_apply` | `L20261018.Core.Step001_bi_kummer_data` | 58 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `PowClassGen` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step002_units_cup_vanish_reduction` | 74 |  |
| `Q` | `L20261018.Infra.Cohomology.Boundary.Step004_coinduced_ses_acyclic` | 39 |  |
| `Qdisc` | `L20261018.Infra.Cohomology.Step004_q_discrete_h1_acyclic` | 28 |  |
| `QdiscRep` | `L20261018.Infra.Cohomology.Step005_cont_integral_dual_shift` | 100 | `label:sec:cohomology-complete-dv` |
| `QoverZdisc` | `L20261018.Infra.Cohomology.Step005_cont_integral_dual_shift` | 60 | `label:sec:cohomology-complete-dv` |
| `RInv` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 58 |  |
| `RInvEquiv` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 69 |  |
| `RInvEquiv_smul` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 85 |  |
| `RInv_eq_top` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 61 |  |
| `ResH1Type` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 129 |  |
| `ResH2Type` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 133 |  |
| `ResidueCupData` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 51 | `label:lem:ramified-vanishing` |
| `RestrictedCoindAcyclic` | `L20261018.Infra.Cohomology.ResidueLES.Step032_inf_c_inverse_narrowed` | 40 |  |
| `SymbolAlg` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 86 |  |
| `TBI` | `L20261018.Infra.Cohomology.Coinduced.Step016_gs617_ses1` | 81 |  |
| `TameModel` | `L20261018.Ch2.Hensel.Inertia.Step019_tame_module_l_part_infinite` | 65 |  |
| `TameResidueFacts` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 92 | `line:1050; line:1608; line:1636; line:1648` |
| `TameSymbolFactors` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 128 | `label:eq:prelim-tame; line:1050` |
| `TgCompat` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step021_tg_compatibility` | 106 |  |
| `TgSection` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step020_tg_definition` | 58 |  |
| `TsenHyp` | `L20261018.Ch2.Rost.Step002_tsen_cd_p_le_one` | 108 |  |
| `U` | `L20261018.Core.Step001_bi_kummer_data` | 45 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `U_alignment` | `L20261018.Ch3.NormImage.Step015_three_six_assembly_u_alignment` | 73 |  |
| `U_inf_Uperp` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 133 | `label:lem:ramified-vanishing` |
| `UnitsCupVanish` | `L20261018.Ch2.Hensel.ResidueMap.Step041_residue_map_single_hypothesis` | 77 | `line:1023` |
| `UnramifiedKummer` | `L20261018.Ch2.Hensel.Inertia.Step033_unramified_kummer_hyp` | 56 |  |
| `Uperp` | `L20261018.Core.Step001_bi_kummer_data` | 56 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `V` | `L20261018.Ch2.Kummer.Step003_triple_cup_product` | 45 |  |
| `V` | `L20261018.Core.Step001_bi_kummer_data` | 664 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `VKG` | `L20261018.Ch2.Hensel.ResidueMap.Step036_residue_cup_product_interface` | 44 | `label:lemma-residue-cup-product; line:1608; line:1636; line:1648` |
| `VKG_cup_eq_zero_of_residueSpan_le` | `L20261018.Infra.Cohomology.ResidueLES.Step015_vkg_kummer_decomposition` | 90 |  |
| `VKern` | `L20261018.Ch2.Hensel.ResidueMap.Step035_hens_residue_data_no_finite` | 16 |  |
| `ValCompat` | `L20261018.Ch2.Hensel.Valuation.Step021_val_compat_elementwise` | 10 |  |
| `ValCompat` | `L20261018.Ch2.Hensel.Valuation.Step021_val_compat_elementwise` | 42 |  |
| `ValFiltrationCompat` | `L20261018.Ch2.Hensel.Valuation.Step005_eisenstein_uniformizer` | 36 |  |
| `ValIntegralityCompat` | `L20261018.Ch2.Hensel.Valuation.Step007_integer_clear_denominators` | 31 |  |
| `X` | `L20261018.Ch2.Brauer.Step015_crossed_product_generators` | 29 |  |
| `X_pow` | `L20261018.Ch2.Brauer.Step015_crossed_product_generators` | 33 |  |
| `X_pow_sub_C_irreducible_iff_of_odd` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step004_capelli_criterion` | 17 |  |
| `Xmat` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 53 |  |
| `Xmat_eq_diagonal` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 289 |  |
| `Xmat_pow` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 104 |  |
| `Y` | `L20261018.Ch2.Brauer.Step015_crossed_product_generators` | 38 |  |
| `Y_mul_X` | `L20261018.Ch2.Brauer.Step015_crossed_product_generators` | 42 |  |
| `Y_mul_X'` | `L20261018.Ch2.Brauer.Step015_crossed_product_generators` | 48 |  |
| `Y_pow` | `L20261018.Ch2.Brauer.Step019_y_pow_eq_b` | 62 |  |
| `Ymat` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 57 |  |
| `Ymat_apply_of_ne_zero` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 73 |  |
| `Ymat_apply_pred` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 175 |  |
| `Ymat_mul_Xmat` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 158 |  |
| `Ymat_mul_diagonal` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 79 |  |
| `Ymat_pow` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 258 |  |
| `Ymat_pow_apply` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 186 |  |
| `ZMod0` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 100 | `line:8162; line:8165` |
| `a1F` | `L20261018.Witness.Step025_f7t_hne_hval` | 121 | `line:1608` |
| `a1Q7` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 88 |  |
| `a2F` | `L20261018.Witness.Step025_f7t_hne_hval` | 124 | `line:1608` |
| `a2Q7` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 90 |  |
| `aUnit` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 248 |  |
| `aUnit_val` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 254 |  |
| `a_ne_zero` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 241 |  |
| `absoluteGaloisGroupRestrictEquiv` | `L20261018.Infra.Galois.Step002_absolute_galois_iso_unconditional` | 13 |  |
| `absoluteGaloisGroup_continuousMulEquiv_unconditional` | `L20261018.Infra.Galois.Step002_absolute_galois_iso_unconditional` | 49 |  |
| `absoluteGaloisGroup_fixes_pow_eq_one` | `L20261018.Ch2.Hensel.Inertia.Step040_tame_character_galois_invariant` | 73 |  |
| `absoluteGaloisGroup_mulEquiv_apply` | `L20261018.Infra.Galois.Step002_absolute_galois_iso_unconditional` | 54 |  |
| `absoluteGaloisGroup_mulEquiv_unconditional` | `L20261018.Infra.Galois.Step002_absolute_galois_iso_unconditional` | 44 |  |
| `addEquiv_map_zmod_smul` | `L20261018.Ch2.Kummer.Step016_zeta_independence_carrier` | 52 |  |
| `addEquiv_symm_eq_smul` | `L20261018.Ch2.Kummer.Step016_zeta_independence_carrier` | 63 |  |
| `addHomTransport` | `L20261018.Ch3.NormImage.Step017_three_six_quotient_transport` | 35 |  |
| `addHomTransport_apply` | `L20261018.Ch3.NormImage.Step017_three_six_quotient_transport` | 40 |  |
| `addHomTransport_injective` | `L20261018.Ch3.NormImage.Step017_three_six_quotient_transport` | 46 |  |
| `addHomTransport_surjective` | `L20261018.Ch3.NormImage.Step017_three_six_quotient_transport` | 52 |  |
| `addMonoidHom_map_zmod_smul` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 68 | `label:thm:hs-tate-exact-sequences` |
| `addSubgroupQuotientModule` | `L20261018.Ch3.NormImage.Step013_three_six_assembly_module` | 38 |  |
| `addVal_ne_top_iff` | `L20261018.Ch2.Hensel.Valuation.Step030_val_compat_order_function` | 31 |  |
| `additiveHilbert90` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 177 | `label:lemma-additive-hilbert90` |
| `additiveHilbert90_one` | `L20261018.Ch2.Kummer.Step043_kummer_bridge_on_h2` | 66 |  |
| `adjoin_alpha` | `L20261018.Ch2.Brauer.Step020_adjoin_surjectivity_blocks` | 29 |  |
| `adjoin_eq_top` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 142 |  |
| `adjoin_eq_top` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 492 |  |
| `adjoin_genSet_eq_top` | `L20261018.Ch2.Brauer.Step022_adjoin_top_assembly` | 53 |  |
| `adjoin_rootSet_eq_bot_of_isPow` | `L20261018.Ch2.Kummer.Step009_pth_power_field_trivial` | 52 |  |
| `adjoin_root_eq_top` | `L20261018.Ch2.Hensel.ResidueMap.Step028_residue_phi_injective` | 58 |  |
| `adjoin_root_eq_top'` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step003_norm_group_adjoin_root` | 95 |  |
| `algEquivToLinearEquiv` | `L20261018.Ch3.BiKummer.Step004_h_nrd_well_defined` | 36 |  |
| `algebraMap_mem_integralClosure` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step034_n4_paper_form` | 101 |  |
| `algebraMap_mem_valuationSubring` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step036_integral_closure_ring_map` | 58 |  |
| `alone.` | `L20261018.Ch2.Brauer.Step002_reduced_norm_maximal_subfield` | 11 |  |
| `alt` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 123 | `label:lem:ramified-vanishing` |
| `alt'` | `L20261018.Core.Step001_bi_kummer_data` | 36 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `bL` | `L20261018.Ch2.Brauer.Step013_carry_cocycle_index` | 34 |  |
| `bL'` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 155 |  |
| `basis_change_brauer` | `L20261018.Ch4.Step010_basis_change_brauer_class` | 37 | `label:lem:basis-change` |
| `basis_change_kummer` | `L20261018.Ch4.Step001_basis_change_first_slot` | 127 | `label:lem:basis-change` |
| `basis_mem_adjoin_gen` | `L20261018.Ch2.Brauer.Step021_adjoin_top` | 56 |  |
| `basis_one_eq_one` | `L20261018.Ch2.Brauer.Step016_power_formula_telescope` | 27 |  |
| `basis_pow` | `L20261018.Ch2.Brauer.Step016_power_formula_telescope` | 33 |  |
| `basis_repr_root_pow` | `L20261018.Ch2.Hensel.Valuation.Step017_repr_computations` | 29 |  |
| `basis_repr_smul_root_pow` | `L20261018.Ch2.Hensel.Valuation.Step017_repr_computations` | 43 |  |
| `basis_root_pow` | `L20261018.Ch2.Hensel.Valuation.Step016_explicit_basis_powers` | 32 |  |
| `biKummerDataKummer` | `L20261018.Ch3.BiKummer.Step001_bi_kummer_data_from_kummer` | 35 |  |
| `biKummerDataKummer_a1` | `L20261018.Ch3.BiKummer.Step001_bi_kummer_data_from_kummer` | 44 |  |
| `biKummerDataKummer_a2` | `L20261018.Ch3.BiKummer.Step001_bi_kummer_data_from_kummer` | 50 |  |
| `biKummerData_nonempty` | `L20261018.Witness.Step001_bi_kummer_data_nonempty` | 54 |  |
| `bilinGen` | `L20261018.Ch2.Hensel.TameSymbol.Step015_tame_symbol_hyp_from_merkurjev_suslin` | 109 |  |
| `brOfH2` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 149 |  |
| `brOfH2_apply` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 154 |  |
| `brOfH2_cup` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 188 |  |
| `brOfH2_eq_nsmul` | `L20261018.Ch2.Kummer.Step016_zeta_independence_carrier` | 193 |  |
| `brOfH2_injective` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 197 |  |
| `brOfH2_smul_cup` | `L20261018.Ch2.Brauer.Step031_brauer_of_h2_smul` | 89 |  |
| `brauerClass_tensorSymbol` | `L20261018.Ch2.Brauer.Step035_symbol_algebra_tensor_class` | 28 |  |
| `brauerGroupEquivBr_carryCocycle` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 263 |  |
| `brauerGroupEquivBr_crossedProductClass` | `L20261018.Ch2.Brauer.Step025_crossed_product_class_inflation` | 70 |  |
| `brauerOfH2` | `L20261018.Ch2.Brauer.Step029_index_function_h2` | 45 |  |
| `brauerOfH2_eq_pow` | `L20261018.Ch2.Brauer.Step034_index_zeta_independent` | 33 |  |
| `brauerOfH2_pow_prime` | `L20261018.Ch2.Brauer.Step034_index_zeta_independent` | 48 |  |
| `brauerOfH2_smul_cup` | `L20261018.Ch2.Brauer.Step031_brauer_of_h2_smul` | 103 |  |
| `brauer_h2_equiv_available` | `L20261018.Infra.Cohomology.Step008_recon_availability_lock` | 39 |  |
| `bridgeKc` | `L20261018.Ch2.Kummer.Step018_bridge_kc_def` | 16 |  |
| `bridgeKc_eq_final` | `L20261018.Ch2.Kummer.Step030_t1_bridge_gm_bypass` | 187 |  |
| `bridgeKc_eq_muP` | `L20261018.Ch2.Kummer.Step032_t1_bridge_same_shape` | 93 |  |
| `bridgeKc_eq_muP'` | `L20261018.Ch2.Kummer.Step039_t1_without_completeness` | 58 |  |
| `bridgeKc_eq_thetaTwo` | `L20261018.Ch2.Kummer.Step027_t1_mu_n_rep_factorization` | 226 |  |
| `bridgeKc_one` | `L20261018.Ch2.Kummer.Step018_bridge_kc_def` | 24 |  |
| `cE` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 64 |  |
| `cEL` | `L20261018.Ch2.Brauer.Step031_brauer_of_h2_smul` | 32 |  |
| `cEL_toAddEquiv` | `L20261018.Ch2.Brauer.Step031_brauer_of_h2_smul` | 39 |  |
| `cE_cup` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 71 |  |
| `cYC` | `L20261018.Ch2.Brauer.Step021_adjoin_top` | 35 |  |
| `cYC'` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 91 |  |
| `cYC'_toFun` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 99 |  |
| `cYC'_toFun_gen'_pow` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 177 |  |
| `capelli_irreducible_iff` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step004_capelli_criterion` | 59 |  |
| `capelli_irreducible_of_not_pow` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step004_capelli_criterion` | 73 |  |
| `carrier_H2` | `L20261018.Infra.Cohomology.ResidueLES.Step006_mu_p_smooth_discrete` | 65 |  |
| `carrier_V` | `L20261018.Infra.Cohomology.ResidueLES.Step006_mu_p_smooth_discrete` | 61 |  |
| `carrier_cup` | `L20261018.Infra.Cohomology.ResidueLES.Step006_mu_p_smooth_discrete` | 69 |  |
| `carryCocycle` | `L20261018.Ch2.Brauer.Step014_carry_cocycle_two_cocycle` | 55 |  |
| `carryCocycle_toFun_gen_pow` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 168 |  |
| `carryExp` | `L20261018.Ch2.Brauer.Step013_carry_cocycle_index` | 50 |  |
| `carryExp_gen` | `L20261018.Ch2.Brauer.Step017_carry_exp_gen_pow` | 38 |  |
| `carryExp_gen_pow` | `L20261018.Ch2.Brauer.Step017_carry_exp_gen_pow` | 43 |  |
| `carryExp_gen_pow_of_lt` | `L20261018.Ch2.Brauer.Step017_carry_exp_gen_pow` | 57 |  |
| `carryExp_lt` | `L20261018.Ch2.Brauer.Step013_carry_cocycle_index` | 54 |  |
| `carryExp_mul` | `L20261018.Ch2.Brauer.Step013_carry_cocycle_index` | 64 |  |
| `carryExp_one` | `L20261018.Ch2.Brauer.Step013_carry_cocycle_index` | 58 |  |
| `carryFun` | `L20261018.Ch2.Brauer.Step014_carry_cocycle_two_cocycle` | 48 |  |
| `carryFun_one_one` | `L20261018.Ch2.Brauer.Step019_y_pow_eq_b` | 38 |  |
| `carry_assoc` | `L20261018.Ch2.Brauer.Step012_carry_cocycle_arithmetic` | 41 |  |
| `carry_left` | `L20261018.Ch2.Brauer.Step012_carry_cocycle_arithmetic` | 24 |  |
| `carry_right` | `L20261018.Ch2.Brauer.Step012_carry_cocycle_arithmetic` | 33 |  |
| `cdLE` | `L20261018.Ch2.Hensel.Inertia.Step013_inertia_pro_p_sylow_data` | 103 | `line:9625; line:9627` |
| `cdLE_inertia` | `L20261018.Ch2.Hensel.Inertia.Step021_inertia_sylow_z_l` | 233 |  |
| `cdLE_of_procyclic` | `L20261018.Ch2.Hensel.Inertia.Step015_cd_p_procyclic_criterion` | 73 | `line:8` |
| `cdLE_of_procyclic_group` | `L20261018.Ch2.Hensel.Inertia.Step018_procyclic_l_part_sylow` | 163 | `line:9626` |
| `cdLE_padicInt_one` | `L20261018.Ch2.Rost.Step001_cd_p_z_p_le_one` | 107 | `label:prop-cd-Z-hat; line:9625; line:9627` |
| `cdLE_padicInt_via_data` | `L20261018.Ch2.Hensel.Inertia.Step013_inertia_pro_p_sylow_data` | 145 | `line:9625; line:9627` |
| `cd_padicInt_ne_zero` | `L20261018.Ch2.Rost.Step001_cd_p_z_p_le_one` | 169 | `label:prop-cd-Z-hat; line:9625; line:9627` |
| `ch4TameSymbolHyp_iff_disjoint` | `L20261018.Ch2.Hensel.TameSymbol.Step003_ch4_tame_symbol_hyp` | 69 |  |
| `ch4TameSymbolHyp_iff_tameResidueFacts` | `L20261018.Ch2.Hensel.TameSymbol.Step005_tame_symbol_hyp_iff_r1_r2` | 69 |  |
| `ch4TameSymbolHyp_of_dependent` | `L20261018.Ch2.Hensel.TameSymbol.Step003_ch4_tame_symbol_hyp` | 84 |  |
| `ch4TameSymbolHyp_of_divisibleResidue` | `L20261018.Ch2.Hensel.TameSymbol.Step004_tame_symbol_hyp_divisible_residue` | 79 | `line:1050` |
| `ch4TameSymbolHyp_of_finite'` | `L20261018.Ch2.Hensel.TameSymbol.Step004_tame_symbol_hyp_divisible_residue` | 91 | `line:1050` |
| `ch4TameSymbolHyp_of_finrank_ker_le_one` | `L20261018.Ch2.Hensel.ResidueMap.Step055_r2_exact_boundary` | 171 |  |
| `ch4TameSymbolHyp_of_merkurjevSuslin` | `L20261018.Ch2.Hensel.TameSymbol.Step016_tame_symbol_hyp_merkurjev_suslin` | 86 | `line:1050` |
| `ch4TameSymbolHyp_of_obligation` | `L20261018.Ch2.Kummer.Step049_two_cup_formulas_remaining` | 68 |  |
| `ch4TameSymbolHyp_of_residueSpan_eq_bot` | `L20261018.Ch4.Step038_ch4_proof_structure_index` | 102 |  |
| `ch4TameSymbolHyp_of_subsingleton_H2` | `L20261018.Ch2.Hensel.ResidueMap.Step060_h_kappa_h2_zero` | 147 |  |
| `ch4TameSymbolHyp_of_subsingleton_H2_domain` | `L20261018.Ch2.Hensel.ResidueMap.Step061_mu_p_in_residue_field` | 100 |  |
| `ch4TameSymbolHyp_of_subsingleton_H2_residue` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 219 |  |
| `ch4TameSymbolHyp_of_subsingleton_H2_residue'` | `L20261018.Ch4.Step038_ch4_proof_structure_index` | 117 |  |
| `ch4TameSymbolHyp_of_subsingleton_H2_residueField` | `L20261018.Ch2.Hensel.ResidueMap.Step060_h_kappa_h2_zero` | 179 |  |
| `ch4TameSymbolHyp_of_subsingleton_H2canon` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 216 |  |
| `ch4TameSymbolHyp_of_tameSymbolFactors` | `L20261018.Ch2.Hensel.TameSymbol.Step016_tame_symbol_hyp_merkurjev_suslin` | 66 | `line:1050` |
| `ch4TameSymbolHyp_of_tsen` | `L20261018.Ch2.Rost.Step002_tsen_cd_p_le_one` | 162 |  |
| `ch4TameSymbolHyp_viaResidue` | `L20261018.Witness.Step040_tame_symbol_hyp_witness` | 72 |  |
| `ch4_single_carrier_combined` | `L20261018.Ch4.Step019_single_carrier_statement` | 46 |  |
| `chi` | `L20261018.Ch2.Hensel.ResidueMap.Step039_residue_classes_linear_dependent` | 38 |  |
| `chi_surjective` | `L20261018.Ch2.Hensel.ResidueMap.Step039_residue_classes_linear_dependent` | 41 |  |
| `closure_toAddSubgroup` | `L20261018.Ch3.NormImage.Step015_three_six_assembly_u_alignment` | 34 |  |
| `cochainSES_S` | `L20261018.Infra.Cohomology.Boundary.Step016_delta_zero_naturality` | 84 | `line:3585` |
| `cochainSES_S_eq` | `L20261018.Infra.Cohomology.Boundary.Step016_delta_zero_naturality` | 95 | `line:3585` |
| `cochainSES_S_shortExact` | `L20261018.Infra.Cohomology.Boundary.Step016_delta_zero_naturality` | 99 | `line:3585` |
| `cochainsMap_apply` | `L20261018.Infra.Cohomology.Boundary.Step017_h0_conj_compatibility` | 57 | `line:3580` |
| `cochainsMap_one_sub_apply` | `L20261018.Infra.Cohomology.Boundary.Step024_prism_identity_on_cycles` | 62 |  |
| `cochainsMap_zero_eq` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 80 |  |
| `coe_e` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 69 |  |
| `coe_infl1ResToVKG_eQ` | `L20261018.Ch4.Step046_exists_residue_map` | 168 |  |
| `coe_quot_smul` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step030_tg_well_defined_complete` | 66 |  |
| `coe_quot_smul'` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step030_tg_well_defined_complete` | 58 |  |
| `coe_quotientMk_smul_subtype_fixedPoints` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 242 |  |
| `coe_quotient_smul_subtype_fixedPoints` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 229 |  |
| `coe_rho` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step012_units_cup_vanish_unconditional` | 37 |  |
| `coe_rho'` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 58 |  |
| `coe_smul` | `L20261018.Infra.Cohomology.ResidueLES.Step018_cont_inv_b_pointwise` | 15 |  |
| `coe_znat` | `L20261018.Ch2.Hensel.Valuation.Step030_val_compat_order_function` | 48 |  |
| `coeffAlg` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 53 | `line:8156; line:8160` |
| `coeffChangeEquiv` | `L20261018.Infra.Cohomology.Conjugation.Step010_h_conj1_implies_f5` | 90 |  |
| `coeffChangeEquiv_uncond` | `L20261018.Infra.Cohomology.Conjugation.Step013_h_conj1_discharged` | 109 |  |
| `coeffIdHom` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 137 |  |
| `coeffIdHomK` | `L20261018.Ch2.Hensel.ResidueMap.Step060_h_kappa_h2_zero` | 73 |  |
| `coeffIncl` | `L20261018.Ch2.Hensel.Inertia.Step007_knr_correct_carrier` | 54 | `line:8152` |
| `coeffInclH1` | `L20261018.Ch4.Step046_exists_residue_map` | 98 |  |
| `coeffInclH1_injective` | `L20261018.Ch4.Step046_exists_residue_map` | 122 |  |
| `coeffInclH1_ne_zero` | `L20261018.Ch4.Step046_exists_residue_map` | 141 |  |
| `coeffIncl_coeff` | `L20261018.Ch2.Hensel.Inertia.Step007_knr_correct_carrier` | 74 | `line:8152` |
| `coeffIncl_knrMap` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 67 | `line:8156; line:8160` |
| `coeffMap_comp_coeffMap_eq_zero` | `L20261018.Infra.Cohomology.Coinduced.Step024_explicit_coeff_one_zero` | 82 |  |
| `coeffMap_comp_map_quotientMk` | `L20261018.Infra.Cohomology.Coinduced.Step020_map_phi_decomposition` | 51 |  |
| `coeffMap_ofDiscrete` | `L20261018.Ch2.Kummer.Step031_t1_model_comparison` | 65 |  |
| `coeffMap_restrictScalarsIntEquiv_comm` | `L20261018.Infra.Cohomology.Step001_coeff_map_scalar_restriction` | 44 |  |
| `coeffMap_smul` | `L20261018.Ch2.Kummer.Step016_zeta_independence_carrier` | 74 |  |
| `coeffMap_zero_eq` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 93 |  |
| `coeffMatrix` | `L20261018.Ch2.Hensel.Valuation.Step022_norm_congruence` | 35 |  |
| `coeffSubAddHom` | `L20261018.Infra.Cohomology.Coinduced.Step030_coefficient_bridge_m_inv` | 40 |  |
| `coeffSubAddHom_apply` | `L20261018.Infra.Cohomology.Coinduced.Step030_coefficient_bridge_m_inv` | 48 |  |
| `coeffSubAddHom_smul` | `L20261018.Infra.Cohomology.Coinduced.Step031_coefficient_bridge_explicit_model` | 56 |  |
| `coeff_scalar` | `L20261018.Ch2.Kummer.Step033_t1_closed` | 59 |  |
| `coeff_scalar'` | `L20261018.Ch2.Kummer.Step039_t1_without_completeness` | 87 |  |
| `coeff_zero_mem_maximalIdeal` | `L20261018.Ch2.Hensel.Valuation.Step026_coefficient_in_maximal_ideal` | 35 |  |
| `cohomEquiv` | `L20261018.Ch2.Kummer.Step010_cup_fp_eq_galo_cup` | 92 |  |
| `cohomEquiv_eq_coeffMap` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 58 |  |
| `cohomFpMap_ofDiscrete` | `L20261018.Ch2.Kummer.Step029_t1_group_variable_cancel` | 128 |  |
| `cohomFpMap_symm_comp_restrict` | `L20261018.Ch2.Kummer.Step030_t1_bridge_gm_bypass` | 82 |  |
| `cohomologicalDimensionAt_eq_one` | `L20261018.Ch2.Hensel.Inertia.Step013_inertia_pro_p_sylow_data` | 123 | `line:9625; line:9627` |
| `cohomologicalDimensionAt_le_one` | `L20261018.Ch2.Hensel.Inertia.Step013_inertia_pro_p_sylow_data` | 97 | `line:9625; line:9627` |
| `cohomologicalDimensionAt_le_padicInt` | `L20261018.Ch2.Hensel.Inertia.Step013_inertia_pro_p_sylow_data` | 87 | `line:9625; line:9627` |
| `cohomologicalDimensionAt_padicInt_eq_one` | `L20261018.Ch2.Rost.Step001_cd_p_z_p_le_one` | 100 | `label:prop-cd-Z-hat; line:9625; line:9627` |
| `cohomologicalDimensionAt_padicInt_eq_zHat` | `L20261018.Ch2.Rost.Step001_cd_p_z_p_le_one` | 79 | `label:prop-cd-Z-hat; line:9625; line:9627` |
| `cohomologicalDimensionAt_padicInt_le_one` | `L20261018.Ch2.Rost.Step001_cd_p_z_p_le_one` | 92 | `label:prop-cd-Z-hat; line:9625; line:9627` |
| `cohomologyClass_cYC'` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 195 |  |
| `cohomologyClass_carryCocycle` | `L20261018.Ch2.Brauer.Step026_carry_cocycle_class_cyclic` | 60 |  |
| `cohomologyConjAction` | `L20261018.Infra.Cohomology.Boundary.Step029_conj_action_on_hn` | 62 |  |
| `cohomologyConjAction_of_mem` | `L20261018.Infra.Cohomology.Boundary.Step029_conj_action_on_hn` | 83 |  |
| `coindBotAddEquiv` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 177 |  |
| `coindBotInvariantsEquiv` | `L20261018.Infra.Cohomology.Coinduced.Step013_coinduced_invariants_backward` | 140 |  |
| `coindBotInvariantsEquiv_smul` | `L20261018.Infra.Cohomology.Coinduced.Step014_coinduced_invariants` | 47 |  |
| `coindBotInvariantsIntLinearEquiv` | `L20261018.Infra.Cohomology.Coinduced.Step014_coinduced_invariants` | 74 |  |
| `coindBotPull` | `L20261018.Infra.Cohomology.ResidueLES.Step020_pull_back_map` | 53 |  |
| `coindBotPull_apply` | `L20261018.Infra.Cohomology.ResidueLES.Step020_pull_back_map` | 65 |  |
| `coindBotPull_mem` | `L20261018.Infra.Cohomology.ResidueLES.Step020_pull_back_map` | 71 |  |
| `coindBotSES` | `L20261018.Infra.Cohomology.Boundary.Step006_delta_two_dimension_shift` | 42 |  |
| `coindBotToContInvB` | `L20261018.Infra.Cohomology.ResidueLES.Step020_pull_back_map` | 78 |  |
| `coindBotToContInvB_injective` | `L20261018.Infra.Cohomology.ResidueLES.Step021_descend_pull_inverse` | 61 |  |
| `coindBot_apply_mul_of_mem` | `L20261018.Infra.Cohomology.Coinduced.Step012_coinduced_invariants_forward` | 36 |  |
| `coindBot_apply_out` | `L20261018.Infra.Cohomology.Coinduced.Step012_coinduced_invariants_forward` | 67 |  |
| `coindBot_dimensionShift` | `L20261018.Infra.Cohomology.Boundary.Step006_delta_two_dimension_shift` | 48 |  |
| `coindBot_dimensionShift_two` | `L20261018.Infra.Cohomology.Boundary.Step006_delta_two_dimension_shift` | 58 |  |
| `coindCoker` | `L20261018.Infra.Cohomology.Boundary.Step027_coinduced_ses_h1_h2` | 86 |  |
| `coindCokerAction` | `L20261018.Infra.Cohomology.Boundary.Step027_coinduced_ses_h1_h2` | 90 |  |
| `coindCokerContinuousSMul` | `L20261018.Infra.Cohomology.Boundary.Step027_coinduced_ses_h1_h2` | 94 |  |
| `coindCokerDiscrete` | `L20261018.Infra.Cohomology.Boundary.Step027_coinduced_ses_h1_h2` | 99 |  |
| `coindCompDeltaZeroBar_eq_zero` | `L20261018.Infra.Cohomology.ResidueLES.Step001_f2_delta_zero_vanishes` | 106 | `label:prop-residue-map-long-exact` |
| `coindFwd` | `L20261018.Infra.Cohomology.Coinduced.Step013_coinduced_invariants_backward` | 107 |  |
| `coindFwd_coindRevInv` | `L20261018.Infra.Cohomology.Coinduced.Step013_coinduced_invariants_backward` | 127 |  |
| `coindIncl` | `L20261018.Infra.Cohomology.Boundary.Step002_coinduced_embedding` | 43 |  |
| `coindIncl_apply` | `L20261018.Infra.Cohomology.Boundary.Step002_coinduced_embedding` | 58 |  |
| `coindIncl_equivariant` | `L20261018.Infra.Cohomology.Boundary.Step002_coinduced_embedding` | 68 |  |
| `coindIncl_injective` | `L20261018.Infra.Cohomology.Boundary.Step002_coinduced_embedding` | 62 |  |
| `coindInvFun` | `L20261018.Infra.Cohomology.Coinduced.Step012_coinduced_invariants_forward` | 45 |  |
| `coindInvFun_isLocallyConstant` | `L20261018.Infra.Cohomology.Coinduced.Step012_coinduced_invariants_forward` | 55 |  |
| `coindQuot` | `L20261018.Infra.Cohomology.Boundary.Step003_coinduced_quotient` | 51 |  |
| `coindRange` | `L20261018.Infra.Cohomology.Boundary.Step027_coinduced_ses_h1_h2` | 76 |  |
| `coindRange_stable` | `L20261018.Infra.Cohomology.Boundary.Step027_coinduced_ses_h1_h2` | 80 |  |
| `coindRev` | `L20261018.Infra.Cohomology.Coinduced.Step013_coinduced_invariants_backward` | 77 |  |
| `coindRevFun` | `L20261018.Infra.Cohomology.Coinduced.Step013_coinduced_invariants_backward` | 69 |  |
| `coindRevFun_isLocallyConstant` | `L20261018.Infra.Cohomology.Coinduced.Step013_coinduced_invariants_backward` | 72 |  |
| `coindRevInv` | `L20261018.Infra.Cohomology.Coinduced.Step013_coinduced_invariants_backward` | 100 |  |
| `coindRevInv_coindFwd` | `L20261018.Infra.Cohomology.Coinduced.Step013_coinduced_invariants_backward` | 118 |  |
| `coindRev_mem` | `L20261018.Infra.Cohomology.Coinduced.Step013_coinduced_invariants_backward` | 91 |  |
| `coindSES_delta_one_eq_explicit` | `L20261018.Infra.Cohomology.Coinduced.Step038_h0_leibniz` | 60 |  |
| `coindSES_delta_zero_eq_explicit` | `L20261018.Infra.Cohomology.Coinduced.Step038_h0_leibniz` | 73 |  |
| `coindSES_incl_smul` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 156 |  |
| `coindSES_proj_smul` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 167 |  |
| `coindShortExact` | `L20261018.Infra.Cohomology.Boundary.Step004_coinduced_ses_acyclic` | 76 |  |
| `coindShortExactCoker` | `L20261018.Infra.Cohomology.Boundary.Step027_coinduced_ses_h1_h2` | 104 |  |
| `coindShortExactSubgroup` | `L20261018.Infra.Cohomology.Coinduced.Step001_coind_subgroup_acyclic_hyp` | 95 |  |
| `coindSub` | `L20261018.Infra.Cohomology.Boundary.Step003_coinduced_quotient` | 42 |  |
| `coindSub_stable` | `L20261018.Infra.Cohomology.Boundary.Step003_coinduced_quotient` | 45 |  |
| `coindSubgroupAcyclicOne` | `L20261018.Infra.Cohomology.Coinduced.Step005_closed_subgroup_acyclicity` | 53 |  |
| `coindSubgroupAcyclicOne_bot` | `L20261018.Infra.Cohomology.Coinduced.Step003_coind_subgroup_acyclic_one` | 56 |  |
| `coindSubgroupAcyclic_bot` | `L20261018.Infra.Cohomology.Coinduced.Step001_coind_subgroup_acyclic_hyp` | 79 |  |
| `cokerSES` | `L20261018.Infra.Cohomology.ResidueLES.Step002_t_cokernel_constructed` | 87 |  |
| `cokerSES_X₂` | `L20261018.Infra.Cohomology.ResidueLES.Step004_i_star_delta_zero_bar` | 54 |  |
| `cokerSES_shortExact` | `L20261018.Infra.Cohomology.ResidueLES.Step002_t_cokernel_constructed` | 92 |  |
| `cokernelπ_comp_iTame` | `L20261018.Infra.Cohomology.ResidueLES.Step002_t_cokernel_constructed` | 102 |  |
| `comap_hf` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 84 |  |
| `commonCupMap` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 95 | `label:lem:ramified-vanishing` |
| `commonCupMap_apply` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 104 | `label:lem:ramified-vanishing` |
| `compactSpace_absoluteGaloisGroup` | `L20261018.Infra.Cohomology.ResidueLES.Step007_continuous_615` | 67 |  |
| `compressed_mem_cocycles` | `L20261018.Infra.Cohomology.Boundary.Step023_compressed_cocycle` | 69 |  |
| `conj1Trivial_apply` | `L20261018.Infra.Cohomology.Conjugation.Step008_conj1_trivial_hyp` | 100 |  |
| `conj1Trivial_iff_conjInvariants_eq_top` | `L20261018.Infra.Cohomology.Conjugation.Step011_h_conj1_tauceti_interface` | 65 |  |
| `conj1Trivial_of_conjInvariants_eq_top` | `L20261018.Infra.Cohomology.Conjugation.Step011_h_conj1_tauceti_interface` | 54 |  |
| `conj1Trivial_of_ne_zero` | `L20261018.Infra.Cohomology.Conjugation.Step008_conj1_trivial_hyp` | 108 |  |
| `conj1Trivial_of_tameChar` | `L20261018.Infra.Cohomology.Conjugation.Step013_h_conj1_discharged` | 12 |  |
| `conj1Trivial_of_tameChar` | `L20261018.Infra.Cohomology.Conjugation.Step013_h_conj1_discharged` | 72 |  |
| `conj1_eq_of_fixes_zmultiples_top` | `L20261018.Infra.Cohomology.Conjugation.Step006_conj_trivial_one_element` | 45 |  |
| `conj1_eq_of_ne_zero` | `L20261018.Infra.Cohomology.Conjugation.Step007_conj_trivial_unconditional` | 81 |  |
| `conjCochainsSES` | `L20261018.Infra.Cohomology.Boundary.Step016_delta_zero_naturality` | 107 | `line:3585` |
| `conjCochainsSES_τ₁` | `L20261018.Infra.Cohomology.Boundary.Step016_delta_zero_naturality` | 125 | `line:3585` |
| `conjCochainsSES_τ₃` | `L20261018.Infra.Cohomology.Boundary.Step016_delta_zero_naturality` | 131 | `line:3585` |
| `conjCocycle` | `L20261018.Infra.Cohomology.Boundary.Step020_conj_one_cocycle` | 87 |  |
| `conjCocycle_sub_mem` | `L20261018.Infra.Cohomology.Boundary.Step020_conj_one_cocycle` | 94 |  |
| `conjCoeffHom` | `L20261018.Infra.Cohomology.Boundary.Step011_conj_coeff_hom` | 40 |  |
| `conjCoeffHom_apply` | `L20261018.Infra.Cohomology.Boundary.Step014_conj_action_foundations` | 35 |  |
| `conjCoeffHom_comp_toLinearMap` | `L20261018.Infra.Cohomology.Boundary.Step015_rep_quotient_structure` | 68 | `line:9497` |
| `conjEndH1` | `L20261018.Infra.Cohomology.Conjugation.Step005_gamma_complete` | 51 |  |
| `conjEndHom` | `L20261018.Infra.Cohomology.Boundary.Step015_rep_quotient_structure` | 106 | `line:9497` |
| `conjEndHom_apply` | `L20261018.Infra.Cohomology.Boundary.Step015_rep_quotient_structure` | 117 | `line:9497` |
| `conjEndHom_ker` | `L20261018.Infra.Cohomology.Boundary.Step015_rep_quotient_structure` | 122 | `line:9497` |
| `conjEndQuot` | `L20261018.Infra.Cohomology.Conjugation.Step005_gamma_complete` | 57 |  |
| `conjEndQuot_apply` | `L20261018.Infra.Cohomology.Conjugation.Step005_gamma_complete` | 61 |  |
| `conjEndQuotient` | `L20261018.Infra.Cohomology.Boundary.Step030_conj_action_descends` | 58 |  |
| `conjH` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step021_tg_compatibility` | 52 |  |
| `conjH_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step022_nsw_y_exists` | 61 |  |
| `conjInvariant_add` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step027_tg_additive_component` | 46 |  |
| `conjInvariants_eq_top` | `L20261018.Infra.Cohomology.Conjugation.Step013_h_conj1_discharged` | 101 |  |
| `conjInvariants_eq_top_of_conj1Trivial` | `L20261018.Infra.Cohomology.Conjugation.Step011_h_conj1_tauceti_interface` | 44 |  |
| `conjMap` | `L20261018.Infra.Cohomology.Boundary.Step011_conj_coeff_hom` | 61 |  |
| `conjMap_comp` | `L20261018.Infra.Cohomology.Boundary.Step014_conj_action_foundations` | 55 |  |
| `conjMap_mul` | `L20261018.Infra.Cohomology.Boundary.Step015_rep_quotient_structure` | 81 | `line:9497` |
| `conjMap_one` | `L20261018.Infra.Cohomology.Boundary.Step015_rep_quotient_structure` | 90 | `line:9497` |
| `conjMap_one_eq_one_of` | `L20261018.Infra.Cohomology.Boundary.Step021_n1_reduction` | 82 |  |
| `conjNormalMap_comp_explicitH1` | `L20261018.Infra.Cohomology.Conjugation.Step002_m_carrier_bridge_beta` | 77 |  |
| `conjNormalMap_degreeZeroClass` | `L20261018.Infra.Cohomology.Conjugation.Step003_m_body_complete` | 70 |  |
| `conjNormal_coe_eq_inverseConjugationHom` | `L20261018.Infra.Cohomology.Conjugation.Step002_m_carrier_bridge_beta` | 59 |  |
| `conjNormal_hequiv` | `L20261018.Infra.Cohomology.Conjugation.Step002_m_carrier_bridge_beta` | 66 |  |
| `conjSubtypeHom` | `L20261018.Infra.Cohomology.Boundary.Step010_conj_map` | 50 |  |
| `conjSubtypeHom_coe` | `L20261018.Infra.Cohomology.Boundary.Step010_conj_map` | 64 |  |
| `conjSubtypeHom_mul` | `L20261018.Infra.Cohomology.Boundary.Step014_conj_action_foundations` | 46 |  |
| `conjSubtypeHom_one` | `L20261018.Infra.Cohomology.Boundary.Step014_conj_action_foundations` | 40 |  |
| `conj_isCocycle` | `L20261018.Infra.Cohomology.Boundary.Step020_conj_one_cocycle` | 74 |  |
| `conj_one_cochain` | `L20261018.Infra.Cohomology.Boundary.Step019_prism_identity_n1` | 76 |  |
| `conj_one_cochain_sub` | `L20261018.Infra.Cohomology.Boundary.Step019_prism_identity_n1` | 92 |  |
| `conj_ρ_comm` | `L20261018.Infra.Cohomology.Boundary.Step020_conj_one_cocycle` | 56 |  |
| `contB` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 56 | `line:9528` |
| `contC` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 60 | `line:9528` |
| `contCModule` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 79 |  |
| `contC_exists_cup_preimage` | `L20261018.Infra.Cohomology.Coinduced.Step040_e_zero_surjective_leibniz` | 82 |  |
| `contC_exists_delta_zero_eq` | `L20261018.Infra.Cohomology.Coinduced.Step039_delta_zero_surjective` | 54 |  |
| `contC_exists_delta_zero_eq_of_H1` | `L20261018.Infra.Cohomology.Coinduced.Step039_delta_zero_surjective` | 67 |  |
| `contC_nsmul_eq_zero` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 69 |  |
| `contC_smul_comm_G` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 92 |  |
| `contC_smul_eq_nsmul_val` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 86 |  |
| `contCoindBotDimensionShiftTwo` | `L20261018.Infra.Cohomology.ResidueLES.Step007_continuous_615` | 83 |  |
| `contCoindBotDimensionShiftTwo_type_lock` | `L20261018.Infra.Cohomology.ResidueLES.Step007_continuous_615` | 90 |  |
| `contCoindSES` | `L20261018.Infra.Cohomology.ResidueLES.Step009_continuous_dim_shift_ses` | 27 |  |
| `contDeltaZeroBar` | `L20261018.Infra.Cohomology.ResidueLES.Step009_continuous_dim_shift_ses` | 43 |  |
| `contDeltaZeroBar_conjNormal` | `L20261018.Infra.Cohomology.Conjugation.Step001_m_conj_equivariant` | 45 |  |
| `contDeltaZeroBar_conjNormal_apply` | `L20261018.Infra.Cohomology.Conjugation.Step001_m_conj_equivariant` | 53 |  |
| `contDeltaZeroBar_eq_delta` | `L20261018.Infra.Cohomology.ResidueLES.Step011_continuous_res_delta_square` | 46 |  |
| `contDeltaZeroBar_kills_proj` | `L20261018.Infra.Cohomology.ResidueLES.Step010_continuous_f2` | 37 |  |
| `contDelta_res_naturality` | `L20261018.Infra.Cohomology.ResidueLES.Step011_continuous_res_delta_square` | 36 |  |
| `contDimShiftSES` | `L20261018.Infra.Cohomology.ResidueLES.Step009_continuous_dim_shift_ses` | 34 |  |
| `contF1` | `L20261018.Infra.Cohomology.ResidueLES.Step013_continuous_f1` | 157 | `label:prop-residue-map-long-exact` |
| `contF1_infl` | `L20261018.Infra.Cohomology.ResidueLES.Step013_continuous_f1` | 186 | `label:prop-residue-map-long-exact` |
| `contF1_split` | `L20261018.Infra.Cohomology.ResidueLES.Step014_continuous_d_two_blocks` | 142 |  |
| `contFC` | `L20261018.Infra.Cohomology.ResidueLES.Step013_continuous_f1` | 131 | `label:prop-residue-map-long-exact` |
| `contFC_eq` | `L20261018.Infra.Cohomology.ResidueLES.Step013_continuous_f1` | 135 | `label:prop-residue-map-long-exact` |
| `contFC_smul` | `L20261018.Infra.Cohomology.ResidueLES.Step013_continuous_f1` | 141 | `label:prop-residue-map-long-exact` |
| `contH1BaseBridge` | `L20261018.Infra.Cohomology.ResidueLES.Step008_base_ring_alignment` | 68 |  |
| `contH1_iso_conjNormal` | `L20261018.Infra.Cohomology.Conjugation.Step002_m_carrier_bridge_beta` | 109 |  |
| `contH1_iso_symm_conjNormal` | `L20261018.Infra.Cohomology.Conjugation.Step002_m_carrier_bridge_beta` | 116 |  |
| `contH2BaseBridge` | `L20261018.Infra.Cohomology.ResidueLES.Step008_base_ring_alignment` | 75 |  |
| `contITame` | `L20261018.Infra.Cohomology.ResidueLES.Step013_continuous_f1` | 114 | `label:prop-residue-map-long-exact` |
| `contITame_mk` | `L20261018.Infra.Cohomology.ResidueLES.Step013_continuous_f1` | 119 | `label:prop-residue-map-long-exact` |
| `contITame_smul` | `L20261018.Infra.Cohomology.ResidueLES.Step013_continuous_f1` | 123 | `label:prop-residue-map-long-exact` |
| `contInvA` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 68 | `line:9528` |
| `contInvAEquiv` | `L20261018.Infra.Cohomology.ResidueLES.Step026_invariants_equiv_self` | 59 |  |
| `contInvAEquiv_smul` | `L20261018.Infra.Cohomology.ResidueLES.Step026_invariants_equiv_self` | 70 |  |
| `contInvATopRepIso` | `L20261018.Infra.Cohomology.ResidueLES.Step027_invariants_equiv_self_top_rep` | 50 |  |
| `contInvA_smul_eq_self` | `L20261018.Infra.Cohomology.ResidueLES.Step027_invariants_equiv_self_top_rep` | 42 |  |
| `contInvB` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 72 | `line:9528` |
| `contInvBDescend` | `L20261018.Infra.Cohomology.ResidueLES.Step019_cont_inv_b_descend` | 70 |  |
| `contInvBDescendCoind` | `L20261018.Infra.Cohomology.ResidueLES.Step022_bi_iso_assembly` | 63 |  |
| `contInvBDescendFun` | `L20261018.Infra.Cohomology.ResidueLES.Step019_cont_inv_b_descend` | 39 |  |
| `contInvBDescendFun_add` | `L20261018.Infra.Cohomology.ResidueLES.Step019_cont_inv_b_descend` | 52 |  |
| `contInvBDescendFun_comp_mk` | `L20261018.Infra.Cohomology.ResidueLES.Step019_cont_inv_b_descend` | 46 |  |
| `contInvBDescendFun_injective` | `L20261018.Infra.Cohomology.ResidueLES.Step019_cont_inv_b_descend` | 60 |  |
| `contInvBDescendFun_locallyConstant` | `L20261018.Infra.Cohomology.ResidueLES.Step023_is_locally_constant_descend` | 32 |  |
| `contInvBDescend_apply` | `L20261018.Infra.Cohomology.ResidueLES.Step019_cont_inv_b_descend` | 80 |  |
| `contInvBDescend_comp_coindBotToContInvB` | `L20261018.Infra.Cohomology.ResidueLES.Step021_descend_pull_inverse` | 51 |  |
| `contInvBDescend_injective` | `L20261018.Infra.Cohomology.ResidueLES.Step019_cont_inv_b_descend` | 84 |  |
| `contInvBEquivCoind` | `L20261018.Infra.Cohomology.ResidueLES.Step022_bi_iso_assembly` | 90 |  |
| `contInvBEquivCoindBot` | `L20261018.Infra.Cohomology.ResidueLES.Step023_is_locally_constant_descend` | 62 |  |
| `contInvBEquivCoindBot_smul` | `L20261018.Infra.Cohomology.ResidueLES.Step024_top_rep_iso_coind` | 47 |  |
| `contInvBEquivCoindBot_symm_smul` | `L20261018.Infra.Cohomology.ResidueLES.Step024_top_rep_iso_coind` | 81 |  |
| `contInvBTopRepIso` | `L20261018.Infra.Cohomology.ResidueLES.Step024_top_rep_iso_coind` | 89 |  |
| `contInvB_apply_eq_of_mk_eq` | `L20261018.Infra.Cohomology.ResidueLES.Step018_cont_inv_b_pointwise` | 60 |  |
| `contInvB_lift_wd` | `L20261018.Infra.Cohomology.ResidueLES.Step018_cont_inv_b_pointwise` | 69 |  |
| `contInvC` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 76 | `line:9528` |
| `contInvC_smul_eq_nsmul_val` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 65 |  |
| `contInvIncl` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 80 | `line:9528` |
| `contInvIncl_coe` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 92 | `line:9528` |
| `contInvIncl_equiv_unit` | `L20261018.Infra.Cohomology.ResidueLES.Step029_hk_content_layer` | 54 |  |
| `contInvIncl_injective` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 97 | `line:9528` |
| `contInvIncl_smul` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 106 | `line:9528` |
| `contInvSES` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 147 | `line:9528` |
| `contInvSES_X₂` | `L20261018.Infra.Cohomology.ResidueLES.Step016_delta_t_iso` | 69 |  |
| `contInvSES_delta_one_isIso` | `L20261018.Infra.Cohomology.ResidueLES.Step025_delta_t_iso_usable` | 36 |  |
| `contInvSES_incl` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 165 | `line:9528` |
| `contKI` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 122 | `line:9528` |
| `contKI_le_ker_contProjInv` | `L20261018.Infra.Cohomology.ResidueLES.Step013_continuous_f1` | 103 | `label:prop-residue-map-long-exact` |
| `contKI_map_eq` | `L20261018.Infra.Cohomology.ResidueLES.Step030_right_square_closed` | 45 |  |
| `contKI_stable` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 131 | `line:9528` |
| `contLeibniz_cup01` | `L20261018.Infra.Cohomology.Coinduced.Step038_h0_leibniz` | 93 |  |
| `contLeibniz_cup01_cont` | `L20261018.Infra.Cohomology.Coinduced.Step040_e_zero_surjective_leibniz` | 60 |  |
| `contM` | `L20261018.Infra.Cohomology.Conjugation.Step003_m_body_complete` | 110 |  |
| `contMAddHomS76` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 140 |  |
| `contMAddHomS76_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 147 |  |
| `contMHom` | `L20261018.Infra.Cohomology.Coinduced.Step009_c2_f_interface` | 58 |  |
| `contM_add` | `L20261018.Infra.Cohomology.Coinduced.Step009_c2_f_interface` | 49 |  |
| `contM_coeffMap` | `L20261018.Infra.Cohomology.Coinduced.Step009_c2_f_interface` | 65 |  |
| `contM_coeffMap_explicitCup01` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 187 |  |
| `contM_comp_iota` | `L20261018.Infra.Cohomology.Coinduced.Step019_cont_m_iota_zero` | 74 |  |
| `contM_comp_projI` | `L20261018.Infra.Cohomology.Coinduced.Step019_cont_m_iota_zero` | 62 |  |
| `contM_eq` | `L20261018.Infra.Cohomology.Conjugation.Step003_m_body_complete` | 116 |  |
| `contM_eq_explicitRes1` | `L20261018.Ch2.Hensel.ResidueMap.Step079_cont_m_eq_explicit_res` | 63 |  |
| `contM_eq_res1V_kummerClass` | `L20261018.Ch2.Hensel.ResidueMap.Step079_cont_m_eq_explicit_res` | 82 |  |
| `contM_fixedPointsPairing` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 156 |  |
| `contM_ne_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step080_cont_m_generator` | 70 |  |
| `contM_quotient_smul` | `L20261018.Infra.Cohomology.Conjugation.Step005_gamma_complete` | 114 |  |
| `contM_smul` | `L20261018.Infra.Cohomology.Conjugation.Step003_m_body_complete` | 126 |  |
| `contM_zero` | `L20261018.Infra.Cohomology.Coinduced.Step009_c2_f_interface` | 54 |  |
| `contM_zmultiples_eq_top` | `L20261018.Ch2.Hensel.ResidueMap.Step080_cont_m_generator` | 88 |  |
| `contMapFC_split` | `L20261018.Infra.Cohomology.ResidueLES.Step014_continuous_d_two_blocks` | 111 |  |
| `contPairFC` | `L20261018.Infra.Cohomology.ResidueLES.Step014_continuous_d_two_blocks` | 88 |  |
| `contPairFC_eq` | `L20261018.Infra.Cohomology.ResidueLES.Step014_continuous_d_two_blocks` | 97 |  |
| `contPairITame` | `L20261018.Infra.Cohomology.ResidueLES.Step014_continuous_d_two_blocks` | 71 |  |
| `contPairSubtypeC` | `L20261018.Infra.Cohomology.ResidueLES.Step014_continuous_d_two_blocks` | 78 |  |
| `contProjInv` | `L20261018.Infra.Cohomology.ResidueLES.Step013_continuous_f1` | 67 | `label:prop-residue-map-long-exact` |
| `contProjInv_coe` | `L20261018.Infra.Cohomology.ResidueLES.Step013_continuous_f1` | 84 | `label:prop-residue-map-long-exact` |
| `contProjInv_smul` | `L20261018.Infra.Cohomology.ResidueLES.Step013_continuous_f1` | 89 | `label:prop-residue-map-long-exact` |
| `contT` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 138 | `line:9528` |
| `contTDistribMulAction` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 141 | `line:9528` |
| `contT_equiv_coindQuotient` | `L20261018.Infra.Cohomology.ResidueLES.Step028_t_equiv_coind_quotient` | 51 |  |
| `contT_equiv_coindQuotient'` | `L20261018.Infra.Cohomology.ResidueLES.Step030_right_square_closed` | 63 |  |
| `continuousCup_projection_res_right` | `L20261018.Ch2.Kummer.Step002_projection_formula_continuous` | 54 |  |
| `continuousMulEquivOfBijective` | `L20261018.Ch2.Hensel.Inertia.Step021_inertia_sylow_z_l` | 68 |  |
| `continuousSMul_bot_quotient` | `L20261018.Infra.Cohomology.Coinduced.Step014_coinduced_invariants` | 81 |  |
| `continuousZModDual_wildInertia_subsingleton` | `L20261018.Ch2.Hensel.Inertia.Step023_b1_hom_inertia_mu_p` | 98 |  |
| `continuous_hCoord` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 126 |  |
| `continuous_smul_of_forall_continuous` | `L20261018.Infra.Cohomology.Coinduced.Step027_continuous_smul_criterion` | 39 |  |
| `continuous_smul_of_stabilizer_isOpen` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 45 | `line:8160; line:8163` |
| `corN` | `L20261018.Ch3.NormImage.Step003_norm_image_def` | 31 |  |
| `corollary_4_4` | `L20261018.Ch4.Step005_corollary_four_four_dimension` | 86 | `line:1646` |
| `corollary_4_4_F` | `L20261018.Ch2.Hensel.ResidueMap.Step040_ker_v_finrank_le_one` | 135 | `line:1648` |
| `corollary_4_4_F_of_hK1` | `L20261018.Witness.Step037_f7t_hval_and_corollary` | 65 |  |
| `corollary_4_4_contradiction` | `L20261018.Ch4.Step005_corollary_four_four_dimension` | 101 | `line:1646` |
| `corollary_4_4_contradiction_uncond` | `L20261018.Ch4.Step008_rank_contradiction_single_phi` | 125 | `line:1646` |
| `corollary_4_4_contradiction_uncond'` | `L20261018.Ch4.Step009_dk_eq_one_is_a_theorem` | 155 | `line:1646` |
| `corollary_4_4_general` | `L20261018.Ch4.Step036_ch4_three_without_finite_residue` | 106 |  |
| `corollary_4_4_noBridge` | `L20261018.Ch4.Step033_ch4_three_and_exists_d` | 148 | `line:1050; line:1608; line:1636; line:1648` |
| `corollary_4_4_noFinite` | `L20261018.Ch2.Hensel.ResidueMap.Step036_residue_cup_product_interface` | 136 | `label:lemma-residue-cup-product; line:1608; line:1636; line:1648` |
| `corollary_4_4_of_D` | `L20261018.Ch4.Step016_corollary_four_four_sec_2_4_only` | 72 | `line:1648` |
| `corollary_4_4_of_D_free` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 204 | `line:1636; line:1648` |
| `corollary_4_4_of_discrete_valuation` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 229 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `corollary_4_4_of_discrete_valuation'` | `L20261018.Ch4.Step031_ch4_closed_units_cup_vanish` | 111 | `line:1608; line:1636; line:1648` |
| `corollary_4_4_of_discrete_valuation''` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step013_exists_d_and_ch4_unconditional` | 108 |  |
| `corollary_4_4_of_merkurjevSuslin` | `L20261018.Ch4.Step039_ch4_four_without_finite_residue` | 143 | `line:1050; line:1608; line:1636; line:1648` |
| `corollary_4_4_of_residue_facts` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 377 | `line:1050; line:1608; line:1636; line:1648` |
| `corollary_4_4_paper` | `L20261018.Ch4.Step040_corollary_four_four_paper_level` | 55 | `line:1646` |
| `corollary_4_4_uncond` | `L20261018.Ch4.Step007_corollary_four_four_no_d` | 97 | `line:1646` |
| `corollary_4_4_uncond'` | `L20261018.Ch4.Step009_dk_eq_one_is_a_theorem` | 97 | `line:1646` |
| `corollary_4_4_viaResidue` | `L20261018.Ch4.Step047_ch4_three_d_free` | 174 | `line:1608; line:1636; line:1648` |
| `cosRep` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 45 |  |
| `cosRep_mul_hCoord` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 52 |  |
| `crossedProductClass_cYC'` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 214 |  |
| `crossedProductClass_eq_one_of_eq_bot` | `L20261018.Ch2.Brauer.Step004_degenerate_crossed_product_trivial` | 85 |  |
| `crossedProductClass_eq_one_of_subsingleton_aut` | `L20261018.Ch2.Brauer.Step004_degenerate_crossed_product_trivial` | 50 |  |
| `crossedProductClass_rootSet_eq_one` | `L20261018.Ch2.Brauer.Step004_degenerate_crossed_product_trivial` | 97 |  |
| `cup` | `L20261018.Core.Step001_bi_kummer_data` | 667 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `cup01C` | `L20261018.Ch2.Hensel.ResidueMap.Step074_delta_two_pi_cup_inf` | 63 |  |
| `cup11A` | `L20261018.Ch2.Hensel.ResidueMap.Step074_delta_two_pi_cup_inf` | 70 |  |
| `cup11A_eq_e2_cupLin` | `L20261018.Ch2.Hensel.ResidueMap.Step081_explicit_cup01` | 115 |  |
| `cupCanon` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 159 |  |
| `cupFp_coeffMap_eq_cup` | `L20261018.Ch2.Kummer.Step011_cup_fp_eq_galo_cup_equiv` | 52 |  |
| `cupFp_kummerClass_eq_zero_of_add_eq_one` | `L20261018.Ch2.Kummer.Step051_cup_steinberg_relation` | 79 |  |
| `cupFp_ne_zero_of_localSymbol_ne_zero` | `L20261018.Witness.Step002_nonzero_local_symbol_reduction` | 67 |  |
| `cupFp_unit_unit_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step011_cup_fp_unit_unit_eq_zero` | 8 |  |
| `cupH` | `L20261018.Ch2.Kummer.Step003_triple_cup_product` | 54 |  |
| `cupK` | `L20261018.Ch2.Hensel.ResidueMap.Step060_h_kappa_h2_zero` | 89 |  |
| `cupLC` | `L20261018.Ch2.Hensel.TameSymbol.Step012_tame_symbol_finsupp` | 57 |  |
| `cupLin` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 101 | `label:thm:hs-tate-exact-sequences` |
| `cupLin_apply` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 112 | `label:thm:hs-tate-exact-sequences` |
| `cupLin_skew` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 148 | `label:thm:hs-tate-exact-sequences` |
| `cupPi` | `L20261018.Ch2.Hensel.ResidueMap.Step021_res_and_tame_u_pi_discharged` | 31 |  |
| `cupPiLin` | `L20261018.Ch2.Hensel.ResidueMap.Step069_hcup_injectivity` | 72 |  |
| `cupPi_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step021_res_and_tame_u_pi_discharged` | 38 |  |
| `cupRes` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 153 |  |
| `cup_a1_a1` | `L20261018.Core.Step001_bi_kummer_data` | 60 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `cup_a2_a1` | `L20261018.Core.Step001_bi_kummer_data` | 64 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `cup_a2_a2` | `L20261018.Core.Step001_bi_kummer_data` | 62 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `cup_basis_change` | `L20261018.Ch4.Step001_basis_change_first_slot` | 70 | `label:lem:basis-change` |
| `cup_bridgeKc_of_add_eq_one` | `L20261018.Ch2.Kummer.Step051_cup_steinberg_relation` | 94 |  |
| `cup_bridgeKc_unit_unit_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step012_bridge_kc_unit_cup_zero` | 37 | `label:prop:prelim-residue` |
| `cup_compat_muP` | `L20261018.Ch2.Kummer.Step023_cup_compatible_mu_p` | 34 |  |
| `cup_compat_muP_zmod` | `L20261018.Ch4.Step006_thm_ramified_no_d` | 82 | `label:thm:ramified` |
| `cup_compat_muP_zmod_free` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 37 | `line:1636; line:1648` |
| `cup_compat_muP_zmod_lc` | `L20261018.Ch2.Kummer.Step041_theta_bridge_true_hypothesis` | 43 |  |
| `cup_compat_statement` | `L20261018.Ch2.Kummer.Step011_cup_fp_eq_galo_cup_equiv` | 69 |  |
| `cup_compat_theta` | `L20261018.Ch4.Step006_thm_ramified_no_d` | 96 | `label:thm:ramified` |
| `cup_compat_theta_F` | `L20261018.Ch2.Kummer.Step041_theta_bridge_true_hypothesis` | 88 |  |
| `cup_compat_theta_free` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 74 | `line:1636; line:1648` |
| `cup_compat_theta_locallyCompact` | `L20261018.Ch2.Kummer.Step041_theta_bridge_true_hypothesis` | 54 |  |
| `cup_eq_zero_iff_mem_normGroup_of_bridge` | `L20261018.Ch2.Hensel.Valuation.Step003_r1_norm_form` | 69 |  |
| `cup_eq_zero_iff_mem_normGroup_of_scaled_bridge` | `L20261018.Ch2.Hensel.ResidueMap.Step030_r1_scaled_bridge` | 63 |  |
| `cup_eq_zero_iff_redequiv` | `L20261018.Ch2.Hensel.Valuation.Step003_r1_norm_form` | 52 |  |
| `cup_eq_zero_of_left_mem_span` | `L20261018.Ch2.Hensel.ResidueMap.Step013_huu_reduced_to_linear_dependence` | 44 | `label:prop:prelim-residue` |
| `cup_eq_zero_of_mem_orth` | `L20261018.Ch4.Step012_ramified_vanishing_paper_route` | 42 | `line:1608` |
| `cup_eq_zero_of_mem_orth_free` | `L20261018.Ch4.Step014_ramified_vanishing_hensel_level` | 108 | `line:1608` |
| `cup_eq_zero_of_right_mem_span` | `L20261018.Ch2.Hensel.ResidueMap.Step013_huu_reduced_to_linear_dependence` | 51 | `label:prop:prelim-residue` |
| `cup_kummerClass_ne_zero` | `L20261018.Ch4.Step006_thm_ramified_no_d` | 155 | `label:thm:ramified` |
| `cup_kummerClass_ne_zero_free` | `L20261018.Ch4.Step018_single_carrier_thm_ramified` | 27 | `line:1636; line:1637` |
| `cup_kummerClass_ne_zero_of_localSymbol_ne_zero` | `L20261018.Witness.Step002_nonzero_local_symbol_reduction` | 56 |  |
| `cup_kummerClass_of_add_eq_one` | `L20261018.Ch2.Kummer.Step051_cup_steinberg_relation` | 149 |  |
| `cup_kummerClass_oneSub_eq_zero` | `L20261018.Ch2.Kummer.Step051_cup_steinberg_relation` | 189 |  |
| `cup_kummerClass_unit_eq_zero_of_norm` | `L20261018.Ch4.Step030_unramified_decomposition_algebraic` | 142 |  |
| `cup_kummerClass_unit_eq_zero_of_norm_pow` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step002_units_cup_vanish_reduction` | 99 |  |
| `cup_kummerClass_unit_eq_zero_of_powClassGen'` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step003_norm_group_adjoin_root` | 118 |  |
| `cup_mem_residueSpan` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 86 | `line:1050; line:1608; line:1636; line:1648` |
| `cup_ne_zero_of_localSymbol_ne_zero` | `L20261018.Witness.Step002_nonzero_local_symbol_reduction` | 50 |  |
| `cup_pi_pi_eq_zero` | `L20261018.Ch2.Hensel.TameSymbol.Step001_tame_symbol_general_formula` | 51 | `label:eq:prelim-tame` |
| `cup_self` | `L20261018.Ch2.Hensel.ResidueMap.Step013_huu_reduced_to_linear_dependence` | 33 | `label:prop:prelim-residue` |
| `cup_self_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step055_r2_exact_boundary` | 67 |  |
| `cup_self_free` | `L20261018.Ch4.Step014_ramified_vanishing_hensel_level` | 43 | `line:1608` |
| `cup_skew` | `L20261018.Core.Step001_bi_kummer_data` | 680 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `cup_smul_left` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 78 | `label:thm:hs-tate-exact-sequences` |
| `cup_smul_right` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 90 | `label:thm:hs-tate-exact-sequences` |
| `cup_smul_smul` | `L20261018.Ch2.Kummer.Step051_cup_steinberg_relation` | 133 |  |
| `cup_sum_sum` | `L20261018.Ch4.Step001_basis_change_first_slot` | 52 | `label:lem:basis-change` |
| `cup_unit_eq_zero_of_pow` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step005_units_cup_vanish_final_form` | 69 |  |
| `cup_unit_eq_zero_of_powClassGen` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step005_units_cup_vanish_final_form` | 80 |  |
| `cup_unit_unit_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step010_cup_unit_unit_eq_zero` | 11 |  |
| `cyclesMap_one_comp_homologyπ` | `L20261018.Infra.Cohomology.Boundary.Step025_inner_conj_trivial_in_discharged` | 93 |  |
| `cyclesMap_one_sub_eq_toCycles` | `L20261018.Infra.Cohomology.Boundary.Step025_inner_conj_trivial_in_discharged` | 57 |  |
| `d1_sub_apply` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step029_first_segment_exactness` | 54 |  |
| `d1_tgLift_fst` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step023_partial_y_coset_dependence` | 68 |  |
| `d1_tgLift_h_mem` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step023_partial_y_coset_dependence` | 57 |  |
| `d1_tgLift_mem_fixed` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step024_partial_y_ah_valued` | 42 |  |
| `d1_tgLift_quot_compat` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step026_partial_y_descent` | 41 |  |
| `d1_tgLift_snd` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step023_partial_y_coset_dependence` | 47 |  |
| `d1_z_h_zero` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step025_descent_lemma_well_defined` | 42 |  |
| `d2` | `L20261018.Ch3.NormImage.Step002_five_term_mg_k2_data` | 30 |  |
| `d2'` | `L20261018.Ch3.NormImage.Step005_three_five_one_first_ses` | 36 | `label:thm:hs-tate-exact-sequences` |
| `d2'_ker` | `L20261018.Ch3.NormImage.Step005_three_five_one_first_ses` | 42 | `label:thm:hs-tate-exact-sequences` |
| `d2'_range` | `L20261018.Ch3.NormImage.Step005_three_five_one_first_ses` | 46 | `label:thm:hs-tate-exact-sequences` |
| `dPartial` | `L20261018.Ch2.Hensel.ResidueMap.Step051_h1_z_equiv_galo_v` | 149 | `line:1050` |
| `dPartialLin` | `L20261018.Ch2.Hensel.ResidueMap.Step051_h1_z_equiv_galo_v` | 157 | `line:1050` |
| `dPartialLin_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step051_h1_z_equiv_galo_v` | 162 | `line:1050` |
| `dPartialLin_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 176 |  |
| `dPartial_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 168 |  |
| `d_F5` | `L20261018.Ch2.Hensel.ResidueMap.Step064_delta_two_definition` | 63 |  |
| `d_one_two_apply` | `L20261018.Infra.Cohomology.Boundary.Step022_coboundary_explicit_fin` | 61 |  |
| `d_zero_one_apply` | `L20261018.Infra.Cohomology.Boundary.Step022_coboundary_explicit_fin` | 52 |  |
| `decompQuotEquivRange` | `L20261018.Ch2.Hensel.Inertia.Step001_inertia_exact_sequence_first` | 53 |  |
| `decompQuotToResidue_injective` | `L20261018.Ch2.Hensel.Inertia.Step001_inertia_exact_sequence_first` | 58 |  |
| `decompToResidue` | `L20261018.Ch2.Hensel.Inertia.Step001_inertia_exact_sequence_first` | 47 |  |
| `decomp_mem_ker` | `L20261018.Ch2.Hensel.ResidueMap.Step005_residue_cup_data_fields_reduced` | 49 | `label:lem:ramified-vanishing` |
| `deg_crossedProduct` | `L20261018.Ch2.Brauer.Step001_index_le_degree` | 45 |  |
| `degreeZeroClass_congr` | `L20261018.Infra.Cohomology.Conjugation.Step003_m_body_complete` | 55 |  |
| `deltaAddEquivOfSub` | `L20261018.Infra.Cohomology.Coinduced.Step025_square_elimination` | 53 |  |
| `deltaAddEquivOfSub_apply` | `L20261018.Infra.Cohomology.Coinduced.Step025_square_elimination` | 64 |  |
| `deltaAddEquiv_of_subsingleton` | `L20261018.Infra.Cohomology.Boundary.Step026_dimension_shift_from_long_exact` | 120 |  |
| `deltaAddEquiv_sesCoind1` | `L20261018.Infra.Cohomology.Coinduced.Step017_ses1_delta_one_iso` | 101 |  |
| `deltaAddEquiv_sesCoind1_witness` | `L20261018.Infra.Cohomology.Coinduced.Step017_ses1_delta_one_iso` | 137 |  |
| `deltaShift1` | `L20261018.Infra.Cohomology.Coinduced.Step008_delta_two_first_factors` | 62 |  |
| `deltaShift1_delta` | `L20261018.Ch2.Hensel.ResidueMap.Step071_delta_two_expansion` | 60 |  |
| `deltaShift1_eq_deltaAddEquivOfSub` | `L20261018.Infra.Cohomology.Coinduced.Step026_delta_two_inf_two_zero` | 119 |  |
| `deltaShift1_injective` | `L20261018.Ch2.Hensel.ResidueMap.Step072_delta_two_factors_bijective` | 57 |  |
| `deltaShift1_surjective` | `L20261018.Ch2.Hensel.ResidueMap.Step072_delta_two_factors_bijective` | 62 |  |
| `deltaTwo` | `L20261018.Infra.Cohomology.Boundary.Step018_delta_two_conditional` | 105 | `line:9498` |
| `deltaTwoCarrier` | `L20261018.Infra.Cohomology.Coinduced.Step010_delta_two_carrier_assembly` | 41 |  |
| `deltaTwoCarrierInertia` | `L20261018.Infra.Cohomology.Coinduced.Step011_hc_inertia_discharged` | 69 |  |
| `deltaTwoCarrierInertia_comp_infl_eq_zero` | `L20261018.Infra.Cohomology.Coinduced.Step028_delta_two_carrier_inertia` | 54 |  |
| `deltaTwoCarrierInertia_cup_eq` | `L20261018.Ch2.Hensel.ResidueMap.Step074_delta_two_pi_cup_inf` | 145 |  |
| `deltaTwoCarrierInertia_cup_eq_value` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 249 |  |
| `deltaTwoCarrierInertia_injective_of_contM_injective` | `L20261018.Ch2.Hensel.ResidueMap.Step073_delta_two_injective_reduction` | 46 |  |
| `deltaTwoCarrierInertia_map_pair_id_eq_zero` | `L20261018.Infra.Cohomology.Coinduced.Step034_delta_two_map_phi_zero` | 45 |  |
| `deltaTwoFree` | `L20261018.Infra.Cohomology.Boundary.Step025_inner_conj_trivial_in_discharged` | 137 |  |
| `deltaTwoFree_type_lock` | `L20261018.Infra.Cohomology.Boundary.Step025_inner_conj_trivial_in_discharged` | 144 |  |
| `deltaTwoGaloBase'` | `L20261018.Infra.Cohomology.Coinduced.Step035_delta_two_cup_y_z_zero` | 59 |  |
| `deltaTwoGaloBase'_apply` | `L20261018.Infra.Cohomology.Coinduced.Step035_delta_two_cup_y_z_zero` | 67 |  |
| `deltaTwoGaloBase'_cup_eq_neg_explicitCup01` | `L20261018.Ch2.Hensel.ResidueMap.Step081_explicit_cup01` | 138 |  |
| `deltaTwoGaloBase'_cup_eq_zero` | `L20261018.Infra.Cohomology.Coinduced.Step035_delta_two_cup_y_z_zero` | 116 |  |
| `deltaTwoGaloBase'_cup_eq_zero'` | `L20261018.Ch4.Step042_hd_infl_final_form` | 63 |  |
| `deltaTwoGaloBase'_h2ToGaloBase` | `L20261018.Infra.Cohomology.Coinduced.Step035_delta_two_cup_y_z_zero` | 76 |  |
| `deltaTwoGaloBase'_infl2Res_eq_zero` | `L20261018.Infra.Cohomology.Coinduced.Step035_delta_two_cup_y_z_zero` | 91 |  |
| `deltaTwoGaloBase'_injective_of_contM_injective` | `L20261018.Ch2.Hensel.ResidueMap.Step073_delta_two_injective_reduction` | 62 |  |
| `deltaTwoShift` | `L20261018.Infra.Cohomology.Coinduced.Step008_delta_two_first_factors` | 97 |  |
| `deltaTwoShift_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step071_delta_two_expansion` | 78 |  |
| `deltaTwoShift_comp_infl_eq_zero` | `L20261018.Infra.Cohomology.Coinduced.Step026_delta_two_inf_two_zero` | 143 |  |
| `deltaTwoShift_eq_iff` | `L20261018.Ch2.Hensel.ResidueMap.Step072_delta_two_factors_bijective` | 80 |  |
| `deltaTwoShift_eq_of_delta_eq` | `L20261018.Ch2.Hensel.ResidueMap.Step071_delta_two_expansion` | 93 |  |
| `deltaTwoShift_injective` | `L20261018.Ch2.Hensel.ResidueMap.Step072_delta_two_factors_bijective` | 70 |  |
| `deltaTwoShift_surjective` | `L20261018.Ch2.Hensel.ResidueMap.Step072_delta_two_factors_bijective` | 75 |  |
| `deltaTwo_eq` | `L20261018.Infra.Cohomology.Boundary.Step018_delta_two_conditional` | 114 | `line:9498` |
| `deltaTwo_firstHalf` | `L20261018.Infra.Cohomology.Boundary.Step008_delta_two_inflation_iso` | 76 |  |
| `deltaTwo_firstHalf'_hom_eq` | `L20261018.Infra.Cohomology.ResidueLES.Step005_delta_two_comp_inf_zero` | 55 |  |
| `deltaTwo_firstHalf'_of_h2` | `L20261018.Infra.Cohomology.Boundary.Step034_hcd_empty_hypothesis` | 78 |  |
| `deltaTwo_minimal` | `L20261018.Infra.Cohomology.Boundary.Step035_delta_two_hypotheses_cleared` | 92 |  |
| `deltaTwo_minimal_comp_inflation` | `L20261018.Infra.Cohomology.ResidueLES.Step005_delta_two_comp_inf_zero` | 106 |  |
| `deltaTwo_minimal_consumes_hcd` | `L20261018.Infra.Cohomology.Boundary.Step035_delta_two_hypotheses_cleared` | 129 |  |
| `deltaTwo_minimal_eq` | `L20261018.Infra.Cohomology.Boundary.Step035_delta_two_hypotheses_cleared` | 101 |  |
| `deltaTwo_minimal_target_V` | `L20261018.Infra.Cohomology.Boundary.Step035_delta_two_hypotheses_cleared` | 120 |  |
| `deltaTwo_minimal_type_lock` | `L20261018.Infra.Cohomology.Boundary.Step035_delta_two_hypotheses_cleared` | 113 |  |
| `deltaTwo_type_lock` | `L20261018.Infra.Cohomology.Boundary.Step018_delta_two_conditional` | 124 | `line:9498` |
| `deltaZeroBar` | `L20261018.Infra.Cohomology.Boundary.Step018_delta_two_conditional` | 78 | `line:9498` |
| `deltaZero_coindBot` | `L20261018.Infra.Cohomology.Boundary.Step009_delta_two_third_segment` | 47 |  |
| `deltaZero_coindBot_comp_coind` | `L20261018.Infra.Cohomology.ResidueLES.Step001_f2_delta_zero_vanishes` | 89 | `label:prop-residue-map-long-exact` |
| `deltaZero_coindBot_eq` | `L20261018.Infra.Cohomology.Boundary.Step009_delta_two_third_segment` | 53 |  |
| `deltaZero_coindBot_eq_δ` | `L20261018.Infra.Cohomology.ResidueLES.Step001_f2_delta_zero_vanishes` | 96 | `label:prop-residue-map-long-exact` |
| `deltaZero_conj` | `L20261018.Infra.Cohomology.Boundary.Step016_delta_zero_naturality` | 146 | `line:3585` |
| `delta_bijective_of_subsingleton` | `L20261018.Infra.Cohomology.Boundary.Step026_dimension_shift_from_long_exact` | 111 |  |
| `delta_bijective_of_subsingleton_witness` | `L20261018.Infra.Cohomology.Boundary.Step026_dimension_shift_from_long_exact` | 138 |  |
| `delta_bijective_sesCoind1` | `L20261018.Infra.Cohomology.Coinduced.Step017_ses1_delta_one_iso` | 87 |  |
| `delta_coind_comp_infl` | `L20261018.Infra.Cohomology.ResidueLES.Step003_f1_square` | 119 | `label:prop-residue-map-long-exact` |
| `delta_coind_comp_infl'` | `L20261018.Infra.Cohomology.ResidueLES.Step005_delta_two_comp_inf_zero` | 76 |  |
| `delta_deltaShift1` | `L20261018.Ch2.Hensel.ResidueMap.Step071_delta_two_expansion` | 68 |  |
| `delta_dimShiftUpSES_eq` | `L20261018.Infra.Cohomology.ResidueLES.Step003_f1_square` | 84 | `label:prop-residue-map-long-exact` |
| `delta_injective_of_subsingleton` | `L20261018.Infra.Cohomology.Boundary.Step026_dimension_shift_from_long_exact` | 77 |  |
| `delta_injective_sesCoind1` | `L20261018.Infra.Cohomology.Coinduced.Step017_ses1_delta_one_iso` | 54 |  |
| `delta_inv_comp_infl_eq` | `L20261018.Infra.Cohomology.Coinduced.Step025_square_elimination` | 79 |  |
| `delta_map_quotient_T` | `L20261018.Infra.Cohomology.Coinduced.Step015_gs617_compatibility_square` | 63 |  |
| `delta_sesCoind1_apply_symm` | `L20261018.Infra.Cohomology.Coinduced.Step017_ses1_delta_one_iso` | 115 |  |
| `delta_surjective_of_subsingleton` | `L20261018.Infra.Cohomology.Boundary.Step026_dimension_shift_from_long_exact` | 95 |  |
| `delta_surjective_sesCoind1` | `L20261018.Infra.Cohomology.Coinduced.Step017_ses1_delta_one_iso` | 71 |  |
| `delta_zero_comp_projRestrCoeff` | `L20261018.Infra.Cohomology.Coinduced.Step019_cont_m_iota_zero` | 47 |  |
| `delta_zero_conjNormal` | `L20261018.Infra.Cohomology.Coinduced.Step007_delta_zero_quotient_morphism` | 68 |  |
| `delta_zero_quotientConj` | `L20261018.Infra.Cohomology.Coinduced.Step007_delta_zero_quotient_morphism` | 81 |  |
| `derivative_henselPoly` | `L20261018.Witness.Step026_f7t_principal_units_cube` | 58 |  |
| `det_mulRight_inc` | `L20261018.Ch2.Brauer.Step002_reduced_norm_maximal_subfield` | 71 |  |
| `diagonal_mul_Ymat` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 90 |  |
| `dimShiftAdd` | `L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive` | 96 |  |
| `dimShiftEquiv` | `L20261018.Infra.Cohomology.Step006_rv_complex_assembly` | 76 |  |
| `dimShiftEquiv_injective` | `L20261018.Infra.Cohomology.Step006_rv_complex_assembly` | 83 |  |
| `dimShiftSES` | `L20261018.Infra.Cohomology.ResidueLES.Step001_f2_delta_zero_vanishes` | 73 | `label:prop-residue-map-long-exact` |
| `dimShiftSES_S` | `L20261018.Infra.Cohomology.Boundary.Step016_delta_zero_naturality` | 70 | `line:3585` |
| `dimShiftSES_S_eq` | `L20261018.Infra.Cohomology.Boundary.Step016_delta_zero_naturality` | 80 | `line:3585` |
| `dimShiftSES_X₁` | `L20261018.Infra.Cohomology.ResidueLES.Step001_f2_delta_zero_vanishes` | 77 | `label:prop-residue-map-long-exact` |
| `dimShiftSES_X₃` | `L20261018.Infra.Cohomology.ResidueLES.Step001_f2_delta_zero_vanishes` | 83 | `label:prop-residue-map-long-exact` |
| `disjoint_iff_exists_residueMap` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step016_b_pinned_to_equivalence` | 127 |  |
| `disjoint_iff_forall` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step018_b_logical_tension` | 61 |  |
| `disjoint_of_dependent` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step017_one_dimensionality_is_the_engine` | 76 |  |
| `disjoint_of_exists_residueMap` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step016_b_pinned_to_equivalence` | 60 |  |
| `disjoint_of_faithfulR2` | `L20261018.Ch2.Hensel.ResidueMap.Step042_residue_span_subset_ker_res` | 127 |  |
| `disjoint_of_residueSpan_eq_bot` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step016_b_pinned_to_equivalence` | 102 |  |
| `disjoint_range_residuePhi` | `L20261018.Ch2.Hensel.ResidueMap.Step042_residue_span_subset_ker_res` | 87 |  |
| `disjoint_viaResidue` | `L20261018.Witness.Step040_tame_symbol_hyp_witness` | 100 |  |
| `divisionRep` | `L20261018.Ch2.Brauer.Step029_index_function_h2` | 71 |  |
| `downCLM` | `L20261018.Ch2.Kummer.Step010_cup_fp_eq_galo_cup` | 44 |  |
| `downHom` | `L20261018.Ch2.Kummer.Step032_t1_bridge_same_shape` | 84 |  |
| `down_intertwining` | `L20261018.Ch2.Kummer.Step010_cup_fp_eq_galo_cup` | 56 |  |
| `e` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 55 |  |
| `e0_res_infl` | `L20261018.Ch2.Hensel.ResidueMap.Step078_res_inertia_infl_image` | 88 |  |
| `e1_explicitRes1` | `L20261018.Ch2.Hensel.ResidueMap.Step076_res_bridges_explicit_continuous` | 51 |  |
| `eCoeffHom` | `L20261018.Ch2.Kummer.Step027_t1_mu_n_rep_factorization` | 92 |  |
| `eDouble` | `L20261018.Ch2.Kummer.Step025_t1_reduction_factor_separation` | 44 |  |
| `eDoubleHom` | `L20261018.Ch2.Kummer.Step027_t1_mu_n_rep_factorization` | 99 |  |
| `eDouble_comp_eq_kce` | `L20261018.Ch2.Kummer.Step026_t1_coefficient_iso_composition` | 36 |  |
| `eQ` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 136 |  |
| `eQ2` | `L20261018.Infra.Cohomology.Coinduced.Step029_second_carrier_square` | 52 |  |
| `eQ_apply` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 142 |  |
| `e_alpha_pow` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 225 |  |
| `e_autCongr_apply` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 75 |  |
| `eigenvalue_relation` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 122 |  |
| `elementary_henselData` | `L20261018.Ch4.Step022_d_residue_field` | 94 |  |
| `emb` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 49 |  |
| `epi_contCoindSES_delta` | `L20261018.Infra.Cohomology.ResidueLES.Step014_continuous_d_two_blocks` | 64 |  |
| `epi_contInvSES_delta` | `L20261018.Infra.Cohomology.ResidueLES.Step016_delta_t_iso` | 59 |  |
| `epi_contInvSES_delta_inertia_one` | `L20261018.Infra.Cohomology.ResidueLES.Step025_delta_t_iso_usable` | 63 |  |
| `epi_contInvSES_delta_one` | `L20261018.Infra.Cohomology.ResidueLES.Step025_delta_t_iso_usable` | 41 |  |
| `epi_contInvSES_delta_uncond` | `L20261018.Infra.Cohomology.ResidueLES.Step025_delta_t_iso_usable` | 30 |  |
| `epi_deltaZero_coindBot` | `L20261018.Infra.Cohomology.Boundary.Step009_delta_two_third_segment` | 59 |  |
| `epi_δ_cokerSES` | `L20261018.Infra.Cohomology.ResidueLES.Step005_delta_two_comp_inf_zero` | 70 |  |
| `eq_oneSub_of_add_eq_one` | `L20261018.Ch2.Hensel.TameSymbol.Step015_tame_symbol_hyp_from_merkurjev_suslin` | 143 |  |
| `eq_one_of_pow_eq_one` | `L20261018.Ch2.Hensel.Valuation.Step037_nu_pth_root_zero` | 57 |  |
| `eq_one_of_pow_eq_one_of_residueUnits_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step033_inertia_fixed_unit_pth_root` | 132 |  |
| `eq_one_of_sq_mul_finrank_eq` | `L20261018.Ch2.Brauer.Step008_matrix_elimination_degree` | 101 |  |
| `equivInertiaLocInertia` | `L20261018.Ch2.Hensel.Inertia.Step024_hom_inertia_tame` | 213 |  |
| `equivTameInertia` | `L20261018.Ch2.Hensel.Inertia.Step024_hom_inertia_tame` | 199 |  |
| `equivTameModelInertia` | `L20261018.Ch2.Hensel.Inertia.Step025_h1_inertia_finite` | 108 |  |
| `eval_zero_henselPoly` | `L20261018.Witness.Step026_f7t_principal_units_cube` | 53 |  |
| `exact_infl_val` | `L20261018.Ch2.Hensel.ResidueMap.Step033_residue_sequence_exact_split` | 53 | `label:prop:prelim-residue` |
| `exists_basis_val_eq` | `L20261018.Ch4.Step013_basis_selection_u` | 44 | `line:1596` |
| `exists_coeff_adjoinRoot` | `L20261018.Ch2.Hensel.Valuation.Step012_coordinate_decomposition` | 34 |  |
| `exists_coeff_of_norm_mem_integer` | `L20261018.Ch2.Hensel.Valuation.Step029_integrality_criterion` | 54 |  |
| `exists_cupFp_ne_zero` | `L20261018.Witness.Step003_nondegenerate_nonzero_cup` | 113 |  |
| `exists_cupFp_ne_zero_of_notMem_powerSubgroup` | `L20261018.Witness.Step003_nondegenerate_nonzero_cup` | 54 |  |
| `exists_cup_pi_ne_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step020_cup_pi_nonzero_injective` | 35 |  |
| `exists_decomp` | `L20261018.Ch2.Hensel.ResidueMap.Step004_valuation_decomposition_unique` | 81 | `label:prop:prelim-kummer-valuation` |
| `exists_decomp_linear` | `L20261018.Ch2.Hensel.ResidueMap.Step004_valuation_decomposition_unique` | 43 | `label:prop:prelim-kummer-valuation` |
| `exists_decomp_of_sup_eq_top` | `L20261018.Core.Step001_bi_kummer_data` | 217 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `exists_dvd_sub_mul` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step010_bezout_arithmetic_core` | 43 |  |
| `exists_galoCup_ne_zero_Q7` | `L20261018.Witness.Step012_q7_exists_nonzero_cup` | 66 |  |
| `exists_generator_primeToPTateModule` | `L20261018.Ch2.Hensel.Inertia.Step017_tame_module_procyclic` | 57 | `line:8` |
| `exists_henselResidueData` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step013_exists_d_and_ch4_unconditional` | 40 |  |
| `exists_henselResidueData_noBridge` | `L20261018.Ch4.Step033_ch4_three_and_exists_d` | 82 | `line:1050; line:1608; line:1636; line:1648` |
| `exists_henselResidueData_noFinite` | `L20261018.Ch2.Hensel.ResidueMap.Step035_hens_residue_data_no_finite` | 21 |  |
| `exists_henselResidueData_noFinite'` | `L20261018.Ch2.Hensel.ResidueMap.Step036_residue_cup_product_interface` | 179 | `label:lemma-residue-cup-product; line:1608; line:1636; line:1648` |
| `exists_henselResidueData_of_le_range` | `L20261018.Ch4.Step027_residue_span_bot_skeleton` | 86 |  |
| `exists_henselResidueData_of_merkurjevSuslin` | `L20261018.Ch4.Step039_ch4_four_without_finite_residue` | 173 | `line:1050; line:1608; line:1636; line:1648` |
| `exists_henselResidueData_of_norm_form` | `L20261018.Ch4.Step029_r1_two_carriers_wired` | 184 |  |
| `exists_henselResidueData_of_residueMap` | `L20261018.Ch4.Step035_exists_d_no_finite_residue` | 37 |  |
| `exists_henselResidueData_of_unitsCupVanish` | `L20261018.Ch2.Hensel.ResidueMap.Step041_residue_map_single_hypothesis` | 115 | `line:1023` |
| `exists_henselResidueData_of_units_cup` | `L20261018.Ch4.Step030_unramified_decomposition_algebraic` | 215 |  |
| `exists_henselResidueData_uncond` | `L20261018.Ch4.Step032_v_and_d_exists` | 55 |  |
| `exists_henselResidueData_uncond_noBridge` | `L20261018.Ch4.Step034_exists_d_unconditional` | 45 | `label:prop:prelim-residue` |
| `exists_henselResidueData_uncond_noBridge'` | `L20261018.Ch2.Hensel.ResidueMap.Step032_hskew_discharged` | 70 | `label:prop:prelim-residue` |
| `exists_henselResidueData_witness_Q7` | `L20261018.Witness.Step007_l1_witness_q7` | 141 |  |
| `exists_isPrimitiveRoot_integer` | `L20261018.Ch2.Hensel.ResidueMap.Step062_mu_p_residue_full_chain` | 97 |  |
| `exists_isPrimitiveRoot_residue` | `L20261018.Ch2.Hensel.ResidueMap.Step062_mu_p_residue_full_chain` | 125 |  |
| `exists_kummerCor_eq_kummerMap_of_nrd` | `L20261018.Ch3.BiKummer.Step015_h_nrd_kummer_form` | 53 | `label:lem:basic-inclusions` |
| `exists_leftInverse_coeff` | `L20261018.Ch2.Hensel.ResidueMap.Step083_left_inverse_coeff_map` | 66 |  |
| `exists_leftInverse_of_injective` | `L20261018.Ch2.Hensel.ResidueMap.Step069_hcup_injectivity` | 100 |  |
| `exists_localSymbol_ne_zero_of_notMem_powerSubgroup` | `L20261018.Witness.Step003_nondegenerate_nonzero_cup` | 42 |  |
| `exists_mul_uniformizer_of_mem_maximalIdeal` | `L20261018.Ch2.Hensel.Valuation.Step023_maximal_ideal_eq_pi` | 31 |  |
| `exists_ne_zero_VKG_of_quot` | `L20261018.Ch2.Hensel.ResidueMap.Step068_infl_to_vkg_injective` | 81 |  |
| `exists_ne_zero_mem_ker` | `L20261018.Ch4.Step009_dk_eq_one_is_a_theorem` | 34 | `line:1646` |
| `exists_notMem_powerSubgroup` | `L20261018.Witness.Step003_nondegenerate_nonzero_cup` | 104 |  |
| `exists_nrdOfIso_eq_norm` | `L20261018.Ch2.Brauer.Step003_reduced_norm_any_crossed_product` | 72 |  |
| `exists_nrdOfIso_eq_norm_of_mk_eq` | `L20261018.Ch2.Brauer.Step009_h_nrd_from_field_norm_algebra` | 37 |  |
| `exists_nrd_eq_norm_of_algEquiv` | `L20261018.Ch3.BiKummer.Step009_h_nrd_presentation_independent` | 148 |  |
| `exists_num_den` | `L20261018.Ch2.Hensel.Valuation.Step031_val_compat_well_defined` | 36 |  |
| `exists_num_den'` | `L20261018.Ch2.Hensel.Valuation.Step032_val_compat_multiplicative` | 43 |  |
| `exists_pow_eq` | `L20261018.Ch2.Kummer.Step016_zeta_independence_carrier` | 94 |  |
| `exists_pow_eq_algebraMap` | `L20261018.Ch3.BiKummer.Step013_orthogonal_roots_trivial` | 39 | `label:lem:orthogonal` |
| `exists_pow_eq_of_pow_eq_one` | `L20261018.Ch2.Hensel.ResidueMap.Step014_ker_v_one_dim_group_core` | 27 |  |
| `exists_pow_eq_of_residue_eq_one` | `L20261018.Ch2.Hensel.ResidueMap.Step056_kummer_valuation_abstract_hensel` | 91 | `label:prop:prelim-kummer-valuation` |
| `exists_pow_mul_pow_of_isCyclic` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step010_bezout_arithmetic_core` | 69 |  |
| `exists_pow_of_residue_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step011_units_transport_steps` | 70 |  |
| `exists_pow_of_rho_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step012_units_cup_vanish_unconditional` | 49 |  |
| `exists_pow_of_rho_eq_one'` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 92 |  |
| `exists_pow_root_mul_coeff_mem` | `L20261018.Ch2.Hensel.Valuation.Step013_normalization_integral` | 31 |  |
| `exists_pow_root_mul_coeff_mem_sumCoeff` | `L20261018.Ch2.Hensel.Valuation.Step024_normalization_sum_coeff` | 39 |  |
| `exists_primitiveComponents` | `L20261018.Ch2.Hensel.Inertia.Step026_hom_inertia_mu_p_eq_zmod` | 68 |  |
| `exists_primitiveRoot_alg` | `L20261018.Ch2.Hensel.Inertia.Step040_tame_character_galois_invariant` | 62 |  |
| `exists_primitiveRoot_three_Q7` | `L20261018.Witness.Step007_l1_witness_q7` | 88 |  |
| `exists_residueMap` | `L20261018.Ch4.Step046_exists_residue_map` | 323 |  |
| `exists_residueMap_iff_tameResidueFacts` | `L20261018.Ch2.Hensel.ResidueMap.Step037_exists_d_iff_tame_residue_facts` | 44 |  |
| `exists_residueMap_of_dependent` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step017_one_dimensionality_is_the_engine` | 99 |  |
| `exists_residueMap_of_disjoint` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step015_b_reduced_to_disjoint` | 65 |  |
| `exists_residueMap_of_faithfulR2` | `L20261018.Ch2.Hensel.ResidueMap.Step042_residue_span_subset_ker_res` | 149 |  |
| `exists_residueMap_of_finite` | `L20261018.Witness.Step016_d_witness_finite_residue` | 40 | `line:1023` |
| `exists_residueMap_of_finite'` | `L20261018.Ch2.Hensel.ResidueMap.Step041_residue_map_single_hypothesis` | 148 | `line:1023` |
| `exists_residueMap_of_unitsCupVanish` | `L20261018.Ch2.Hensel.ResidueMap.Step041_residue_map_single_hypothesis` | 98 | `line:1023` |
| `exists_root_X_sq_add_X_add_one` | `L20261018.Witness.Step007_l1_witness_q7` | 68 |  |
| `exists_smul_eq_of_finrank_eq_one` | `L20261018.Infra.Algebra.Step003_one_dim_linear_maps_scalar` | 33 |  |
| `exists_smul_eq_of_linearEquiv` | `L20261018.Infra.Algebra.Step003_one_dim_linear_maps_scalar` | 63 |  |
| `exists_smul_kummerCoeffLinearEquiv` | `L20261018.Ch2.Kummer.Step034_hbridge_scalar_source` | 46 |  |
| `exists_tameResidueFacts_of_residueSpan_ne_bot` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 330 | `label:eq:prelim-tame; line:1050` |
| `exists_tgCompat_normalized` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step022_nsw_y_exists` | 71 |  |
| `exists_tgLift` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step022_nsw_y_exists` | 108 |  |
| `exists_tg_partial` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step024_partial_y_ah_valued` | 88 |  |
| `exists_uniformizer_not_pow` | `L20261018.Ch2.Hensel.Valuation.Step035_uniformizer_constructed` | 38 |  |
| `exists_uniformizer_pow_mul_mem_integer` | `L20261018.Ch2.Hensel.Valuation.Step007_integer_clear_denominators` | 37 |  |
| `exists_unique_decomp` | `L20261018.Ch2.Hensel.ResidueMap.Step004_valuation_decomposition_unique` | 92 | `label:prop:prelim-kummer-valuation` |
| `exists_unitOf_of_val_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step011_units_transport_steps` | 51 |  |
| `exists_unit_kummerClass_of_mem_ker` | `L20261018.Infra.Cohomology.ResidueLES.Step015_vkg_kummer_decomposition` | 53 |  |
| `exists_unit_of_valH1Gen_eq_zero` | `L20261018.Ch4.Step030_unramified_decomposition_algebraic` | 91 |  |
| `exists_unit_of_zval_eq_zero` | `L20261018.Witness.Step029_f7t_zval_powers` | 62 |  |
| `exists_unit_pow_eq` | `L20261018.Ch2.Hensel.ResidueMap.Step043_units_mod_pth_powers_paper_level` | 83 | `label:prop:prelim-kummer-valuation; line:992` |
| `exists_unit_rep` | `L20261018.Ch2.Hensel.ResidueMap.Step008_exists_unit_rep` | 34 | `label:prop:prelim-kummer-valuation` |
| `exists_unit_rep_F` | `L20261018.Ch2.Hensel.Valuation.Step036_exists_unit_rep_val_lin` | 52 |  |
| `exists_unit_residue_eq` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step007_units_surject_residue` | 50 |  |
| `exists_unit_rho_eq` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step012_units_cup_vanish_unconditional` | 43 |  |
| `exists_unit_rho_eq'` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 86 |  |
| `exists_valCompat` | `L20261018.Ch2.Hensel.Valuation.Step033_val_compat_exists` | 100 |  |
| `exists_valuationRing_unit_of_val_eq_one` | `L20261018.Ch2.Hensel.Inertia.Step037_unramified_kummer_paper_level` | 71 |  |
| `expEquiv` | `L20261018.Ch2.Brauer.Step013_carry_cocycle_index` | 45 |  |
| `explicitCoeff1_eq_zero_of_apply_eq_zero` | `L20261018.Infra.Cohomology.Coinduced.Step024_explicit_coeff_one_zero` | 53 |  |
| `explicitCoeff1_zero` | `L20261018.Infra.Cohomology.Coinduced.Step024_explicit_coeff_one_zero` | 70 |  |
| `explicitCup01_contM_ne_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step084_explicit_cup01_nonzero` | 64 |  |
| `explicitCup01_ne_zero_of_leftInverse` | `L20261018.Ch2.Hensel.ResidueMap.Step082_explicit_cup_nonzero` | 53 |  |
| `explicitCup11_flip_eq` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 125 | `label:thm:hs-tate-exact-sequences` |
| `explicitCup_projection_res_right` | `L20261018.Ch2.Kummer.Step001_cup_projection_res_right` | 10 |  |
| `explicitH0Iso_conjNormalMap_zero` | `L20261018.Infra.Cohomology.Conjugation.Step003_m_body_complete` | 88 |  |
| `explicitInfl1AddEquiv_of_subsingleton` | `L20261018.Infra.Cohomology.Boundary.Step028_inflation_h1_iso` | 85 |  |
| `explicitInfl1AddEquiv_of_subsingleton_witness` | `L20261018.Infra.Cohomology.Boundary.Step028_inflation_h1_iso` | 119 |  |
| `explicitInfl1_bijective_of_subsingleton` | `L20261018.Infra.Cohomology.Boundary.Step028_inflation_h1_iso` | 79 |  |
| `explicitInfl1_coeffInclH1` | `L20261018.Ch4.Step046_exists_residue_map` | 151 |  |
| `explicitInfl1_eq_comp_coeff` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 255 |  |
| `explicitInfl1_surjective_of_subsingleton` | `L20261018.Infra.Cohomology.Boundary.Step028_inflation_h1_iso` | 64 |  |
| `explicitLeibniz_cup01` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 189 |  |
| `explicitMap1_comp_coeff` | `L20261018.Ch2.Kummer.Step032_t1_bridge_same_shape` | 47 |  |
| `explicitMap1_eq_nsmul` | `L20261018.Ch2.Kummer.Step028_t1_explicit_map1_linear` | 79 |  |
| `explicitMap1_quot_id_eq_infl_comp_coeff` | `L20261018.Infra.Cohomology.Coinduced.Step036_res_h1_type_equiv_vkg` | 111 |  |
| `explicitMap1_quot_id_injective` | `L20261018.Infra.Cohomology.Coinduced.Step036_res_h1_type_equiv_vkg` | 130 |  |
| `explicitMap1_subtype_comp_coeff` | `L20261018.Infra.Cohomology.Coinduced.Step036_res_h1_type_equiv_vkg` | 53 |  |
| `explicitMap2_id_eq_subtype_comp` | `L20261018.Infra.Cohomology.Coinduced.Step031_coefficient_bridge_explicit_model` | 74 |  |
| `explicitMap2_quot_id_eq_subtype_comp` | `L20261018.Infra.Cohomology.Coinduced.Step033_delta_two_infl_zero_carrier` | 64 |  |
| `explicitMap2_quot_subtype_eq_comp` | `L20261018.Infra.Cohomology.Coinduced.Step032_a1_last_step` | 35 |  |
| `explicitMap2_subtype_comp_coeff` | `L20261018.Infra.Cohomology.Coinduced.Step033_delta_two_infl_zero_carrier` | 43 |  |
| `explicitRes0_explicitInfl0` | `L20261018.Ch2.Hensel.ResidueMap.Step078_res_inertia_infl_image` | 62 |  |
| `explicitRes1_explicitCoeff1Equiv_comp` | `L20261018.Ch2.Hensel.Inertia.Step034_inertia_restriction_res1` | 67 |  |
| `explicitRes1_explicitMap1_id` | `L20261018.Ch3.BiKummer.Step007_restriction_coefficient_change` | 30 |  |
| `explicitRes1_inertiaLoc_eq_zero_iff` | `L20261018.Ch2.Hensel.Inertia.Step035_ker_v_eq_ker_res1` | 66 |  |
| `explicitRes1_inertiaLoc_kummerMap_eq_zero_iff` | `L20261018.Ch2.Hensel.Inertia.Step035_ker_v_eq_ker_res1` | 74 |  |
| `explicitRes1_kummerExplicit_eq_zero` | `L20261018.Ch3.BiKummer.Step012_basic_inclusions_cor_subset` | 63 | `label:lem:basic-inclusions` |
| `explicitRes1_kummerMap_a1` | `L20261018.Ch3.BiKummer.Step006_explicit_restriction_kernel` | 128 |  |
| `explicitRes1_kummerMap_a2` | `L20261018.Ch3.BiKummer.Step006_explicit_restriction_kernel` | 140 |  |
| `explicitRes1_kummerMap_eq_zero_iff` | `L20261018.Ch3.BiKummer.Step006_explicit_restriction_kernel` | 114 |  |
| `explicitRes1_mem_H1ConjInvariants` | `L20261018.Ch2.Hensel.ResidueMap.Step065_partial_one_inputs` | 66 |  |
| `f1Sq` | `L20261018.Infra.Cohomology.ResidueLES.Step003_f1_square` | 66 | `label:prop-residue-map-long-exact` |
| `f1Sq_τ₁_eq` | `L20261018.Infra.Cohomology.ResidueLES.Step003_f1_square` | 89 | `label:prop-residue-map-long-exact` |
| `f1Sq_τ₃_eq` | `L20261018.Infra.Cohomology.ResidueLES.Step003_f1_square` | 96 | `label:prop-residue-map-long-exact` |
| `fB` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 84 | `label:lemma-additive-hilbert90` |
| `fCG` | `L20261018.Infra.Cohomology.Coinduced.Step026_delta_two_inf_two_zero` | 64 |  |
| `fCG_compat` | `L20261018.Infra.Cohomology.Coinduced.Step026_delta_two_inf_two_zero` | 68 |  |
| `fact_irreducible_of_notMem_pow` | `L20261018.Ch2.Brauer.Step030_index_le_degree_instances` | 56 |  |
| `faithfulR2_of_span_eq_bot` | `L20261018.Ch2.Hensel.ResidueMap.Step042_residue_span_subset_ker_res` | 118 |  |
| `fieldRange_le_of_le` | `L20261018.Ch2.Hensel.Inertia.Step007_knr_correct_carrier` | 94 | `line:8152` |
| `finInt_sup` | `L20261018.Ch2.Hensel.Inertia.Step007_knr_correct_carrier` | 86 | `line:8152` |
| `finiteDimensional` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 404 |  |
| `finiteDimensional_galoBaseV_F` | `L20261018.Witness.Step032_f7t_v_finite_dimensional` | 69 | `line:1608` |
| `finiteDimensional_galoBaseV_Q7` | `L20261018.Witness.Step011_q7_v_finite_dimensional` | 73 |  |
| `finiteDimensional_range` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 110 |  |
| `finiteDimensional_symbolAlg` | `L20261018.Ch2.Brauer.Step030_index_le_degree_instances` | 87 |  |
| `finiteIndex_cubes_F` | `L20261018.Witness.Step035_f7t_thm_ramified_witness` | 53 |  |
| `finiteIndex_of_isOpen` | `L20261018.Infra.Cohomology.Coinduced.Step005_closed_subgroup_acyclicity` | 45 |  |
| `finite_H0` | `L20261018.Ch3.NormImage.Step010_three_six_h0_finite` | 63 |  |
| `finite_H1_kummerCoeff_F` | `L20261018.Witness.Step032_f7t_v_finite_dimensional` | 50 | `line:1608` |
| `finite_H1_kummerCoeff_Q7` | `L20261018.Witness.Step011_q7_v_finite_dimensional` | 56 |  |
| `finite_H1_zmod_F` | `L20261018.Witness.Step032_f7t_v_finite_dimensional` | 57 | `line:1608` |
| `finite_H1_zmod_Q7` | `L20261018.Witness.Step011_q7_v_finite_dimensional` | 62 |  |
| `finite_K2` | `L20261018.Ch3.NormImage.Step009_three_six_finiteness_k2` | 50 |  |
| `finite_adjoinRoot_uniformizer` | `L20261018.Infra.Algebra.Step002_norm_basis_change_bridge` | 42 |  |
| `finite_adjoinRoot_uniformizer_f` | `L20261018.Ch2.Hensel.Valuation.Step025_norm_smul_uniformizer` | 39 |  |
| `finite_galoBaseV_F` | `L20261018.Witness.Step032_f7t_v_finite_dimensional` | 64 | `line:1608` |
| `finite_galoBaseV_Q7` | `L20261018.Witness.Step011_q7_v_finite_dimensional` | 68 |  |
| `finite_hom_cont_tameModel_zmod` | `L20261018.Ch2.Hensel.Inertia.Step025_h1_inertia_finite` | 94 |  |
| `finite_of_addHom_surjective` | `L20261018.Ch3.NormImage.Step010_three_six_h0_finite` | 39 |  |
| `finite_powerClassQuotient` | `L20261018.Witness.Step031_f7t_finite_cube_classes` | 78 |  |
| `finite_powerClassQuotient_Q7` | `L20261018.Witness.Step011_q7_v_finite_dimensional` | 49 |  |
| `finite_quotient_fixingSubgroup` | `L20261018.Ch3.NormImage.Step009_three_six_finiteness_k2` | 44 |  |
| `finite_residueField` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 154 |  |
| `finite_residueUnits` | `L20261018.Witness.Step028_f7t_same_cube_class` | 36 |  |
| `finite_zmodDual_inertiaLoc` | `L20261018.Ch2.Hensel.Inertia.Step025_h1_inertia_finite` | 134 |  |
| `finite_zmodDual_inertiaLoc_iff` | `L20261018.Ch2.Hensel.Inertia.Step024_hom_inertia_tame` | 226 |  |
| `finite_zmodDual_inertia_iff` | `L20261018.Ch2.Hensel.Inertia.Step024_hom_inertia_tame` | 206 |  |
| `finite_zmodDual_tameInertia` | `L20261018.Ch2.Hensel.Inertia.Step025_h1_inertia_finite` | 121 |  |
| `finrank_H1_eq_two` | `L20261018.Ch4.Step009_dk_eq_one_is_a_theorem` | 122 | `line:1646` |
| `finrank_VKG_eq_one` | `L20261018.Ch2.Hensel.ResidueMap.Step066_finrank_vkg_one_reduction` | 63 |  |
| `finrank_VKG_eq_one_of_ne_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step067_finrank_vkg_le_one` | 116 |  |
| `finrank_VKG_eq_one_of_quot` | `L20261018.Ch2.Hensel.ResidueMap.Step068_infl_to_vkg_injective` | 94 |  |
| `finrank_VKG_le_one` | `L20261018.Ch2.Hensel.ResidueMap.Step067_finrank_vkg_le_one` | 106 |  |
| `finrank_V_eq_two` | `L20261018.Ch4.Step009_dk_eq_one_is_a_theorem` | 136 | `line:1646` |
| `finrank_adjoinRoot` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step004_capelli_criterion` | 85 |  |
| `finrank_adjoinRoot_uniformizer` | `L20261018.Ch2.Hensel.Valuation.Step008_adjoin_root_model` | 46 |  |
| `finrank_eq` | `L20261018.Ch2.Brauer.Step011_kummer_extension_generator` | 69 |  |
| `finrank_eq_finrank_add_one` | `L20261018.Ch4.Step005_corollary_four_four_dimension` | 64 | `line:1646` |
| `finrank_eq_finrank_add_one_of_D` | `L20261018.Ch4.Step016_corollary_four_four_sec_2_4_only` | 61 | `line:1648` |
| `finrank_eq_finrank_add_one_of_D_free` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 193 | `line:1636; line:1648` |
| `finrank_eq_finrank_add_one_uncond` | `L20261018.Ch4.Step007_corollary_four_four_no_d` | 76 | `line:1646` |
| `finrank_eq_prime_of_root_uniformizer` | `L20261018.Ch2.Hensel.Valuation.Step004_adjoin_root_degree_p` | 73 |  |
| `finrank_ker_le_one` | `L20261018.Ch2.Hensel.ResidueMap.Step067_finrank_vkg_le_one` | 89 |  |
| `finrank_ker_le_one_of_exists_ne_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step067_finrank_vkg_le_one` | 64 |  |
| `finrank_ker_restrict_plane_eq_one` | `L20261018.Ch4.Step011_transition_paragraph_4_1_4_2` | 100 | `line:1596; line:1599` |
| `finrank_ker_restrict_plane_eq_one_free` | `L20261018.Ch4.Step014_ramified_vanishing_hensel_level` | 119 | `line:1608` |
| `finrank_ker_restrict_plane_eq_one_general` | `L20261018.Ch4.Step012_ramified_vanishing_paper_route` | 74 | `line:1608` |
| `finrank_ker_restrict_plane_eq_one_nofin` | `L20261018.Ch4.Step037_ch4_without_finite_dimensional_v` | 51 | `line:1636` |
| `finrank_ker_restrict_plane_kummerClass_eq_one` | `L20261018.Ch4.Step011_transition_paragraph_4_1_4_2` | 182 | `line:1596; line:1599` |
| `finrank_ker_valLinOf_Q7` | `L20261018.Witness.Step015_q7_hk1` | 77 |  |
| `finrank_ker_valLinOf_le_one` | `L20261018.Ch2.Hensel.ResidueMap.Step040_ker_v_finrank_le_one` | 71 | `line:1648` |
| `finrank_ker_valLinOf_pos` | `L20261018.Ch2.Hensel.ResidueMap.Step038_ker_v_finrank_pos` | 62 |  |
| `finrank_ker_valLin_eq_one` | `L20261018.Ch4.Step009_dk_eq_one_is_a_theorem` | 79 | `line:1646` |
| `finrank_ker_valLin_le_one` | `L20261018.Ch4.Step009_dk_eq_one_is_a_theorem` | 53 | `line:1646` |
| `finrank_le` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 409 |  |
| `finrank_plane_eq_two` | `L20261018.Ch4.Step011_transition_paragraph_4_1_4_2` | 73 | `line:1596; line:1599` |
| `finrank_plane_eq_two_free` | `L20261018.Ch4.Step014_ramified_vanishing_hensel_level` | 97 | `line:1608` |
| `finrank_plane_kummerClass_eq_two` | `L20261018.Ch4.Step011_transition_paragraph_4_1_4_2` | 173 | `line:1596; line:1599` |
| `finrank_range` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 120 |  |
| `finrank_range_commonCupMap` | `L20261018.Ch4.Step005_corollary_four_four_dimension` | 77 | `line:1646` |
| `finrank_range_eq` | `L20261018.Ch4.Step008_rank_contradiction_single_phi` | 100 | `line:1646` |
| `finrank_ses` | `L20261018.Core.Step001_bi_kummer_data` | 515 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `five_isUnit` | `L20261018.Witness.Step007_l1_witness_q7` | 62 |  |
| `fixedField_inertiaLoc` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 102 | `label:sec:cohomology-complete-dv` |
| `fixedPointsZModEquiv` | `L20261018.Infra.Cohomology.Step010_trivial_action_fixed_points` | 66 |  |
| `fixedPoints_zmod_eq_top` | `L20261018.Infra.Cohomology.Step010_trivial_action_fixed_points` | 57 |  |
| `fixingSubgroup_Knr` | `L20261018.Ch2.Hensel.Inertia.Step003_knr_galois_quotient` | 111 | `label:sec:cohomology-complete-dv` |
| `fixingSubgroup_KnrLoc` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 107 | `label:sec:cohomology-complete-dv` |
| `fixingSubgroup_Knr_uncond` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 152 | `label:sec:cohomology-complete-dv` |
| `fixingSubgroup_finiteIndex` | `L20261018.Ch3.NormImage.Step009_three_six_finiteness_k2` | 37 |  |
| `fixingSubgroup_le_stabilizer` | `L20261018.Ch2.Hensel.Inertia.Step010_knr_continuous_smul` | 53 | `line:8160; line:8162` |
| `forall_VKG_cup_eq_zero_of_units` | `L20261018.Infra.Cohomology.ResidueLES.Step015_vkg_kummer_decomposition` | 62 |  |
| `free_adjoinRoot_uniformizer` | `L20261018.Infra.Algebra.Step002_norm_basis_change_bridge` | 37 |  |
| `free_adjoinRoot_uniformizer_f` | `L20261018.Ch2.Hensel.Valuation.Step025_norm_smul_uniformizer` | 34 |  |
| `gE` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 80 |  |
| `gE_apply` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 86 |  |
| `gE_cup` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 93 |  |
| `galoBaseH2_eq` | `L20261018.Ch2.Kummer.Step043_kummer_bridge_on_h2` | 57 |  |
| `galoBaseV_eq` | `L20261018.Ch2.Kummer.Step043_kummer_bridge_on_h2` | 52 |  |
| `galoBiKummer` | `L20261018.Core.Step001_bi_kummer_data` | 696 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `galo_five_term` | `L20261018.Ch3.NormImage.Step001_galo_five_term` | 29 |  |
| `galoisGroupKnrEquivRange` | `L20261018.Ch2.Hensel.Inertia.Step003_knr_galois_quotient` | 142 | `label:sec:cohomology-complete-dv` |
| `galoisGroupKnrLocEquivZHat` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 122 | `label:sec:cohomology-complete-dv` |
| `galoisGroupKnrLocQuotient` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 112 | `label:sec:cohomology-complete-dv` |
| `galoisGroupKnrQuotient` | `L20261018.Ch2.Hensel.Inertia.Step003_knr_galois_quotient` | 127 | `label:sec:cohomology-complete-dv` |
| `galoisGroupKnrQuotient_uncond` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 158 | `label:sec:cohomology-complete-dv` |
| `galoisQuotientInertiaEquivZHat` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 127 | `label:sec:cohomology-complete-dv` |
| `galois_fixes_rootsOfUnity_of_hasEnough` | `L20261018.Infra.Cohomology.Conjugation.Step009_h_conj1_carrier_inputs` | 60 |  |
| `gen` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 77 |  |
| `gen` | `L20261018.Ch2.Brauer.Step017_carry_exp_gen_pow` | 35 |  |
| `gen'` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 125 |  |
| `gen'_e_alpha` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 231 |  |
| `genAlg` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 285 |  |
| `genSet` | `L20261018.Ch2.Brauer.Step021_adjoin_top` | 38 |  |
| `gen_alpha` | `L20261018.Ch2.Brauer.Step023_symbol_alg_equiv_crossed_product` | 41 |  |
| `gen_pow_carryExp` | `L20261018.Ch2.Brauer.Step022_adjoin_top_assembly` | 43 |  |
| `gen_pow_eq_one` | `L20261018.Ch2.Brauer.Step018_product_cocycle_sum` | 55 |  |
| `generalHensel_reduction` | `L20261018.Ch4.Step024_tame_residue_facts_class_free` | 44 |  |
| `gens` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 281 |  |
| `geomSum_sub_eq` | `L20261018.Ch2.Hensel.ResidueMap.Step059_mu_p_into_residue_units` | 60 |  |
| `geomSum_sub_eq'` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step033_inertia_fixed_unit_pth_root` | 76 |  |
| `gsInputHyp_apply` | `L20261018.Ch2.Hensel.Inertia.Step027_cd_l_inertia_vanishing` | 83 |  |
| `gsInputHyp_of_cdLE` | `L20261018.Ch2.Hensel.Inertia.Step027_cd_l_inertia_vanishing` | 75 |  |
| `gs_coind_invariants_quotient` | `L20261018.Infra.Cohomology.Boundary.Step005_coinduced_invariants_recon` | 58 |  |
| `gs_coind_invariants_restrict` | `L20261018.Infra.Cohomology.Boundary.Step005_coinduced_invariants_recon` | 48 |  |
| `h0Bridge_projI` | `L20261018.Infra.Cohomology.Coinduced.Step018_iota_delta_zero_zero` | 162 |  |
| `h0Emb` | `L20261018.Ch2.Hensel.ResidueMap.Step074_delta_two_pi_cup_inf` | 57 |  |
| `h0Emb_res_infl` | `L20261018.Ch2.Hensel.ResidueMap.Step078_res_inertia_infl_image` | 112 |  |
| `h0Iso_surjective` | `L20261018.Infra.Cohomology.Coinduced.Step040_e_zero_surjective_leibniz` | 45 |  |
| `h0_exists_preimage` | `L20261018.Infra.Cohomology.Coinduced.Step041_infl_inverse_cup` | 108 |  |
| `h1BridgeQ` | `L20261018.Infra.Cohomology.Coinduced.Step008_delta_two_first_factors` | 70 |  |
| `h1BridgeQ_coeffMap` | `L20261018.Infra.Cohomology.Coinduced.Step021_h1_bridge_coeff_comm` | 64 |  |
| `h1BridgeQ_comp_coeffMap` | `L20261018.Infra.Cohomology.Coinduced.Step021_h1_bridge_coeff_comm` | 79 |  |
| `h1BridgeQ_cup01` | `L20261018.Ch2.Hensel.ResidueMap.Step074_delta_two_pi_cup_inf` | 81 |  |
| `h1BridgeQ_cup01_of_infl` | `L20261018.Ch2.Hensel.ResidueMap.Step074_delta_two_pi_cup_inf` | 117 |  |
| `h1BridgeQ_infl` | `L20261018.Infra.Cohomology.Coinduced.Step022_h1_bridge_infl_comm` | 52 |  |
| `h1ContEquivH` | `L20261018.Infra.Cohomology.Boundary.Step031_quotient_action_explicit_model` | 56 |  |
| `h1InertiaAddEquiv` | `L20261018.Infra.Cohomology.Conjugation.Step010_h_conj1_implies_f5` | 66 |  |
| `h1InertiaAddEquiv_neg_self` | `L20261018.Ch2.Hensel.ResidueMap.Step065_partial_one_inputs` | 143 |  |
| `h1InertiaAddEquiv_self` | `L20261018.Ch2.Hensel.ResidueMap.Step065_partial_one_inputs` | 130 |  |
| `h1InertiaLinearEquiv` | `L20261018.Ch2.Hensel.Inertia.Step039_h1_inertia_zmod` | 104 |  |
| `h1Inertia_smul_eq_nsmul_val` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 71 |  |
| `h1RepQuot` | `L20261018.Infra.Cohomology.Boundary.Step015_rep_quotient_structure` | 136 | `line:9497` |
| `h1RepQuot_V` | `L20261018.Infra.Cohomology.Boundary.Step015_rep_quotient_structure` | 143 | `line:9497` |
| `h1RepQuot_one_V` | `L20261018.Infra.Cohomology.Boundary.Step018_delta_two_conditional` | 131 | `line:9498` |
| `h1RepQuot_ρ_mk` | `L20261018.Infra.Cohomology.Boundary.Step015_rep_quotient_structure` | 150 | `line:9497` |
| `h1RepQuot_ρ_mk_coe` | `L20261018.Infra.Cohomology.Boundary.Step015_rep_quotient_structure` | 157 | `line:9497` |
| `h1ToVEquiv` | `L20261018.Ch2.Kummer.Step007_kummer_class_coefficient_bridge` | 76 |  |
| `h1ToVEquiv_apply_eq_muP` | `L20261018.Ch2.Kummer.Step019_kummer_class_route_a_normal_form` | 59 |  |
| `h1ToVEquiv_eq_muP` | `L20261018.Ch2.Kummer.Step031_t1_model_comparison` | 89 |  |
| `h1ToVEquiv_eq_muP'` | `L20261018.Ch2.Kummer.Step038_bridges_without_completeness` | 37 |  |
| `h1ToVEquiv_infl_valLinOf_eq_zero` | `L20261018.Infra.Cohomology.Conjugation.Step014_f5_landing` | 75 |  |
| `h1ToVEquiv_kummerExplicit_eq` | `L20261018.Ch2.Kummer.Step021_bridge_first_segment` | 42 |  |
| `h1ZModBridge` | `L20261018.Ch2.Hensel.ResidueMap.Step051_h1_z_equiv_galo_v` | 136 | `line:1050` |
| `h1ZModToMuNRep` | `L20261018.Ch2.Kummer.Step027_t1_mu_n_rep_factorization` | 128 |  |
| `h1_coker_addEquiv_h2` | `L20261018.Infra.Cohomology.Boundary.Step027_coinduced_ses_h1_h2` | 120 |  |
| `h1_inflation_addEquiv_of_subsingleton` | `L20261018.Infra.Cohomology.Boundary.Step028_inflation_h1_iso` | 98 |  |
| `h1_smul_eq_self_of_mem` | `L20261018.Infra.Cohomology.Conjugation.Step004_gamma_scalar_action` | 58 |  |
| `h2KummerToUnits_range_available` | `L20261018.Ch2.Hensel.ResidueMap.Step049_integral_bockstein_usable` | 60 |  |
| `h2ToGaloBase` | `L20261018.Infra.Cohomology.Coinduced.Step029_second_carrier_square` | 59 |  |
| `h2_addEquiv_h1_fixedPoints` | `L20261018.Infra.Cohomology.Boundary.Step028_inflation_h1_iso` | 135 |  |
| `h2_eq_zero_of_cd_le_one` | `L20261018.Ch4.Step026_residue_span_bot_reduction` | 46 |  |
| `hCoord` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 48 |  |
| `hCoord_cosRep_mul` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 66 |  |
| `hK1_F` | `L20261018.Ch2.Hensel.ResidueMap.Step040_ker_v_finrank_le_one` | 124 | `line:1648` |
| `hNG` | `L20261018.Ch3.NormImage.Step003_norm_image_def` | 49 |  |
| `hNrd_crossedProduct` | `L20261018.Ch3.BiKummer.Step003_h_nrd_from_field_norm` | 43 |  |
| `hUU` | `L20261018.Ch2.Hensel.ResidueMap.Step017_hdep_huu_are_theorems` | 80 | `label:prop:prelim-residue` |
| `hUU_of_ker_le_one` | `L20261018.Ch2.Hensel.ResidueMap.Step013_huu_reduced_to_linear_dependence` | 64 | `label:prop:prelim-residue` |
| `hUU_of_scale` | `L20261018.Ch2.Hensel.ResidueMap.Step012_bridge_kc_unit_cup_zero` | 78 | `label:prop:prelim-residue` |
| `hU_F` | `L20261018.Witness.Step036_f7t_thm_ramified_witness_paper_objects` | 96 | `line:1636` |
| `hasEnoughRootsOfUnity_Q7_three` | `L20261018.Witness.Step007_l1_witness_q7` | 112 |  |
| `hasEnoughRootsOfUnity_laurentSeries_zmod7_three` | `L20261018.Witness.Step021_f7t_mu3_transport` | 39 |  |
| `hasEnoughRootsOfUnity_residue` | `L20261018.Ch2.Hensel.ResidueMap.Step063_mu_p_residue_instance` | 72 |  |
| `hasEnoughRootsOfUnity_zmod7_three` | `L20261018.Witness.Step020_f7_mu3_primitive_root` | 34 |  |
| `hbridge_iff_eq_bridgeKc` | `L20261018.Ch2.Kummer.Step035_hbridge_single_equation` | 44 |  |
| `hcompat` | `L20261018.Ch2.Kummer.Step011_cup_fp_eq_galo_cup_equiv` | 37 |  |
| `hcupG_F` | `L20261018.Witness.Step034_f7t_galo_cup_nonzero` | 39 |  |
| `hcupT_pi` | `L20261018.Witness.Step033_f7t_mun_rep_cup_nonzero` | 68 |  |
| `hcyc_of_divisible` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 64 |  |
| `hcyc_of_finite` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 75 |  |
| `hd2surj` | `L20261018.Ch3.NormImage.Step002_five_term_mg_k2_data` | 47 |  |
| `hd_infl_F5_uncond` | `L20261018.Ch4.Step045_hd_infl_discharged` | 64 |  |
| `hd_infl_d_F5` | `L20261018.Ch2.Hensel.ResidueMap.Step064_delta_two_definition` | 78 |  |
| `hd_infl_of_linear` | `L20261018.Ch4.Step042_hd_infl_final_form` | 79 |  |
| `henselPoly` | `L20261018.Witness.Step026_f7t_principal_units_cube` | 42 |  |
| `henselResidueDataOfCup` | `L20261018.Ch2.Hensel.ResidueMap.Step022_ramified_vanishing_no_tame_symbol` | 31 | `label:lem:ramified-vanishing` |
| `henselResidueDataOfDiscreteValuation` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 172 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `henselResidueDataOfFacts` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 129 | `line:1050; line:1608; line:1636; line:1648` |
| `henselResidueDataOfFacts_val` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 164 | `line:1050; line:1608; line:1636; line:1648` |
| `henselResidueDataOfKer` | `L20261018.Ch2.Hensel.ResidueMap.Step019_hens_residue_data_nine_fields` | 36 |  |
| `henselResidueDataTransport` | `L20261018.Ch2.Hensel.ResidueMap.Step023_hens_residue_data_transport` | 28 |  |
| `henselResidueData_explicit` | `L20261018.Ch4.Step006_thm_ramified_no_d` | 119 | `label:thm:ramified` |
| `henselResidueData_explicit_of_D` | `L20261018.Ch4.Step016_corollary_four_four_sec_2_4_only` | 31 | `line:1648` |
| `henselResidueData_explicit_of_D_free` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 182 | `line:1636; line:1648` |
| `henselResidueData_explicit_of_D_val` | `L20261018.Ch4.Step016_corollary_four_four_sec_2_4_only` | 42 | `line:1648` |
| `henselResidueData_explicit_val` | `L20261018.Ch4.Step006_thm_ramified_no_d` | 137 | `label:thm:ramified` |
| `henselResidueData_nonempty` | `L20261018.Ch2.Hensel.ResidueMap.Step021_res_and_tame_u_pi_discharged` | 84 |  |
| `henselianRing_O` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 129 |  |
| `hilbert90_residueField` | `L20261018.Ch4.Step048_r2_infinite_residue_certificate` | 63 |  |
| `hind_kummer` | `L20261018.Ch3.BiKummer.Step016_hind_kummer` | 81 |  |
| `hkerd2` | `L20261018.Ch3.NormImage.Step002_five_term_mg_k2_data` | 42 |  |
| `hne43_F` | `L20261018.Witness.Step034_f7t_galo_cup_nonzero` | 61 |  |
| `hne_F` | `L20261018.Witness.Step025_f7t_hne_hval` | 128 | `line:1608` |
| `hne_Q7` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 93 |  |
| `hom_cont_eval_bijective` | `L20261018.Ch2.Hensel.Inertia.Step026_hom_inertia_mu_p_eq_zmod` | 201 |  |
| `hom_cont_eval_injective` | `L20261018.Ch2.Hensel.Inertia.Step025_h1_inertia_finite` | 64 |  |
| `hom_cont_eval_surjective` | `L20261018.Ch2.Hensel.Inertia.Step026_hom_inertia_mu_p_eq_zmod` | 185 |  |
| `hom_cont_inertiaLoc_equiv` | `L20261018.Ch2.Hensel.Inertia.Step026_hom_inertia_mu_p_eq_zmod` | 238 |  |
| `hom_cont_tameModel_equiv` | `L20261018.Ch2.Hensel.Inertia.Step026_hom_inertia_mu_p_eq_zmod` | 228 |  |
| `hom_ext` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 467 |  |
| `hpart` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step020_tg_definition` | 72 |  |
| `hpart_conj` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step021_tg_compatibility` | 75 |  |
| `hpart_mul` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step020_tg_definition` | 91 |  |
| `hpart_section` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step021_tg_compatibility` | 65 |  |
| `hroots` | `L20261018.Ch3.BiKummer.Step013_orthogonal_roots_trivial` | 51 | `label:lem:orthogonal` |
| `hroots_top_F` | `L20261018.Witness.Step036_f7t_thm_ramified_witness_paper_objects` | 77 | `line:1636` |
| `hstab_of_hval` | `L20261018.Ch2.Hensel.Inertia.Step028_inertia_subgroup_galois` | 64 |  |
| `hval43_F` | `L20261018.Witness.Step034_f7t_galo_cup_nonzero` | 77 |  |
| `hval44_F` | `L20261018.Witness.Step037_f7t_hval_and_corollary` | 38 |  |
| `hval_F` | `L20261018.Witness.Step025_f7t_hne_hval` | 155 | `line:1608` |
| `hval_Q7` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 118 |  |
| `iCocycles_cocyclesIso₀_inv` | `L20261018.Infra.Cohomology.Boundary.Step017_h0_conj_compatibility` | 90 | `line:3580` |
| `iCocycles_cocyclesMap` | `L20261018.Infra.Cohomology.Boundary.Step017_h0_conj_compatibility` | 82 | `line:3580` |
| `iCycles_cyclesMap` | `L20261018.Infra.Cohomology.Boundary.Step021_n1_reduction` | 69 |  |
| `iTame` | `L20261018.Infra.Cohomology.ResidueLES.Step002_t_cokernel_constructed` | 97 |  |
| `iTame_comp_deltaZeroBar` | `L20261018.Infra.Cohomology.ResidueLES.Step004_i_star_delta_zero_bar` | 77 |  |
| `inc_mem_adjoin` | `L20261018.Ch2.Brauer.Step020_adjoin_surjectivity_blocks` | 42 |  |
| `inc_mem_adjoin_gen` | `L20261018.Ch2.Brauer.Step021_adjoin_top` | 42 |  |
| `inclI` | `L20261018.Infra.Cohomology.Coinduced.Step016_gs617_ses1` | 47 |  |
| `inclI_quotient_smul` | `L20261018.Infra.Cohomology.Coinduced.Step016_gs617_ses1` | 66 |  |
| `indOfH2` | `L20261018.Ch2.Brauer.Step029_index_function_h2` | 88 |  |
| `indOfH2_def` | `L20261018.Ch2.Brauer.Step029_index_function_h2` | 92 |  |
| `indOfH2_independent` | `L20261018.Ch2.Brauer.Step034_index_zeta_independent` | 63 |  |
| `indOfH2_le_of_class_eq` | `L20261018.Ch2.Brauer.Step029_index_function_h2` | 104 |  |
| `indOfH2_le_of_class_one` | `L20261018.Ch3.BiKummer.Step016_hind_kummer` | 65 |  |
| `index_crossedProduct_le` | `L20261018.Ch2.Brauer.Step001_index_le_degree` | 51 |  |
| `index_crossedProduct_le_of_finrank` | `L20261018.Ch2.Brauer.Step001_index_le_degree` | 57 |  |
| `index_dvd_finrank_of_isSplittingField` | `L20261018.Ch2.Brauer.Step033_index_unit_scalar_invariant` | 96 |  |
| `index_dvd_finrank_of_isSplittingField_division` | `L20261018.Ch2.Brauer.Step033_index_unit_scalar_invariant` | 53 |  |
| `index_eq_of_algEquiv_matrix` | `L20261018.Ch2.Brauer.Step010_index_brauer_invariant` | 53 |  |
| `index_eq_of_mk_eq` | `L20261018.Ch2.Brauer.Step010_index_brauer_invariant` | 64 |  |
| `index_eq_of_mk_eq_pow` | `L20261018.Ch2.Brauer.Step033_index_unit_scalar_invariant` | 136 |  |
| `index_matrix` | `L20261018.Ch2.Brauer.Step010_index_brauer_invariant` | 47 |  |
| `index_self_eq_one` | `L20261018.Ch3.BiKummer.Step016_hind_kummer` | 43 |  |
| `index_self_le` | `L20261018.Ch3.BiKummer.Step016_hind_kummer` | 48 |  |
| `index_symbolAlg_le` | `L20261018.Ch2.Brauer.Step024_index_le_degree_symbol` | 44 |  |
| `index_symbolAlg_le_of_notMem_pow` | `L20261018.Ch2.Brauer.Step030_index_le_degree_instances` | 96 |  |
| `inertia` | `L20261018.Ch2.Hensel.Inertia.Step028_inertia_subgroup_galois` | 86 |  |
| `inertiaAbs` | `L20261018.Ch2.Hensel.Inertia.Step002_knr_definition` | 40 |  |
| `inertiaAbs_le_decompositionSubgroup` | `L20261018.Ch2.Hensel.Inertia.Step003_knr_galois_quotient` | 68 | `label:sec:cohomology-complete-dv` |
| `inertiaAbs_le_fixingSubgroup_Knr` | `L20261018.Ch2.Hensel.Inertia.Step002_knr_definition` | 53 |  |
| `inertiaAbs_normal_of_decomp_eq_top` | `L20261018.Ch2.Hensel.Inertia.Step003_knr_galois_quotient` | 80 | `label:sec:cohomology-complete-dv` |
| `inertiaEquivInertiaLoc` | `L20261018.Ch2.Hensel.Inertia.Step022_cd_p_inertia_unconditional` | 64 | `line:9627` |
| `inertiaEquivInertiaLoc_coe` | `L20261018.Infra.Cohomology.Conjugation.Step012_h_conj1_entry` | 90 |  |
| `inertiaEquivInertiaLoc_conj` | `L20261018.Infra.Cohomology.Conjugation.Step012_h_conj1_entry` | 118 |  |
| `inertiaEquivInertiaLoc_symm_coe` | `L20261018.Infra.Cohomology.Conjugation.Step012_h_conj1_entry` | 138 |  |
| `inertiaEquivInertiaLoc_symm_conj` | `L20261018.Infra.Cohomology.Conjugation.Step012_h_conj1_entry` | 150 |  |
| `inertiaLoc` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 78 | `label:sec:cohomology-complete-dv` |
| `inertiaLoc_Hq_eq_zero` | `L20261018.Ch2.Hensel.Inertia.Step023_b1_hom_inertia_mu_p` | 73 |  |
| `inertiaLoc_Hq_zmod_eq_zero` | `L20261018.Ch2.Hensel.Inertia.Step023_b1_hom_inertia_mu_p` | 83 |  |
| `inertiaLoc_cdLE` | `L20261018.Ch2.Hensel.Inertia.Step022_cd_p_inertia_unconditional` | 107 | `line:9627` |
| `inertiaLoc_cohomologicalDimensionAt_le_one` | `L20261018.Ch2.Hensel.Inertia.Step022_cd_p_inertia_unconditional` | 100 | `line:9627` |
| `inertiaLoc_eq_map_inertiaSubgroup` | `L20261018.Ch2.Hensel.Inertia.Step016_inertia_loc_carrier_alignment` | 60 | `line:8` |
| `inertiaLoc_fixes_pow_eq_one` | `L20261018.Infra.Cohomology.Conjugation.Step009_h_conj1_carrier_inputs` | 78 |  |
| `inertiaLoc_subsingleton_H1_contC` | `L20261018.Infra.Cohomology.Coinduced.Step011_hc_inertia_discharged` | 53 |  |
| `inertiaLoc_subsingleton_H2` | `L20261018.Ch2.Hensel.Inertia.Step022_cd_p_inertia_unconditional` | 148 | `line:9627` |
| `inertiaLoc_subsingleton_H2_zmod` | `L20261018.Ch2.Hensel.Inertia.Step022_cd_p_inertia_unconditional` | 139 | `line:9627` |
| `inertiaLoc_subsingleton_Hq` | `L20261018.Ch2.Hensel.Inertia.Step022_cd_p_inertia_unconditional` | 114 | `line:9627` |
| `inertiaProPSylowData_inertia` | `L20261018.Ch2.Hensel.Inertia.Step021_inertia_sylow_z_l` | 176 |  |
| `inertiaProPSylowData_inertiaLoc` | `L20261018.Ch2.Hensel.Inertia.Step022_cd_p_inertia_unconditional` | 91 | `line:9627` |
| `inertiaProPSylowData_of_procyclic` | `L20261018.Ch2.Hensel.Inertia.Step015_cd_p_procyclic_criterion` | 61 | `line:8` |
| `inertiaProPSylowData_of_procyclic_group` | `L20261018.Ch2.Hensel.Inertia.Step018_procyclic_l_part_sylow` | 153 | `line:9626` |
| `inertiaProPSylowData_of_procyclic_infinite` | `L20261018.Ch2.Hensel.Inertia.Step015_cd_p_procyclic_criterion` | 118 | `line:8` |
| `inertiaProPSylowData_tameModel` | `L20261018.Ch2.Hensel.Inertia.Step019_tame_module_l_part_infinite` | 155 |  |
| `inertiaProPSylowData_witness` | `L20261018.Ch2.Hensel.Inertia.Step013_inertia_pro_p_sylow_data` | 136 | `line:9625; line:9627` |
| `inertiaSet` | `L20261018.Ch2.Hensel.Valuation.Step040_integral_closure_value_preserving` | 83 |  |
| `inertiaSubgroup_compactSpace` | `L20261018.Ch2.Hensel.Inertia.Step021_inertia_sylow_z_l` | 96 |  |
| `inertiaSubgroup_normal` | `L20261018.Ch2.Hensel.Inertia.Step001_inertia_exact_sequence_first` | 42 |  |
| `inertia_Q_subsingleton_Hq` | `L20261018.Infra.Cohomology.Coinduced.Step002_coind_subgroup_acyclic_carrier` | 87 |  |
| `inertia_cdLE` | `L20261018.Ch2.Hensel.Inertia.Step014_cd_p_inertia_instance` | 92 | `label:cons-residue-map-finite-coefficients-2; line:9627` |
| `inertia_cohomologicalDimensionAt_le_one` | `L20261018.Ch2.Hensel.Inertia.Step014_cd_p_inertia_instance` | 86 | `label:cons-residue-map-finite-coefficients-2; line:9627` |
| `inertia_fixes_pow_eq_one_of_rootOfUnity` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step040_cocycle_on_quotient` | 193 |  |
| `inertia_fixes_pow_root` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step033_inertia_fixed_unit_pth_root` | 195 |  |
| `inertia_fixes_pow_root_of_unit` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step034_n4_paper_form` | 173 |  |
| `inertia_normal` | `L20261018.Ch2.Hensel.Inertia.Step029_inertia_normal` | 59 |  |
| `inertia_one_fixes_pow_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step040_cocycle_on_quotient` | 231 |  |
| `inertia_subsingleton_H2` | `L20261018.Ch2.Hensel.Inertia.Step014_cd_p_inertia_instance` | 113 | `label:cons-residue-map-finite-coefficients-2; line:9627` |
| `inertia_subsingleton_H2_zmod` | `L20261018.Ch2.Hensel.Inertia.Step014_cd_p_inertia_instance` | 107 | `label:cons-residue-map-finite-coefficients-2; line:9627` |
| `inertia_subsingleton_Hq` | `L20261018.Ch2.Hensel.Inertia.Step014_cd_p_inertia_instance` | 97 | `label:cons-residue-map-finite-coefficients-2; line:9627` |
| `inf_wildInertia_eq_bot` | `L20261018.Ch2.Hensel.Inertia.Step020_inertia_sylow_mod_ramification` | 105 |  |
| `inf_wildInertia_eq_bot'` | `L20261018.Ch2.Hensel.Inertia.Step020_inertia_sylow_mod_ramification` | 141 |  |
| `infinite_tameModel_pPart` | `L20261018.Ch2.Hensel.Inertia.Step019_tame_module_l_part_infinite` | 84 |  |
| `infl1AddEquiv_of_H1_subsingleton` | `L20261018.Infra.Cohomology.Coinduced.Step006_inf_h1_iso_closed_subgroup` | 77 |  |
| `infl1AddEquiv_of_coindAcyclic` | `L20261018.Infra.Cohomology.Coinduced.Step006_inf_h1_iso_closed_subgroup` | 94 |  |
| `infl1Canon` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 147 |  |
| `infl1EquivVKG` | `L20261018.Infra.Cohomology.Coinduced.Step036_res_h1_type_equiv_vkg` | 223 |  |
| `infl1Res` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 145 |  |
| `infl1ResToVKG` | `L20261018.Infra.Cohomology.Coinduced.Step036_res_h1_type_equiv_vkg` | 212 |  |
| `infl1Res_eQ` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 181 |  |
| `infl1Res_eQ_coeff` | `L20261018.Ch4.Step046_exists_residue_map` | 160 |  |
| `infl1Res_injective` | `L20261018.Infra.Cohomology.Coinduced.Step036_res_h1_type_equiv_vkg` | 177 |  |
| `infl1Res_valLinOf_eq_zero` | `L20261018.Infra.Cohomology.Coinduced.Step036_res_h1_type_equiv_vkg` | 202 |  |
| `infl1_surjective_of_H1_subsingleton` | `L20261018.Infra.Cohomology.Coinduced.Step006_inf_h1_iso_closed_subgroup` | 59 |  |
| `infl2Canon` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 153 |  |
| `infl2Canon_cup` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 168 |  |
| `infl2Res` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 149 |  |
| `infl2Res_cupRes` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 161 |  |
| `infl2Res_eQ2` | `L20261018.Infra.Cohomology.Coinduced.Step029_second_carrier_square` | 67 |  |
| `inflH1` | `L20261018.Ch2.Hensel.ResidueMap.Step060_h_kappa_h2_zero` | 81 |  |
| `inflH2` | `L20261018.Ch2.Hensel.ResidueMap.Step060_h_kappa_h2_zero` | 85 |  |
| `inflH2_cupK` | `L20261018.Ch2.Hensel.ResidueMap.Step060_h_kappa_h2_zero` | 94 |  |
| `inflStep` | `L20261018.Infra.Cohomology.Coinduced.Step008_delta_two_first_factors` | 75 |  |
| `inflStep_cup01_infl` | `L20261018.Infra.Cohomology.Coinduced.Step041_infl_inverse_cup` | 132 |  |
| `inflStep_explicitCup01` | `L20261018.Infra.Cohomology.Coinduced.Step041_infl_inverse_cup` | 75 |  |
| `inflStep_explicitInfl1` | `L20261018.Infra.Cohomology.Coinduced.Step008_delta_two_first_factors` | 87 |  |
| `inflToVAddHom` | `L20261018.Infra.Cohomology.Conjugation.Step014_f5_landing` | 96 |  |
| `inflToVAddHom_injective` | `L20261018.Ch2.Hensel.ResidueMap.Step068_infl_to_vkg_injective` | 52 |  |
| `inflToVKG` | `L20261018.Infra.Cohomology.Conjugation.Step014_f5_landing` | 106 |  |
| `inflToVKG_injective` | `L20261018.Ch2.Hensel.ResidueMap.Step068_infl_to_vkg_injective` | 70 |  |
| `infl_eq_of_split'` | `L20261018.Ch2.Hensel.TameSymbol.Step002_tame_symbol_formula` | 77 | `label:eq:prelim-tame` |
| `infl_res_cup` | `L20261018.Ch2.Hensel.TameSymbol.Step002_tame_symbol_formula` | 108 | `label:eq:prelim-tame` |
| `inflateZ2_eq_relBrCocycle` | `L20261018.Ch2.Brauer.Step025_crossed_product_class_inflation` | 41 |  |
| `inflationIso_dimensionShiftUp` | `L20261018.Infra.Cohomology.Boundary.Step008_delta_two_inflation_iso` | 50 |  |
| `inflationIso_dimensionShiftUp_hom` | `L20261018.Infra.Cohomology.Boundary.Step008_delta_two_inflation_iso` | 59 |  |
| `inflationIso_dimensionShiftUp_oneH` | `L20261018.Infra.Cohomology.Boundary.Step008_delta_two_inflation_iso` | 67 |  |
| `inflationIso_dimensionShiftUp_zero` | `L20261018.Infra.Cohomology.Boundary.Step034_hcd_empty_hypothesis` | 70 |  |
| `inflationIso_hom_eq` | `L20261018.Infra.Cohomology.ResidueLES.Step005_delta_two_comp_inf_zero` | 62 |  |
| `injective_of_comp_eq` | `L20261018.Ch4.Step028_r1_linear_transport` | 49 |  |
| `injective_of_comp_eq_fun` | `L20261018.Ch4.Step029_r1_two_carriers_wired` | 64 |  |
| `injective_of_exists_leftInverse` | `L20261018.Ch2.Hensel.ResidueMap.Step069_hcup_injectivity` | 112 |  |
| `innerConjTrivialIn` | `L20261018.Infra.Cohomology.Boundary.Step013_inner_conj_trivial_in` | 43 |  |
| `innerConjTrivialIn_iff` | `L20261018.Infra.Cohomology.Boundary.Step013_inner_conj_trivial_in` | 47 |  |
| `innerConjTrivialIn_of_forall` | `L20261018.Infra.Cohomology.Boundary.Step013_inner_conj_trivial_in` | 67 |  |
| `innerConjTrivialIn_of_subsingleton` | `L20261018.Infra.Cohomology.Boundary.Step013_inner_conj_trivial_in` | 59 |  |
| `innerConjTrivialIn_one` | `L20261018.Infra.Cohomology.Boundary.Step025_inner_conj_trivial_in_discharged` | 131 |  |
| `innerConjTrivialIn_one_of` | `L20261018.Infra.Cohomology.Boundary.Step021_n1_reduction` | 94 |  |
| `innerConjTrivial_iff` | `L20261018.Infra.Cohomology.Boundary.Step012_inner_conj_trivial_hyp` | 45 |  |
| `innerConjTrivial_of_subsingleton` | `L20261018.Infra.Cohomology.Boundary.Step012_inner_conj_trivial_hyp` | 57 |  |
| `instContinuousSMulAbsGaloisZMod` | `L20261018.Ch2.Kummer.Step027_t1_mu_n_rep_factorization` | 71 |  |
| `instContinuousSMulMuP` | `L20261018.Ch2.Kummer.Step019_kummer_class_route_a_normal_form` | 40 |  |
| `instContinuousSMulMuP320` | `L20261018.Ch2.Kummer.Step039_t1_without_completeness` | 54 |  |
| `instContinuousSMulMuPH223` | `L20261018.Ch2.Kummer.Step033_t1_closed` | 47 |  |
| `instContinuousSMulQuotZMod` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 80 |  |
| `instContinuousSMulTrivialFp` | `L20261018.Ch2.Kummer.Step028_t1_explicit_map1_linear` | 112 |  |
| `instContinuousSMulTrivialFpGen` | `L20261018.Ch2.Kummer.Step029_t1_group_variable_cancel` | 119 |  |
| `instDistribMulActionAbsGaloisZMod` | `L20261018.Ch2.Kummer.Step027_t1_mu_n_rep_factorization` | 66 |  |
| `instDistribMulActionQuotZMod` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 71 |  |
| `instDistribMulActionQuotientH1` | `L20261018.Infra.Cohomology.Conjugation.Step005_gamma_complete` | 69 |  |
| `instIsInvariant` | `L20261018.Ch2.Brauer.Step001_index_le_degree` | 35 |  |
| `instModuleZModH1` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 60 | `label:thm:hs-tate-exact-sequences` |
| `instMulActionQuotZMod` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 67 |  |
| `instSMulCommClassQuotZModInt` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 76 |  |
| `instSMulQuotZMod` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 64 |  |
| `instSMulQuotientH1` | `L20261018.Infra.Cohomology.Conjugation.Step004_gamma_scalar_action` | 64 |  |
| `instValuativeRel` | `L20261018.Witness.Step017_laurent_series_valuative_rel` | 23 |  |
| `inst_finiteDimensional_Efield_top_F` | `L20261018.Witness.Step036_f7t_thm_ramified_witness_paper_objects` | 56 | `line:1636` |
| `inst_finiteRelIndex_top_F` | `L20261018.Witness.Step036_f7t_thm_ramified_witness_paper_objects` | 42 | `line:1636` |
| `inst_isGalois_Efield_top_F` | `L20261018.Witness.Step036_f7t_thm_ramified_witness_paper_objects` | 67 | `line:1636` |
| `intH2AddEquivH1RatOverZ` | `L20261018.Infra.Cohomology.Step005_cont_integral_dual_shift` | 175 | `label:sec:cohomology-complete-dv` |
| `intH2EquivH1RatOverZ` | `L20261018.Infra.Cohomology.Step005_cont_integral_dual_shift` | 167 | `label:sec:cohomology-complete-dv` |
| `integralBockstein_available` | `L20261018.Ch2.Hensel.ResidueMap.Step047_integral_bockstein_range` | 56 |  |
| `integralBockstein_one_range` | `L20261018.Ch2.Hensel.ResidueMap.Step048_integral_bockstein_range_complete` | 70 |  |
| `integralBockstein_one_range_nsmul` | `L20261018.Ch2.Hensel.ResidueMap.Step049_integral_bockstein_usable` | 52 |  |
| `invB` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 94 | `label:lemma-additive-hilbert90` |
| `invB_mkB` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 97 | `label:lemma-additive-hilbert90` |
| `invFun` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 149 |  |
| `invFunFun` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 115 |  |
| `invFun_toFun` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 159 |  |
| `invMul` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 91 |  |
| `invMul_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 115 |  |
| `invPairing` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 121 |  |
| `invPairing_comp` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 134 |  |
| `iota` | `L20261018.Infra.Cohomology.Coinduced.Step018_iota_delta_zero_zero` | 107 |  |
| `iotaHom` | `L20261018.Infra.Cohomology.Coinduced.Step023_cont_m_coeff_map` | 46 |  |
| `iotaHom_comp_eq_zero` | `L20261018.Infra.Cohomology.Coinduced.Step023_cont_m_coeff_map` | 61 |  |
| `iota_mk` | `L20261018.Infra.Cohomology.Coinduced.Step018_iota_delta_zero_zero` | 115 |  |
| `iota_quotient_smul` | `L20261018.Infra.Cohomology.Coinduced.Step018_iota_delta_zero_zero` | 121 |  |
| `irreducible` | `L20261018.Ch2.Brauer.Step011_kummer_extension_generator` | 27 |  |
| `irreducible_X_pow_sub_C_uniformizer` | `L20261018.Ch2.Hensel.Valuation.Step004_adjoin_root_degree_p` | 60 |  |
| `irreducible_piO` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 109 |  |
| `is` | `L20261018.Core.Step001_bi_kummer_data` | 716 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `isAdicComplete_O` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 119 |  |
| `isCentral_of_algEquiv` | `L20261018.Ch2.Brauer.Step007_brauer_interfaces` | 46 |  |
| `isCentral_symbolAlg` | `L20261018.Ch2.Brauer.Step030_index_le_degree_instances` | 61 |  |
| `isClosed_bot_quot` | `L20261018.Infra.Cohomology.ResidueLES.Step017_delta_t_iso_upper` | 77 |  |
| `isClosed_inertiaAbs_of_eq` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 139 | `label:sec:cohomology-complete-dv` |
| `isClosed_inertiaLoc` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 93 | `label:sec:cohomology-complete-dv` |
| `isCompl_range_infl_span_pi` | `L20261018.Ch2.Hensel.ResidueMap.Step033_residue_sequence_exact_split` | 71 | `label:prop:prelim-residue` |
| `isCube_of_residue_cube` | `L20261018.Witness.Step027_f7t_unit_cube_from_residue` | 55 |  |
| `isCube_of_residue_one` | `L20261018.Witness.Step027_f7t_unit_cube_from_residue` | 96 |  |
| `isCyclic` | `L20261018.Ch2.Brauer.Step011_kummer_extension_generator` | 79 |  |
| `isCyclic_units_of_finite` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step008_residue_field_units_cyclic` | 42 |  |
| `isDiscreteValuationRing_O` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 52 |  |
| `isEisensteinAt_uniformizer` | `L20261018.Ch2.Hensel.Valuation.Step005_eisenstein_uniformizer` | 73 |  |
| `isGalois` | `L20261018.Ch2.Brauer.Step011_kummer_extension_generator` | 74 |  |
| `isGalois_Knr` | `L20261018.Ch2.Hensel.Inertia.Step003_knr_galois_quotient` | 96 | `label:sec:cohomology-complete-dv` |
| `isGalois_KnrLoc` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 85 | `label:sec:cohomology-complete-dv` |
| `isGalois_Knr_of_decomp_eq_top` | `L20261018.Ch2.Hensel.Inertia.Step003_knr_galois_quotient` | 101 | `label:sec:cohomology-complete-dv` |
| `isGalois_Knr_uncond` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 146 | `label:sec:cohomology-complete-dv` |
| `isGalois_range` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 115 |  |
| `isIntegral_algEquiv` | `L20261018.Ch2.Hensel.Valuation.Step039_integral_closure_stable` | 57 |  |
| `isIso_HInfRes_dimensionShiftUp` | `L20261018.Infra.Cohomology.Boundary.Step008_delta_two_inflation_iso` | 42 |  |
| `isIso_HInfRes_dimensionShift_zero_of_h2` | `L20261018.Infra.Cohomology.Boundary.Step034_hcd_empty_hypothesis` | 58 |  |
| `isIso_contCoindSES_delta` | `L20261018.Infra.Cohomology.ResidueLES.Step014_continuous_d_two_blocks` | 58 |  |
| `isIso_contInvSES_delta` | `L20261018.Infra.Cohomology.ResidueLES.Step016_delta_t_iso` | 50 |  |
| `isIso_contInvSES_delta_inertia` | `L20261018.Infra.Cohomology.ResidueLES.Step025_delta_t_iso_usable` | 58 |  |
| `isIso_contInvSES_delta_uncond` | `L20261018.Infra.Cohomology.ResidueLES.Step024_top_rep_iso_coind` | 114 |  |
| `isLocallyConstant_invFunFun` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 138 |  |
| `isLocallyConstant_mk_quotient` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 119 |  |
| `isLocallyConstant_toFunFun` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 95 |  |
| `isOpen_stabilizer` | `L20261018.Ch2.Hensel.Inertia.Step010_knr_continuous_smul` | 64 | `line:8160; line:8162` |
| `isOpen_stabilizer'` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 131 | `line:8160; line:8163` |
| `isOpen_stabilizerKer` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 218 | `line:8160; line:8163` |
| `isPPrimaryTorsion_muP` | `L20261018.Ch2.Rost.Step002_tsen_cd_p_le_one` | 115 |  |
| `isPPrimaryTorsion_of_module_zmod` | `L20261018.Ch2.Rost.Step001_cd_p_z_p_le_one` | 131 | `label:prop-cd-Z-hat; line:9625; line:9627` |
| `isPPrimaryTorsion_zmod_p` | `L20261018.Infra.Cohomology.Coinduced.Step011_hc_inertia_discharged` | 36 |  |
| `isPrimitiveRoot_C_two` | `L20261018.Witness.Step021_f7t_mu3_transport` | 34 |  |
| `isPrimitiveRoot_residue` | `L20261018.Ch2.Hensel.ResidueMap.Step061_mu_p_in_residue_field` | 65 |  |
| `isPrimitiveRoot_two_zmod7` | `L20261018.Witness.Step020_f7_mu3_primitive_root` | 19 |  |
| `isPrincipalIdealRing_O` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 45 |  |
| `isProPSylow_closedZpowers_zpowHat_idem` | `L20261018.Ch2.Hensel.Inertia.Step018_procyclic_l_part_sylow` | 107 | `line:9626` |
| `isProPSylow_map_toTameInertia` | `L20261018.Ch2.Hensel.Inertia.Step020_inertia_sylow_mod_ramification` | 96 |  |
| `isSimpleRing_of_algEquiv` | `L20261018.Ch2.Brauer.Step007_brauer_interfaces` | 66 |  |
| `isSimpleRing_symbolAlg` | `L20261018.Ch2.Brauer.Step030_index_le_degree_instances` | 74 |  |
| `isSmoothDiscrete_muP` | `L20261018.Infra.Cohomology.ResidueLES.Step006_mu_p_smooth_discrete` | 86 |  |
| `isSplittingField` | `L20261018.Ch2.Brauer.Step011_kummer_extension_generator` | 64 |  |
| `isSplittingField_of_mk_eq` | `L20261018.Ch2.Brauer.Step033_index_unit_scalar_invariant` | 124 |  |
| `isUnit_algebraMap_of_isUnit` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step034_n4_paper_form` | 130 |  |
| `isUnit_mk_of_inv_mem` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step034_n4_paper_form` | 80 |  |
| `isUnit_natCast_of_charZero` | `L20261018.Ch4.Step044_ch4_hypothesis_deflation_audit` | 58 |  |
| `isUnit_natCast_residueField` | `L20261018.Ch4.Step048_r2_infinite_residue_certificate` | 50 |  |
| `isUnit_of_constantCoeff_ne_zero` | `L20261018.Witness.Step025_f7t_hne_hval` | 64 | `line:1608` |
| `isUnit_of_mul_left` | `L20261018.Ch2.Hensel.ResidueMap.Step059_mu_p_into_residue_units` | 74 |  |
| `isUnit_of_mul_left'` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step033_inertia_fixed_unit_pth_root` | 90 |  |
| `isUnit_of_notMem_maximalIdeal` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 109 | `line:739` |
| `isUnit_sub_one_of_pow_eq_one` | `L20261018.Ch2.Hensel.ResidueMap.Step059_mu_p_into_residue_units` | 83 |  |
| `isUnit_sub_one_of_pow_eq_one'` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step033_inertia_fixed_unit_pth_root` | 99 |  |
| `isZero_h2_of_hcd` | `L20261018.Infra.Cohomology.Boundary.Step035_delta_two_hypotheses_cleared` | 74 |  |
| `isZero_res_dimensionShiftUp` | `L20261018.Infra.Cohomology.Boundary.Step007_delta_two_gating` | 45 |  |
| `isZero_res_dimensionShiftUp_of_cd` | `L20261018.Infra.Cohomology.Boundary.Step007_delta_two_gating` | 70 |  |
| `isZero_res_dimensionShiftUp_one` | `L20261018.Infra.Cohomology.Boundary.Step007_delta_two_gating` | 59 |  |
| `iso` | `L20261018.Ch2.Kummer.Step010_cup_fp_eq_galo_cup` | 70 |  |
| `kc_eq_zero_of_residue_cube` | `L20261018.Ch2.Hensel.ResidueMap.Step040_ker_v_finrank_le_one` | 62 | `line:1648` |
| `kc_inv` | `L20261018.Ch2.Hensel.ResidueMap.Step040_ker_v_finrank_le_one` | 53 | `line:1648` |
| `kc_one` | `L20261018.Ch2.Hensel.ResidueMap.Step040_ker_v_finrank_le_one` | 46 | `line:1648` |
| `kc_two_mem_ker` | `L20261018.Ch2.Hensel.ResidueMap.Step038_ker_v_finrank_pos` | 47 |  |
| `kc_two_mem_ker_Q7` | `L20261018.Witness.Step010_q7_nonzero_cup` | 69 |  |
| `kc_two_ne_zero` | `L20261018.Witness.Step025_f7t_hne_hval` | 81 | `line:1608` |
| `kc_two_ne_zero_G` | `L20261018.Ch2.Hensel.ResidueMap.Step038_ker_v_finrank_pos` | 38 |  |
| `kc_two_ne_zero_muNRep_Q7` | `L20261018.Witness.Step012_q7_exists_nonzero_cup` | 54 |  |
| `kce_eq_eDouble_comp` | `L20261018.Ch2.Kummer.Step025_t1_reduction_factor_separation` | 49 |  |
| `kerCupPi` | `L20261018.Ch2.Hensel.ResidueMap.Step021_res_and_tame_u_pi_discharged` | 43 |  |
| `kerCupPi_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step021_res_and_tame_u_pi_discharged` | 48 |  |
| `kerCupPi_injective` | `L20261018.Ch2.Hensel.ResidueMap.Step021_res_and_tame_u_pi_discharged` | 55 |  |
| `ker_comp_mkQ_eq_bot` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 103 | `line:1050; line:1608; line:1636; line:1648` |
| `ker_cup_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step018_huu_discharged` | 39 | `label:lem:ramified-vanishing` |
| `ker_dependent` | `L20261018.Ch2.Hensel.ResidueMap.Step017_hdep_huu_are_theorems` | 33 | `label:prop:prelim-residue` |
| `ker_kummerMap_residueField` | `L20261018.Ch4.Step048_r2_infinite_residue_certificate` | 93 |  |
| `ker_res_eq_span` | `L20261018.Ch3.BiKummer.Step011_restriction_kernel_eq_u` | 97 |  |
| `ker_toTameInertia` | `L20261018.Ch2.Hensel.Inertia.Step021_inertia_sylow_z_l` | 121 |  |
| `ker_valLin_contains_zeta` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step019_b_tension_resolved` | 77 |  |
| `ker_val_eq_range_infl` | `L20261018.Ch2.Hensel.ResidueMap.Step033_residue_sequence_exact_split` | 37 | `label:prop:prelim-residue` |
| `ker_val_eq_range_infl` | `L20261018.Ch4.Step005_corollary_four_four_dimension` | 45 | `line:1646` |
| `knrContinuousSMulOn` | `L20261018.Ch2.Hensel.Inertia.Step010_knr_continuous_smul` | 83 | `line:8160; line:8162` |
| `knrD` | `L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive` | 196 |  |
| `knrD_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive` | 203 |  |
| `knrD_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 163 |  |
| `knrFinIntNonempty` | `L20261018.Ch2.Hensel.Inertia.Step007_knr_correct_carrier` | 110 | `line:8152` |
| `knrIncl` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 164 | `line:8162; line:8165` |
| `knrInclOn` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 132 | `line:8162; line:8163` |
| `knrInclOn_equivariant` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 246 | `line:8160; line:8163` |
| `knrInclOn_injective` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 139 | `line:8162; line:8163` |
| `knrIncl_injective` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 171 | `line:8162; line:8165` |
| `knrMap` | `L20261018.Ch2.Hensel.Inertia.Step006_knr_coefficient_action` | 63 | `line:8156; line:8160` |
| `knrMapOn` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 93 | `line:8156; line:8160` |
| `knrMapOn_coe` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 101 | `line:8156; line:8160` |
| `knrMapOn_id` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 105 | `line:8156; line:8160` |
| `knrMapOn_mul` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 111 | `line:8156; line:8160` |
| `knrMap_apply` | `L20261018.Ch2.Hensel.Inertia.Step006_knr_coefficient_action` | 83 | `line:8156; line:8160` |
| `knrMap_coeff` | `L20261018.Ch2.Hensel.Inertia.Step006_knr_coefficient_action` | 87 | `line:8156; line:8160` |
| `knrMap_eq_self_of_mem_fixing` | `L20261018.Ch2.Hensel.Inertia.Step010_knr_continuous_smul` | 40 | `line:8160; line:8162` |
| `knrMap_id` | `L20261018.Ch2.Hensel.Inertia.Step006_knr_coefficient_action` | 94 | `line:8156; line:8160` |
| `knrMap_mem_Knr` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 81 | `line:8156; line:8160` |
| `knrMap_mul` | `L20261018.Ch2.Hensel.Inertia.Step006_knr_coefficient_action` | 101 | `line:8156; line:8160` |
| `knrMap_single_zero` | `L20261018.Ch2.Hensel.Inertia.Step012_kummer_coeff_equivariant` | 43 | `line:8176` |
| `knrMulActionOn` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 118 | `line:8156; line:8160` |
| `knrPi` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 136 | `line:8162; line:8165` |
| `knrPiOn` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 103 | `line:8162; line:8163` |
| `knrProj` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 150 | `line:8162; line:8165` |
| `knrProjCoeffAdd` | `L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive` | 104 |  |
| `knrProjCoeffAdd_comp_kummerCoeffToKnrAdd_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 117 |  |
| `knrProjOn` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 117 | `line:8162; line:8163` |
| `knrProjOn_equivariant` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 253 | `line:8160; line:8163` |
| `knrProjOn_exact` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 147 | `line:8162; line:8163` |
| `knrProjOn_kummerCoeffToKnrUnits` | `L20261018.Ch2.Hensel.ResidueMap.Step052_delta_two_candidate_zero` | 104 | `label:prop-units-cohomology; line:8160` |
| `knrProjOn_split` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 181 | `line:8162; line:8163` |
| `knrProjOn_surjective` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 170 | `line:8162; line:8163` |
| `knrProj_exact` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 180 | `line:8162; line:8165` |
| `knrProj_split` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 212 | `line:8162; line:8165` |
| `knrProj_surjective` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 202 | `line:8162; line:8165` |
| `knrResidueMap'` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 276 | `line:8160; line:8163` |
| `knrResidueMapInt` | `L20261018.Ch2.Hensel.ResidueMap.Step046_knr_residue_map_int` | 53 |  |
| `knrResidueMapInt_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step046_knr_residue_map_int` | 61 |  |
| `knrResidueObligation_iff_exists_three` | `L20261018.Ch2.Hensel.ResidueMap.Step053_exists_d_three_properties` | 82 | `line:1050` |
| `knrResidueObligation_of_divisibleResidue` | `L20261018.Ch2.Hensel.TameSymbol.Step004_tame_symbol_hyp_divisible_residue` | 66 | `line:1050` |
| `knrResidueObligation_of_reduced` | `L20261018.Ch2.Hensel.ResidueMap.Step051_h1_z_equiv_galo_v` | 193 | `line:1050` |
| `knrResidueObligation_of_reduced_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step051_h1_z_equiv_galo_v` | 209 | `line:1050` |
| `knrResidueObligation_of_reduced_regression` | `L20261018.Ch2.Hensel.ResidueMap.Step053_exists_d_three_properties` | 106 | `line:1050` |
| `knrResidueObligation_of_three` | `L20261018.Ch2.Hensel.ResidueMap.Step053_exists_d_three_properties` | 63 | `line:1050` |
| `knrShortExact'` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 264 | `line:8160; line:8163` |
| `knrSubfieldDiscreteTopology` | `L20261018.Ch2.Hensel.Inertia.Step010_knr_continuous_smul` | 76 | `line:8160; line:8162` |
| `knrSubfieldTopologicalSpace` | `L20261018.Ch2.Hensel.Inertia.Step010_knr_continuous_smul` | 74 | `line:8160; line:8162` |
| `knrSubfield_directed` | `L20261018.Ch2.Hensel.Inertia.Step007_knr_correct_carrier` | 104 | `line:8152` |
| `knrUContinuousSMul'` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 153 | `line:8160; line:8163` |
| `knrUContinuousSMulInt` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 126 | `line:8160; line:8163` |
| `knrUDistribMulAction` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 92 | `line:8160; line:8163` |
| `knrUKerContinuousSMul'` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 239 | `line:8160; line:8163` |
| `knrUKerContinuousSMulInt` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 215 | `line:8160; line:8163` |
| `knrUKerDiscrete` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 87 | `line:8160; line:8163` |
| `knrUKerDistribMulAction` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 167 | `line:8160; line:8163` |
| `knrUKerSMulCommClass` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 204 | `line:8160; line:8163` |
| `knrUKerSmul` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 159 | `line:8160; line:8163` |
| `knrUKerTopology` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 85 | `line:8160; line:8163` |
| `knrUSMulCommClass` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 118 | `line:8160; line:8163` |
| `knrUUnitsDiscrete` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 83 | `line:8160; line:8163` |
| `knrUUnitsTopology` | `L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units` | 81 | `line:8160; line:8163` |
| `knrUnit` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 103 | `line:8162; line:8165` |
| `knrUnitIncl` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 77 | `line:8162; line:8163` |
| `knrUnitIncl_smul` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 147 | `line:8156; line:8160` |
| `knrUnitIncl_unit` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 81 | `line:8162; line:8163` |
| `knrUnitOn` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 62 | `line:8162; line:8163` |
| `knrUnitOn_coe` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 70 | `line:8162; line:8163` |
| `knrUnit_coe` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 119 | `line:8162; line:8165` |
| `knrUnit_mem` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 46 | `line:8162; line:8163` |
| `knrUnitsMulAction` | `L20261018.Ch2.Hensel.Inertia.Step006_knr_coefficient_action` | 110 | `line:8156; line:8160` |
| `knrUnitsMulActionOn` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 131 | `line:8156; line:8160` |
| `knrVal` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 111 | `line:8162; line:8165` |
| `knrValOn` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 91 | `line:8162; line:8163` |
| `knrValOn_apply` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 95 | `line:8162; line:8163` |
| `knrValOn_pi` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 107 | `line:8162; line:8163` |
| `knrValOn_smul` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 159 | `line:8156; line:8160` |
| `knrValOn_unit` | `L20261018.Ch2.Hensel.Inertia.Step008_gs61_on_correct_knr` | 98 | `line:8162; line:8163` |
| `knrVal_map_eq` | `L20261018.Ch2.Hensel.Inertia.Step006_knr_coefficient_action` | 129 | `line:8156; line:8160` |
| `knrVal_pi` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 139 | `line:8162; line:8165` |
| `knrVal_single` | `L20261018.Ch2.Hensel.Inertia.Step005_knr_explicit_laurent` | 124 | `line:8162; line:8165` |
| `knrVal_smul` | `L20261018.Ch2.Hensel.Inertia.Step006_knr_coefficient_action` | 184 | `line:8156; line:8160` |
| `kummerBrauerClass_swap` | `L20261018.Ch2.Kummer.Step012_symbol_cup` | 65 | `label:cor:symbol-cup` |
| `kummerClass` | `L20261018.Ch2.Kummer.Step007_kummer_class_coefficient_bridge` | 83 |  |
| `kummerClassHom` | `L20261018.Ch3.BiKummer.Step005_kummer_class_generators` | 22 |  |
| `kummerClassHom_apply` | `L20261018.Ch3.BiKummer.Step005_kummer_class_generators` | 29 |  |
| `kummerClass_eq_h1ToVEquiv_kummerExplicit` | `L20261018.Ch2.Kummer.Step021_bridge_first_segment` | 37 |  |
| `kummerClass_eq_iff` | `L20261018.Ch3.BiKummer.Step005_kummer_class_generators` | 35 |  |
| `kummerClass_eq_muP` | `L20261018.Ch2.Kummer.Step031_t1_model_comparison` | 101 |  |
| `kummerClass_eq_muP'` | `L20261018.Ch2.Kummer.Step038_bridges_without_completeness` | 69 |  |
| `kummerClass_eq_muP_explicitH1` | `L20261018.Ch2.Kummer.Step019_kummer_class_route_a_normal_form` | 72 |  |
| `kummerClass_eq_thetaOne` | `L20261018.Ch2.Kummer.Step027_t1_mu_n_rep_factorization` | 237 |  |
| `kummerClass_eq_thetaOne'` | `L20261018.Ch2.Kummer.Step038_bridges_without_completeness` | 58 |  |
| `kummerClass_eq_zero_iff` | `L20261018.Ch2.Kummer.Step007_kummer_class_coefficient_bridge` | 88 |  |
| `kummerClass_eq_zero_of_residue_eq_one` | `L20261018.Ch2.Hensel.TameSymbol.Step007_tame_symbol_triviality` | 73 | `label:eq:prelim-tame` |
| `kummerClass_eq_zero_of_residue_eq_one_unit` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 226 | `line:739` |
| `kummerClass_inv` | `L20261018.Ch3.BiKummer.Step011_restriction_kernel_eq_u` | 58 |  |
| `kummerClass_isUnit_proof_irrel` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step001_units_cup_vanish_complete` | 62 |  |
| `kummerClass_mem_ker_of_val_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step019_b_tension_resolved` | 63 |  |
| `kummerClass_mem_span_of_mem_closure` | `L20261018.Ch3.BiKummer.Step011_restriction_kernel_eq_u` | 68 |  |
| `kummerClass_mul` | `L20261018.Ch3.BiKummer.Step011_restriction_kernel_eq_u` | 50 |  |
| `kummerClass_mul_pow_eq` | `L20261018.Ch2.Kummer.Step017_kummer_class_pow_identities` | 27 | `label:prop:prelim-kummer-valuation` |
| `kummerClass_neg_one` | `L20261018.Ch2.Hensel.TameSymbol.Step007_tame_symbol_triviality` | 61 | `label:eq:prelim-tame` |
| `kummerClass_oneSub_eq_zero_of_val_pos` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 255 | `line:739` |
| `kummerClass_pair_linearIndependent` | `L20261018.Ch4.Step011_transition_paragraph_4_1_4_2` | 164 | `line:1596; line:1599` |
| `kummerClass_pow` | `L20261018.Ch2.Kummer.Step017_kummer_class_pow_identities` | 13 | `label:prop:prelim-kummer-valuation` |
| `kummerClass_pow_eq_zero` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step005_units_cup_vanish_final_form` | 58 |  |
| `kummerClass_pow_prime` | `L20261018.Ch2.Kummer.Step017_kummer_class_pow_identities` | 22 | `label:prop:prelim-kummer-valuation` |
| `kummerClass_split_gen` | `L20261018.Ch4.Step022_d_residue_field` | 63 |  |
| `kummerClass_surjective` | `L20261018.Ch3.BiKummer.Step011_restriction_kernel_eq_u` | 37 |  |
| `kummerClass_two_ne_zero_Q7` | `L20261018.Witness.Step009_q7_non_cube_unit` | 67 |  |
| `kummerCocycle` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step035_kummer_cocycle_properties` | 57 |  |
| `kummerCocycleQuot` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step039_cocycle_descends` | 57 |  |
| `kummerCocycleQuot_mem_rootsOfUnity` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step040_cocycle_on_quotient` | 156 |  |
| `kummerCocycleQuot_mk` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step040_cocycle_on_quotient` | 92 |  |
| `kummerCocycleQuot_mul` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step040_cocycle_on_quotient` | 114 |  |
| `kummerCocycleQuot_mul_quot` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step040_cocycle_on_quotient` | 128 |  |
| `kummerCocycleQuot_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step040_cocycle_on_quotient` | 101 |  |
| `kummerCocycleQuot_pow_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step040_cocycle_on_quotient` | 143 |  |
| `kummerCocycle_apply` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step035_kummer_cocycle_properties` | 61 |  |
| `kummerCocycle_eq_of_mul_mem_inertia` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step038_cocycle_constant_on_cosets` | 70 |  |
| `kummerCocycle_eq_one_of_mem_inertia` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step035_kummer_cocycle_properties` | 110 |  |
| `kummerCocycle_mul` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step035_kummer_cocycle_properties` | 66 |  |
| `kummerCocycle_mul_right_mem_inertia` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step038_cocycle_constant_on_cosets` | 58 |  |
| `kummerCocycle_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step035_kummer_cocycle_properties` | 91 |  |
| `kummerCocycle_pow_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step035_kummer_cocycle_properties` | 78 |  |
| `kummerCoeffClass` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step041_res_inertia_kummer_class_zero` | 134 |  |
| `kummerCoeffClass_def` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step041_res_inertia_kummer_class_zero` | 140 |  |
| `kummerCoeffClass_res_eq_zero` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step041_res_inertia_kummer_class_zero` | 182 |  |
| `kummerCoeffCocycle` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step041_res_inertia_kummer_class_zero` | 108 |  |
| `kummerCoeffCocycle_eq_zero_of_mem_inertia` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step041_res_inertia_kummer_class_zero` | 166 |  |
| `kummerCoeffCocycle_mem_Z1` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step041_res_inertia_kummer_class_zero` | 126 |  |
| `kummerCoeffCocycle_toMul_coe` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step041_res_inertia_kummer_class_zero` | 115 |  |
| `kummerCoeffEquivMuNRep_available` | `L20261018.Ch2.Kummer.Step044_kummer_coeff_category_entry` | 53 |  |
| `kummerCoeffEquivZMod` | `L20261018.Ch2.Kummer.Step013_mu_p_equiv_zmod` | 41 |  |
| `kummerCoeffEquivZMod_map_smul` | `L20261018.Ch2.Kummer.Step014_mu_p_linear_equiv` | 35 |  |
| `kummerCoeffH2_nsmul_eq_zero` | `L20261018.Infra.Cohomology.Step009_h2_p_torsion` | 33 |  |
| `kummerCoeffInertiaEquiv` | `L20261018.Ch2.Hensel.Inertia.Step035_ker_v_eq_ker_res1` | 84 |  |
| `kummerCoeffInertiaEquiv_apply` | `L20261018.Ch2.Hensel.Inertia.Step035_ker_v_eq_ker_res1` | 99 |  |
| `kummerCoeffLinearEquiv` | `L20261018.Ch2.Kummer.Step007_kummer_class_coefficient_bridge` | 52 |  |
| `kummerCoeffLinearEquiv` | `L20261018.Ch2.Kummer.Step014_mu_p_linear_equiv` | 50 |  |
| `kummerCoeffLinearEquiv_available` | `L20261018.Ch2.Kummer.Step047_kummer_coeff_bridge_chain_known` | 55 |  |
| `kummerCoeffLinearMap` | `L20261018.Ch2.Kummer.Step014_mu_p_linear_equiv` | 43 |  |
| `kummerCoeffMap_bijective` | `L20261018.Ch3.BiKummer.Step006_explicit_restriction_kernel` | 33 |  |
| `kummerCoeffMap_smul_comp` | `L20261018.Ch3.BiKummer.Step006_explicit_restriction_kernel` | 42 |  |
| `kummerCoeffMort` | `L20261018.Ch2.Kummer.Step046_zmod_equiv_kummer_coeff` | 37 |  |
| `kummerCoeffMuRealCohomologyIso` | `L20261018.Ch2.Kummer.Step048_kummer_coeff_bridge_closed` | 72 |  |
| `kummerCoeffMuRealEquiv` | `L20261018.Ch2.Kummer.Step048_kummer_coeff_bridge_closed` | 53 |  |
| `kummerCoeffMuRealIso` | `L20261018.Ch2.Kummer.Step048_kummer_coeff_bridge_closed` | 63 |  |
| `kummerCoeffToKnr` | `L20261018.Ch2.Hensel.Inertia.Step012_kummer_coeff_equivariant` | 82 | `line:8176` |
| `kummerCoeffToKnrAdd` | `L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive` | 114 |  |
| `kummerCoeffToKnrUnits` | `L20261018.Ch2.Hensel.Inertia.Step011_kummer_coeff_to_knr` | 100 | `line:8152; line:8160` |
| `kummerCoeffToKnrUnits_equivariant` | `L20261018.Ch2.Hensel.Inertia.Step012_kummer_coeff_equivariant` | 65 | `line:8176` |
| `kummerCoeffToKnrUnits_mem_ker` | `L20261018.Ch2.Hensel.ResidueMap.Step052_delta_two_candidate_zero` | 123 | `label:prop-units-cohomology; line:8160` |
| `kummerCoeffToKnr_comp_proj_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 105 |  |
| `kummerCoeffToUnits` | `L20261018.Ch2.Hensel.ResidueMap.Step052_delta_two_candidate_zero` | 128 | `label:prop-units-cohomology; line:8160` |
| `kummerCoeffToUnits_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step052_delta_two_candidate_zero` | 134 | `label:prop-units-cohomology; line:8160` |
| `kummerCoeff_nsmul_eq_zero` | `L20261018.Ch2.Kummer.Step045_kummer_coeff_zmod_instance` | 40 |  |
| `kummerCoeff_smul_eq_self` | `L20261018.Ch2.Kummer.Step013_mu_p_equiv_zmod` | 47 |  |
| `kummerCoeff_smul_trivial` | `L20261018.Ch2.Kummer.Step025_t1_reduction_factor_separation` | 75 |  |
| `kummerCor_kummerMap_eq` | `L20261018.Ch3.BiKummer.Step015_h_nrd_kummer_form` | 42 | `label:lem:basic-inclusions` |
| `kummerCupPairing_skew` | `L20261018.Ch2.Kummer.Step012_symbol_cup` | 48 | `label:cor:symbol-cup` |
| `kummerCup_skew` | `L20261018.Ch2.Hensel.ResidueMap.Step032_hskew_discharged` | 45 | `label:prop:prelim-residue` |
| `kummerCup_smul_smul` | `L20261018.Ch2.Hensel.ResidueMap.Step030_r1_scaled_bridge` | 47 |  |
| `kummerExplicit` | `L20261018.Ch3.BiKummer.Step012_basic_inclusions_cor_subset` | 57 | `label:lem:basic-inclusions` |
| `kummerExplicit_eq` | `L20261018.Ch2.Kummer.Step021_bridge_first_segment` | 32 |  |
| `kummerExplicit_eq_zero_of_mem_pow` | `L20261018.Ch3.NormImage.Step008_three_five_u_wiring` | 155 | `label:thm:hs-tate-exact-sequences` |
| `kummerExplicit_inv` | `L20261018.Ch3.NormImage.Step008_three_five_u_wiring` | 52 | `label:thm:hs-tate-exact-sequences` |
| `kummerExplicit_mem_span_of_mem_closure` | `L20261018.Ch3.NormImage.Step008_three_five_u_wiring` | 62 | `label:thm:hs-tate-exact-sequences` |
| `kummerExplicit_mul` | `L20261018.Ch3.NormImage.Step008_three_five_u_wiring` | 34 | `label:thm:hs-tate-exact-sequences` |
| `kummerExplicit_one` | `L20261018.Ch3.NormImage.Step008_three_five_u_wiring` | 40 | `label:thm:hs-tate-exact-sequences` |
| `kummerExplicit_surjective` | `L20261018.Ch3.NormImage.Step008_three_five_u_wiring` | 87 | `label:thm:hs-tate-exact-sequences` |
| `kummerH1Equiv` | `L20261018.Ch2.Kummer.Step007_kummer_class_coefficient_bridge` | 64 |  |
| `kummerH1EquivCanon` | `L20261018.Ch2.Kummer.Step036_kc_scalar_from_coefficient` | 37 |  |
| `kummerH1Equiv_apply_eq` | `L20261018.Ch2.Kummer.Step027_t1_mu_n_rep_factorization` | 108 |  |
| `kummerH1Equiv_apply_eq'` | `L20261018.Ch2.Kummer.Step038_bridges_without_completeness` | 49 |  |
| `kummerH1Equiv_eq_smul_canon` | `L20261018.Ch2.Kummer.Step037_kc_scalar_transfer` | 41 |  |
| `kummerH2Bridge` | `L20261018.Ch2.Kummer.Step050_h2_equiv_h2_z` | 42 |  |
| `kummerIso_residueField` | `L20261018.Ch4.Step048_r2_infinite_residue_certificate` | 74 |  |
| `kummerMapToTrivialFp` | `L20261018.Ch2.Kummer.Step028_t1_explicit_map1_linear` | 145 |  |
| `kummerMapToTrivialFp_eq_merged` | `L20261018.Ch2.Kummer.Step029_t1_group_variable_cancel` | 68 |  |
| `kummerMap_residueField_surjective` | `L20261018.Ch4.Step048_r2_infinite_residue_certificate` | 84 |  |
| `kummerRes_eq_one_iff_explicitRes1_eq_zero` | `L20261018.Ch3.BiKummer.Step006_explicit_restriction_kernel` | 80 |  |
| `kummerRes_kummerIso_eq_one_iff` | `L20261018.Ch2.Kummer.Step004_restriction_kummer_kernel` | 39 |  |
| `kummerRes_kummerMap_a1` | `L20261018.Ch3.BiKummer.Step005_kummer_class_generators` | 74 |  |
| `kummerRes_kummerMap_a2` | `L20261018.Ch3.BiKummer.Step005_kummer_class_generators` | 87 |  |
| `kummerRes_kummerMap_eq_one_iff` | `L20261018.Ch2.Kummer.Step004_restriction_kummer_kernel` | 27 |  |
| `kummerRes_kummerMap_eq_one_iff_mem_sup` | `L20261018.Ch2.Kummer.Step008_bi_kummer_kernel_restriction` | 36 |  |
| `kummerRes_kummerMap_eq_one_of_mem_sup` | `L20261018.Ch3.BiKummer.Step005_kummer_class_generators` | 64 |  |
| `kummerRes_toAdd_eq` | `L20261018.Ch3.BiKummer.Step006_explicit_restriction_kernel` | 59 |  |
| `kummerResidueAdd` | `L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive` | 124 |  |
| `kummerResidueAdd_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 135 |  |
| `kummerResidueH1ZMod` | `L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive` | 174 |  |
| `kummerResidueH1ZMod_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 150 |  |
| `kummerResidueH1ZMod_spec` | `L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive` | 186 |  |
| `kummerResidueInt` | `L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive` | 143 |  |
| `kummerResidueInt_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive` | 152 |  |
| `kummerResidueInt_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 143 |  |
| `kummerResidueInt_torsion` | `L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive` | 161 |  |
| `kummerResidueMap` | `L20261018.Ch2.Hensel.Inertia.Step012_kummer_coeff_equivariant` | 100 | `line:8176` |
| `kummerResidueMap_eq_add` | `L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive` | 133 |  |
| `kummerSeries_mem_Knr` | `L20261018.Ch2.Hensel.Inertia.Step011_kummer_coeff_to_knr` | 60 | `line:8152; line:8160` |
| `kummerUnit` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step037_cocycle_unit_valued` | 62 |  |
| `kummerUnitOn` | `L20261018.Ch2.Hensel.Inertia.Step011_kummer_coeff_to_knr` | 82 | `line:8152; line:8160` |
| `kummerUnitOn_coe` | `L20261018.Ch2.Hensel.Inertia.Step011_kummer_coeff_to_knr` | 93 | `line:8152; line:8160` |
| `kummerUnit_coe` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step037_cocycle_unit_valued` | 93 |  |
| `kummerUnit_eq_one_of_mem_inertia` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step037_cocycle_unit_valued` | 121 |  |
| `kummerUnit_mem_rootsOfUnity` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step040_cocycle_on_quotient` | 203 |  |
| `kummerUnit_pow_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step037_cocycle_unit_valued` | 102 |  |
| `kummer_injective_available` | `L20261018.Infra.Cohomology.Step008_recon_availability_lock` | 47 |  |
| `kummer_range_available` | `L20261018.Infra.Cohomology.Step008_recon_availability_lock` | 53 |  |
| `lagrangeFactor_eq` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 327 |  |
| `lagrangeFactor_mem` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 337 |  |
| `le_mul_pow_of_kummerField_eq` | `L20261018.Ch2.Kummer.Step005_bi_kummer_kernel_field` | 40 |  |
| `leftMulMatrix_apply_eq` | `L20261018.Ch2.Hensel.Valuation.Step019_left_mul_matrix_sum` | 26 |  |
| `leftMulMatrix_entry_of_le` | `L20261018.Ch2.Hensel.Valuation.Step020_left_mul_matrix_shape` | 29 |  |
| `leftMulMatrix_entry_of_lt` | `L20261018.Ch2.Hensel.Valuation.Step020_left_mul_matrix_shape` | 66 |  |
| `leftMulMatrix_eq_mapMatrix_coeffMatrix` | `L20261018.Ch2.Hensel.Valuation.Step022_norm_congruence` | 89 |  |
| `lemma_3_1_1` | `L20261018.Core.Step001_bi_kummer_data` | 73 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `lemma_3_1_1_kummer` | `L20261018.Ch3.BiKummer.Step002_basic_inclusions_paper_objects` | 33 | `label:lem:basic-inclusions; label:lem:orthogonal` |
| `lemma_3_1_2` | `L20261018.Core.Step001_bi_kummer_data` | 98 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `lemma_3_1_2_galo` | `L20261018.Ch3.BiKummer.Step011_restriction_kernel_eq_u` | 156 |  |
| `lemma_3_1_2_galo'` | `L20261018.Ch3.BiKummer.Step013_orthogonal_roots_trivial` | 57 | `label:lem:orthogonal` |
| `lemma_3_1_3` | `L20261018.Core.Step001_bi_kummer_data` | 138 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `lemma_3_1_3_kummer` | `L20261018.Ch3.BiKummer.Step002_basic_inclusions_paper_objects` | 45 | `label:lem:basic-inclusions; label:lem:orthogonal` |
| `lemma_3_3_1` | `L20261018.Core.Step001_bi_kummer_data` | 283 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `lemma_3_3_1_galo` | `L20261018.Ch3.BiKummer.Step015_h_nrd_kummer_form` | 117 | `label:lem:basic-inclusions` |
| `lemma_3_3_2` | `L20261018.Core.Step001_bi_kummer_data` | 292 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `lemma_3_3_2_explicit` | `L20261018.Ch3.BiKummer.Step012_basic_inclusions_cor_subset` | 85 | `label:lem:basic-inclusions` |
| `lemma_3_3_3` | `L20261018.Core.Step001_bi_kummer_data` | 310 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `lemma_3_3_3_continuous` | `L20261018.Ch2.Kummer.Step003_triple_cup_product` | 99 |  |
| `lemma_3_3_3_kummer` | `L20261018.Ch3.BiKummer.Step002_basic_inclusions_paper_objects` | 61 | `label:lem:basic-inclusions; label:lem:orthogonal` |
| `levelP` | `L20261018.Ch2.Hensel.Inertia.Step026_hom_inertia_mu_p_eq_zmod` | 98 |  |
| `liftOf` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 238 |  |
| `liftOf_surjective_of_adjoin_eq_top` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 450 |  |
| `liftOf_x` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 252 |  |
| `liftOf_y` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 264 |  |
| `linearCombination_surjective` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 376 |  |
| `linearIndependent_Phi` | `L20261018.Core.Step001_bi_kummer_data` | 119 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `linearIndependent_a1a2` | `L20261018.Core.Step001_bi_kummer_data` | 494 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `locB` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 85 | `label:lemma-additive-hilbert90` |
| `longExact_exact₁` | `L20261018.Ch2.Hensel.ResidueMap.Step048_integral_bockstein_range_complete` | 12 |  |
| `mE` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 105 |  |
| `mE_cup` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 112 |  |
| `mF` | `L20261018.Witness.Step026_f7t_principal_units_cube` | 39 |  |
| `mF'` | `L20261018.Witness.Step027_f7t_unit_cube_from_residue` | 38 |  |
| `mF''` | `L20261018.Witness.Step028_f7t_same_cube_class` | 33 |  |
| `mapField` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 41 | `line:8156; line:8160` |
| `mapField_finite` | `L20261018.Ch2.Hensel.Inertia.Step009_galois_preserves_knr` | 46 | `line:8156; line:8160` |
| `map_e_bL` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 160 |  |
| `map_fCG_apply` | `L20261018.Infra.Cohomology.Coinduced.Step026_delta_two_inf_two_zero` | 79 |  |
| `map_iTame_comp_map_deltaZeroBar` | `L20261018.Infra.Cohomology.ResidueLES.Step005_delta_two_comp_inf_zero` | 86 |  |
| `map_inertiaSubgroup_eq_inertiaLoc` | `L20261018.Ch2.Hensel.Inertia.Step016_inertia_loc_carrier_alignment` | 67 | `line:8` |
| `map_maximalIdeal` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 109 |  |
| `map_restrictScalarsIntEquiv_comm` | `L20261018.Infra.Cohomology.Step002_map_coefficient_restriction` | 37 |  |
| `map_zero_eq` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 87 |  |
| `matrixFinOneAlgEquiv` | `L20261018.Ch2.Brauer.Step008_matrix_elimination_degree` | 82 |  |
| `maximalIdeal_O_eq_span_pi` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 102 |  |
| `mem_E` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 441 |  |
| `mem_KnrSubfield` | `L20261018.Ch2.Hensel.Inertia.Step007_knr_correct_carrier` | 123 | `line:8152` |
| `mem_O_iff` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 50 |  |
| `mem_O_iff_exists_powerSeries` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 69 |  |
| `mem_U_iff` | `L20261018.Core.Step001_bi_kummer_data` | 66 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `mem_Uperp_iff` | `L20261018.Core.Step001_bi_kummer_data` | 69 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `mem_bot_of_pow_eq_one` | `L20261018.Ch2.Kummer.Step009_pth_power_field_trivial` | 37 |  |
| `mem_contInvB_iff` | `L20261018.Infra.Cohomology.ResidueLES.Step018_cont_inv_b_pointwise` | 40 |  |
| `mem_contKI` | `L20261018.Infra.Cohomology.ResidueLES.Step012_continuous_t_carrier` | 126 | `line:9528` |
| `mem_diagonal_single` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 387 |  |
| `mem_fixedPoints_zmod` | `L20261018.Infra.Cohomology.Coinduced.Step030_coefficient_bridge_m_inv` | 33 |  |
| `mem_inertia` | `L20261018.Ch2.Hensel.Inertia.Step028_inertia_subgroup_galois` | 117 |  |
| `mem_inertia_iff_residueAct_eq_one` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 206 |  |
| `mem_inertia_iff_residue_eq` | `L20261018.Ch2.Hensel.Inertia.Step030_inertia_maximal_ideal` | 78 |  |
| `mem_inertia_iff_sub_mem_maximalIdeal` | `L20261018.Ch2.Hensel.Inertia.Step030_inertia_maximal_ideal` | 51 |  |
| `mem_integer_of_pow_eq_one` | `L20261018.Ch2.Hensel.ResidueMap.Step062_mu_p_residue_full_chain` | 81 |  |
| `mem_integer_vCompat` | `L20261018.Ch2.Hensel.Valuation.Step033_val_compat_exists` | 47 |  |
| `mem_integralClosure_algEquiv` | `L20261018.Ch2.Hensel.Valuation.Step039_integral_closure_stable` | 63 |  |
| `mem_ker_resMG_iff` | `L20261018.Ch3.NormImage.Step008_three_five_u_wiring` | 174 | `label:thm:hs-tate-exact-sequences` |
| `mem_ker_toLinearMap_iff` | `L20261018.Ch3.NormImage.Step014_three_six_assembly_linearize` | 63 |  |
| `mem_maximalIdeal_iff_not_isUnit` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 105 | `line:739` |
| `mem_maximalIdeal_vCompat` | `L20261018.Ch2.Hensel.Valuation.Step033_val_compat_exists` | 70 |  |
| `mem_normGroup_adjoinRoot` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step003_norm_group_adjoin_root` | 84 |  |
| `mem_normGroup_of_powClassGen` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step002_units_cup_vanish_reduction` | 79 |  |
| `mem_orth_iff` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 111 | `label:lem:ramified-vanishing` |
| `mem_orth_iff` | `L20261018.Ch4.Step015_thm_ramified_1_sec_2_4_only` | 29 | `line:1636` |
| `mem_paperUseSpan_pi` | `L20261018.Ch4.Step020_delta_two_eq_res_carrier` | 69 |  |
| `mem_paperUseSpan_uu` | `L20261018.Ch4.Step020_delta_two_eq_res_carrier` | 74 |  |
| `mem_plane_iff` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 107 | `label:lem:ramified-vanishing` |
| `mem_pow_of_mem_normGroup_of_valOfUnitOf_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step027_norm_group_form` | 39 |  |
| `mem_range_toLinearMap_iff` | `L20261018.Ch3.NormImage.Step014_three_six_assembly_linearize` | 57 |  |
| `mem_subring_of_pow_mem` | `L20261018.Ch2.Hensel.ResidueMap.Step043_units_mod_pth_powers_paper_level` | 72 | `label:prop:prelim-kummer-valuation; line:992` |
| `mem_sup_of_isPow_in_kummerField` | `L20261018.Ch2.Kummer.Step006_bi_kummer_kernel_intersection` | 40 |  |
| `mem_unitFiltration_zero_of_val_eq_one` | `L20261018.Ch2.Hensel.Inertia.Step037_unramified_kummer_paper_level` | 122 |  |
| `mem_zpowers_gen` | `L20261018.Ch2.Brauer.Step026_carry_cocycle_class_cyclic` | 44 |  |
| `mem_zpowers_gen'` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 131 |  |
| `merkurjevSuslin_of_spanned_by_one` | `L20261018.Ch2.Hensel.TameSymbol.Step015_tame_symbol_hyp_from_merkurjev_suslin` | 273 |  |
| `merkurjevSuslin_of_subsingleton` | `L20261018.Ch2.Hensel.TameSymbol.Step015_tame_symbol_hyp_from_merkurjev_suslin` | 248 |  |
| `mkB` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 87 | `label:lemma-additive-hilbert90` |
| `mkB_add` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 114 | `label:lemma-additive-hilbert90` |
| `mkB_invB` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 108 | `label:lemma-additive-hilbert90` |
| `mk_eq_of_eq_cube_mul` | `L20261018.Witness.Step031_f7t_finite_cube_classes` | 40 |  |
| `mk_matrix_eq` | `L20261018.Ch2.Brauer.Step008_matrix_elimination_degree` | 55 |  |
| `mk_matrix_eq_one` | `L20261018.Ch2.Brauer.Step007_brauer_interfaces` | 73 |  |
| `mk_mul_coe` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 57 |  |
| `mk_mul_coe_I` | `L20261018.Infra.Cohomology.Coinduced.Step013_coinduced_invariants_backward` | 84 |  |
| `moduleFinite_H0'` | `L20261018.Ch3.NormImage.Step011_three_six_h1_module` | 71 |  |
| `moduleFinite_H0ex` | `L20261018.Ch3.NormImage.Step019_three_six_short_names` | 42 |  |
| `moduleFinite_K2` | `L20261018.Ch3.NormImage.Step009_three_six_finiteness_k2` | 61 |  |
| `moduleFinite_K2'` | `L20261018.Ch3.NormImage.Step012_three_six_k2_submodule` | 59 |  |
| `moduleFinite_K2ex` | `L20261018.Ch3.NormImage.Step019_three_six_short_names` | 48 |  |
| `moduleFinite_adjoinRoot` | `L20261018.Ch4.Step032_v_and_d_exists` | 31 |  |
| `moduleFixedPoints` | `L20261018.Ch3.NormImage.Step012_three_six_k2_submodule` | 33 |  |
| `moduleH0ex` | `L20261018.Ch3.NormImage.Step019_three_six_short_names` | 37 |  |
| `moduleH1fixing` | `L20261018.Ch3.NormImage.Step011_three_six_h1_module` | 38 |  |
| `moduleH2` | `L20261018.Ch3.NormImage.Step012_three_six_k2_submodule` | 41 |  |
| `module_H0` | `L20261018.Ch3.NormImage.Step011_three_six_h1_module` | 61 |  |
| `module_K2` | `L20261018.Ch3.NormImage.Step012_three_six_k2_submodule` | 55 |  |
| `monic_X_pow_sub_C_uniformizer` | `L20261018.Ch2.Hensel.Valuation.Step025_norm_smul_uniformizer` | 30 |  |
| `monic_henselPoly` | `L20261018.Witness.Step026_f7t_principal_units_cube` | 47 |  |
| `mono_qSES_f` | `L20261018.Infra.Cohomology.ResidueLES.Step002_t_cokernel_constructed` | 69 |  |
| `mono_δ_cokerSES` | `L20261018.Infra.Cohomology.ResidueLES.Step004_i_star_delta_zero_bar` | 86 |  |
| `monomialSubalgebra` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 334 |  |
| `monomial_mul_monomial` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 287 |  |
| `monomials` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 277 |  |
| `muCohomologyIso` | `L20261018.Ch2.Kummer.Step042_mu_p_module_structure` | 176 |  |
| `muGens` | `L20261018.Ch2.Kummer.Step042_mu_p_module_structure` | 107 |  |
| `muGens_ne_zero` | `L20261018.Ch2.Kummer.Step042_mu_p_module_structure` | 117 |  |
| `muGens_toMul` | `L20261018.Ch2.Kummer.Step042_mu_p_module_structure` | 114 |  |
| `muH1Equiv` | `L20261018.Ch2.Kummer.Step043_kummer_bridge_on_h2` | 40 |  |
| `muH2Equiv` | `L20261018.Ch2.Kummer.Step043_kummer_bridge_on_h2` | 46 |  |
| `muH2Equiv_available` | `L20261018.Ch2.Kummer.Step047_kummer_coeff_bridge_chain_known` | 66 |  |
| `muHom` | `L20261018.Ch2.Kummer.Step028_t1_explicit_map1_linear` | 118 |  |
| `muHomAbs` | `L20261018.Ch2.Kummer.Step030_t1_bridge_gm_bypass` | 67 |  |
| `muHomAbs_equivariant` | `L20261018.Ch2.Kummer.Step030_t1_bridge_gm_bypass` | 74 |  |
| `muHom_comp_kce` | `L20261018.Ch2.Kummer.Step028_t1_explicit_map1_linear` | 124 |  |
| `muHom_equivariant` | `L20261018.Ch2.Kummer.Step028_t1_explicit_map1_linear` | 134 |  |
| `muKummerCoeff` | `L20261018.Ch2.Kummer.Step048_kummer_coeff_bridge_closed` | 58 |  |
| `muLinearEquiv` | `L20261018.Ch2.Kummer.Step042_mu_p_module_structure` | 127 |  |
| `muNRepCohomologyEquivTrivialFp_apply_eq_smul` | `L20261018.Ch2.Kummer.Step016_zeta_independence_carrier` | 152 |  |
| `muNRepCohomologyEquivTrivialFp_one_kummerClass` | `L20261018.Ch2.Kummer.Step028_t1_explicit_map1_linear` | 168 |  |
| `muNRepEquivTrivialFp_eq_smul` | `L20261018.Ch2.Kummer.Step016_zeta_independence_carrier` | 118 |  |
| `muNRepH1Equiv_apply_eq` | `L20261018.Ch2.Kummer.Step027_t1_mu_n_rep_factorization` | 146 |  |
| `muNRepIsoTrivialFp_hom_eq_smul` | `L20261018.Ch2.Kummer.Step016_zeta_independence_carrier` | 138 |  |
| `muNRep_explicitH1_eq_restrictScalars` | `L20261018.Ch2.Kummer.Step020_route_b_normal_form` | 41 |  |
| `muNRep_smul_trivial` | `L20261018.Ch2.Kummer.Step025_t1_reduction_factor_separation` | 80 |  |
| `muNRep_smul_trivial_available` | `L20261018.Ch2.Kummer.Step044_kummer_coeff_category_entry` | 58 |  |
| `muP` | `L20261018.Ch2.Kummer.Step042_mu_p_module_structure` | 13 |  |
| `muP` | `L20261018.Core.Step001_bi_kummer_data` | 641 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `muPCoeffIso` | `L20261018.Ch2.Hensel.ResidueMap.Step051_h1_z_equiv_galo_v` | 123 | `line:1050` |
| `muPIso` | `L20261018.Ch2.Kummer.Step042_mu_p_module_structure` | 171 |  |
| `muPIso_available` | `L20261018.Ch2.Kummer.Step047_kummer_coeff_bridge_chain_known` | 60 |  |
| `muPQuot` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 96 |  |
| `muPQuot_ρ` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 102 |  |
| `muPReal` | `L20261018.Ch2.Kummer.Step042_mu_p_module_structure` | 166 |  |
| `muP_eq_ofDiscreteModule` | `L20261018.Infra.Cohomology.ResidueLES.Step007_continuous_615` | 62 |  |
| `muP_explicitH1_eq_restrictScalars` | `L20261018.Ch2.Kummer.Step019_kummer_class_route_a_normal_form` | 48 |  |
| `muP_trivial_available` | `L20261018.Infra.Cohomology.Step008_recon_availability_lock` | 61 |  |
| `muP_ρ` | `L20261018.Core.Step001_bi_kummer_data` | 646 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `muPairing` | `L20261018.Core.Step001_bi_kummer_data` | 652 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `muPairing_flip` | `L20261018.Core.Step001_bi_kummer_data` | 670 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `mulPairing` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 130 |  |
| `mulPairing_equivariant` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 149 |  |
| `mulRight` | `L20261018.Ch2.Brauer.Step002_reduced_norm_maximal_subfield` | 43 |  |
| `mulRight_conj` | `L20261018.Ch3.BiKummer.Step004_h_nrd_well_defined` | 48 |  |
| `mulRight_inc` | `L20261018.Ch2.Brauer.Step002_reduced_norm_maximal_subfield` | 51 |  |
| `mul_E_apply` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 396 |  |
| `mul_conj_mul_inv_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step012_units_cup_vanish_unconditional` | 73 |  |
| `mul_mem_span` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 310 |  |
| `natCard_h1Inertia_eq` | `L20261018.Ch2.Hensel.Inertia.Step038_h1_inertia_one_dim` | 67 |  |
| `natCard_hom_cont_inertiaLoc_eq` | `L20261018.Ch2.Hensel.Inertia.Step038_h1_inertia_one_dim` | 54 |  |
| `natCard_hom_cont_tameModel_zmod_eq` | `L20261018.Ch2.Hensel.Inertia.Step026_hom_inertia_mu_p_eq_zmod` | 210 |  |
| `natCard_hom_cont_tameModel_zmod_le` | `L20261018.Ch2.Hensel.Inertia.Step025_h1_inertia_finite` | 99 |  |
| `natCard_kummerCoeff_available` | `L20261018.Ch2.Kummer.Step044_kummer_coeff_category_entry` | 48 |  |
| `natCard_units_of_finite` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step008_residue_field_units_cyclic` | 46 |  |
| `natCard_zmodDual_inertiaLoc_le` | `L20261018.Ch2.Hensel.Inertia.Step025_h1_inertia_finite` | 141 |  |
| `natCoprime_of_zmod_ne_zero` | `L20261018.Ch2.Kummer.Step016_zeta_independence_carrier` | 110 |  |
| `nbAddEquiv` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 123 | `label:lemma-additive-hilbert90` |
| `nbLinEquiv` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 130 | `label:lemma-additive-hilbert90` |
| `nbLinEquiv_smul` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 166 | `label:lemma-additive-hilbert90` |
| `neZero_two_zmod` | `L20261018.Ch3.BiKummer.Step001_bi_kummer_data_from_kummer` | 56 |  |
| `neZero_two_zmod` | `L20261018.Ch3.BiKummer.Step011_restriction_kernel_eq_u` | 141 |  |
| `neZero_two_zmod` | `L20261018.Ch3.NormImage.Step018_three_six_nezero_two` | 23 |  |
| `ne_of_coprime` | `L20261018.Ch2.Hensel.Inertia.Step038_h1_inertia_one_dim` | 49 |  |
| `nonempty_algEquiv` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 518 |  |
| `nonempty_algEquiv_crossedProduct` | `L20261018.Ch2.Brauer.Step023_symbol_alg_equiv_crossed_product` | 49 |  |
| `nonempty_algEquiv_of_finrank` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 422 |  |
| `nonempty_algEquiv_of_matrix_algEquiv` | `L20261018.Ch2.Brauer.Step008_matrix_elimination_degree` | 63 |  |
| `nonempty_algEquiv_of_mk_eq_crossedProductClass` | `L20261018.Ch2.Brauer.Step008_matrix_elimination_degree` | 159 |  |
| `nonempty_algEquiv_of_wedderburn` | `L20261018.Ch2.Brauer.Step008_matrix_elimination_degree` | 127 |  |
| `nonempty_divisionRep` | `L20261018.Ch2.Brauer.Step029_index_function_h2` | 63 |  |
| `nonempty_henselResidueData_iff` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 251 | `line:1050; line:1608; line:1636; line:1648` |
| `nonempty_henselResidueData_iff_tameSymbolFactors` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 236 | `label:eq:prelim-tame; line:1050` |
| `nonempty_henselResidueData_of_merkurjevSuslin` | `L20261018.Ch2.Hensel.TameSymbol.Step016_tame_symbol_hyp_merkurjev_suslin` | 95 | `line:1050` |
| `nonempty_valCompat` | `L20261018.Witness.Step038_val_compat_nonempty` | 110 |  |
| `nontrivial_adjoinRoot_X_pow` | `L20261018.Ch2.Hensel.Valuation.Step015_norm_s_eq_zero` | 31 |  |
| `nontrivial_adjoinRoot_uniformizer_f` | `L20261018.Ch2.Hensel.Valuation.Step025_norm_smul_uniformizer` | 44 |  |
| `normGroup` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step002_units_cup_vanish_reduction` | 16 |  |
| `normUnits_mem_pow_of_valOfUnitOf_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step026_unit_norm_pth_power_from_valuation` | 71 |  |
| `normUnits_mem_pow_of_val_eq_zero` | `L20261018.Ch2.Hensel.ResidueMap.Step025_unit_norm_pth_power` | 44 |  |
| `norm_algebraMap_adjoinRoot` | `L20261018.Ch2.Hensel.Valuation.Step009_norm_residue_basic` | 40 |  |
| `norm_eq_zero_of_nilpotent` | `L20261018.Infra.Algebra.Step001_norm_monoid_hom` | 50 |  |
| `norm_image_le_nrdOfIso_image` | `L20261018.Ch2.Brauer.Step003_reduced_norm_any_crossed_product` | 84 |  |
| `norm_mem_integer` | `L20261018.Ch2.Hensel.Valuation.Step022_norm_congruence` | 110 |  |
| `norm_mem_range_nrd_units` | `L20261018.Ch2.Brauer.Step002_reduced_norm_maximal_subfield` | 103 |  |
| `norm_mul` | `L20261018.Infra.Algebra.Step001_norm_monoid_hom` | 40 |  |
| `norm_pow` | `L20261018.Infra.Algebra.Step001_norm_monoid_hom` | 45 |  |
| `norm_pow_root_mul` | `L20261018.Ch2.Hensel.Valuation.Step025_norm_smul_uniformizer` | 54 |  |
| `norm_range_subset_nrd_range_of_mk_eq` | `L20261018.Ch2.Brauer.Step009_h_nrd_from_field_norm_algebra` | 51 |  |
| `norm_residue_eq_pow` | `L20261018.Ch2.Hensel.Valuation.Step022_norm_congruence` | 120 |  |
| `norm_root_X_pow_sub_C` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step003_norm_group_adjoin_root` | 17 |  |
| `norm_root_eq` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step003_norm_group_adjoin_root` | 57 |  |
| `norm_root_eq'` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step003_norm_group_adjoin_root` | 62 |  |
| `norm_root_eq_zero_adjoinRoot` | `L20261018.Ch2.Hensel.Valuation.Step015_norm_s_eq_zero` | 40 |  |
| `norm_root_uniformizer_adjoinRoot` | `L20261018.Ch2.Hensel.Valuation.Step008_adjoin_root_model` | 38 |  |
| `normalBasisRepr_smul` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 139 | `label:lemma-additive-hilbert90` |
| `normal_KnrLoc` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 88 | `label:sec:cohomology-complete-dv` |
| `normal_inertiaAbs_of_eq` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 165 | `label:sec:cohomology-complete-dv` |
| `normal_inertiaLoc` | `L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat` | 99 | `label:sec:cohomology-complete-dv` |
| `normalizedValuation_seven_Q7` | `L20261018.Witness.Step014_q7_val_compat` | 72 |  |
| `notMem_maximalIdeal_of_isUnit` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 114 | `line:739` |
| `notMem_pow_of_notMem_powerSubgroup` | `L20261018.Ch3.BiKummer.Step016_hind_kummer` | 53 |  |
| `notMem_powerSubgroup_of_isUniformizer` | `L20261018.Witness.Step003_nondegenerate_nonzero_cup` | 89 |  |
| `not_ch4TameSymbolHyp_of_not_disjoint` | `L20261018.Ch2.Hensel.TameSymbol.Step005_tame_symbol_hyp_iff_r1_r2` | 81 |  |
| `not_exists_cube_pi` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 152 |  |
| `not_exists_cube_two` | `L20261018.Witness.Step024_f7t_not_cube` | 74 |  |
| `not_exists_cube_two_Q7` | `L20261018.Witness.Step009_q7_non_cube_unit` | 41 |  |
| `not_isOfFinOrder_of_infinite` | `L20261018.Ch2.Hensel.Inertia.Step015_cd_p_procyclic_criterion` | 95 | `line:8` |
| `not_neg_val_of_mem_integer` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 144 | `line:739` |
| `not_pos_val_of_isUnit` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 133 | `line:739` |
| `not_pow_of_irreducible` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step004_capelli_criterion` | 78 |  |
| `not_pow_of_zval_eq_one` | `L20261018.Ch2.Hensel.Valuation.Step034_discharge_pi_hypotheses` | 66 |  |
| `not_pow_unitOf` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step012_units_cup_vanish_unconditional` | 57 |  |
| `not_pow_unitOf'` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 100 |  |
| `not_ringChar_dvd_of_coprime` | `L20261018.Ch4.Step042_hd_infl_final_form` | 44 |  |
| `nrd` | `L20261018.Ch2.Brauer.Step002_reduced_norm_maximal_subfield` | 83 |  |
| `nrdOfIso` | `L20261018.Ch2.Brauer.Step003_reduced_norm_any_crossed_product` | 53 |  |
| `nrdOfIso_independent` | `L20261018.Ch2.Brauer.Step003_reduced_norm_any_crossed_product` | 61 |  |
| `nrd_algEquiv` | `L20261018.Ch3.BiKummer.Step004_h_nrd_well_defined` | 63 |  |
| `nrd_algEquivOfCoboundary` | `L20261018.Ch3.BiKummer.Step004_h_nrd_well_defined` | 70 |  |
| `nrd_algEquiv_of_cohomologous` | `L20261018.Ch3.BiKummer.Step009_h_nrd_presentation_independent` | 116 |  |
| `nrd_algEquiv_self` | `L20261018.Ch3.BiKummer.Step009_h_nrd_presentation_independent` | 101 |  |
| `nrd_conj_unit` | `L20261018.Ch3.BiKummer.Step009_h_nrd_presentation_independent` | 85 |  |
| `nrd_image_eq_of_algEquiv` | `L20261018.Ch3.BiKummer.Step009_h_nrd_presentation_independent` | 130 |  |
| `nrd_image_eq_of_cohomologous` | `L20261018.Ch3.BiKummer.Step004_h_nrd_well_defined` | 78 |  |
| `nrd_inc` | `L20261018.Ch2.Brauer.Step002_reduced_norm_maximal_subfield` | 88 |  |
| `nrd_inv_unit` | `L20261018.Ch3.BiKummer.Step009_h_nrd_presentation_independent` | 73 |  |
| `nrd_mul` | `L20261018.Ch2.Brauer.Step002_reduced_norm_maximal_subfield` | 92 |  |
| `nrd_one` | `L20261018.Ch3.BiKummer.Step009_h_nrd_presentation_independent` | 66 |  |
| `nsmulAddMonoidHom_kummerCoeff_eq_zero` | `L20261018.Infra.Cohomology.Step009_h2_p_torsion` | 24 |  |
| `nsmul_H1_eq_zero` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 46 | `label:thm:hs-tate-exact-sequences` |
| `nsmul_H1_fixingSubgroup` | `L20261018.Ch3.NormImage.Step011_three_six_h1_module` | 31 |  |
| `numDen` | `L20261018.Ch2.Hensel.Valuation.Step032_val_compat_multiplicative` | 49 |  |
| `numDen_spec` | `L20261018.Ch2.Hensel.Valuation.Step032_val_compat_multiplicative` | 52 |  |
| `num_ne_zero_of_mul_eq` | `L20261018.Ch2.Hensel.Valuation.Step032_val_compat_multiplicative` | 34 |  |
| `ofAdd_one_pow` | `L20261018.Ch2.Brauer.Step018_product_cocycle_sum` | 25 |  |
| `ofAdd_one_pow_eq` | `L20261018.Ch2.Brauer.Step022_adjoin_top_assembly` | 24 |  |
| `ofAdd_one_zpow_gen` | `L20261018.Ch4.Step022_d_residue_field` | 47 |  |
| `ofPowerSeries_C_eq` | `L20261018.Witness.Step024_f7t_not_cube` | 39 |  |
| `ofPowerSeries_X_ne_zero` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 74 |  |
| `of_algEquiv` | `L20261018.Ch3.BiKummer.Step014_splitting_field` | 48 |  |
| `of_apply` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 66 |  |
| `oneSub` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 190 | `line:739` |
| `oneSub_coe` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 203 | `line:739` |
| `oneSub_eq_neg_subOne` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 209 | `line:739` |
| `one_add_mem_cubes` | `L20261018.Witness.Step026_f7t_principal_units_cube` | 66 |  |
| `one_add_subset_pow` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step007_units_surject_residue` | 75 |  |
| `one_mem_inertiaSet` | `L20261018.Ch2.Hensel.Valuation.Step040_integral_closure_value_preserving` | 88 |  |
| `orderOf_eq_prime_of_pow_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step009_units_group_lemma` | 38 |  |
| `orderOf_gen` | `L20261018.Ch2.Brauer.Step026_carry_cocycle_class_cyclic` | 52 |  |
| `orderOf_gen'` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 141 |  |
| `orth` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 101 | `label:lem:ramified-vanishing` |
| `orth_eq_bot_F` | `L20261018.Witness.Step025_f7t_hne_hval` | 185 | `line:1608` |
| `orth_eq_bot_F_uncond` | `L20261018.Witness.Step032_f7t_v_finite_dimensional` | 77 | `line:1608` |
| `orth_eq_bot_Q7` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 143 |  |
| `orth_eq_bot_general` | `L20261018.Ch4.Step036_ch4_three_without_finite_residue` | 60 |  |
| `orth_eq_bot_noBridge` | `L20261018.Ch4.Step033_ch4_three_and_exists_d` | 102 | `line:1050; line:1608; line:1636; line:1648` |
| `orth_eq_bot_noFinite` | `L20261018.Ch2.Hensel.ResidueMap.Step036_residue_cup_product_interface` | 76 | `label:lemma-residue-cup-product; line:1608; line:1636; line:1648` |
| `orth_eq_bot_of_cyclicUnits` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 225 |  |
| `orth_eq_bot_of_discrete_valuation` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 185 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `orth_eq_bot_of_discrete_valuation'` | `L20261018.Ch4.Step031_ch4_closed_units_cup_vanish` | 52 | `line:1608; line:1636; line:1648` |
| `orth_eq_bot_of_discrete_valuation''` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step013_exists_d_and_ch4_unconditional` | 60 |  |
| `orth_eq_bot_of_discrete_valuation_nofin` | `L20261018.Ch4.Step037_ch4_without_finite_dimensional_v` | 228 | `line:1636` |
| `orth_eq_bot_of_disjoint` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step015_b_reduced_to_disjoint` | 103 |  |
| `orth_eq_bot_of_merkurjevSuslin` | `L20261018.Ch4.Step039_ch4_four_without_finite_residue` | 101 | `line:1050; line:1608; line:1636; line:1648` |
| `orth_eq_bot_paper` | `L20261018.Ch4.Step037_ch4_without_finite_dimensional_v` | 281 | `line:1636` |
| `orth_eq_bot_paper_route` | `L20261018.Ch4.Step012_ramified_vanishing_paper_route` | 113 | `line:1608` |
| `orth_eq_bot_paper_route_hensel` | `L20261018.Ch4.Step014_ramified_vanishing_hensel_level` | 182 | `line:1608` |
| `orth_eq_bot_paper_route_hensel_nofin` | `L20261018.Ch4.Step037_ch4_without_finite_dimensional_v` | 94 | `line:1636` |
| `orth_eq_bot_paper_route_residue_facts` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 327 | `line:1050; line:1608; line:1636; line:1648` |
| `orth_eq_bot_viaResidue` | `L20261018.Ch4.Step047_ch4_three_d_free` | 76 | `line:1608; line:1636; line:1648` |
| `orth_map_eq` | `L20261018.Ch4.Step015_thm_ramified_1_sec_2_4_only` | 46 | `line:1636` |
| `orth_map_eq_free` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 93 | `line:1636; line:1648` |
| `p_smul_V_eq_zero` | `L20261018.Ch2.Kummer.Step017_kummer_class_pow_identities` | 9 | `label:prop:prelim-kummer-valuation` |
| `p_smul_brOfH2` | `L20261018.Ch2.Brauer.Step032_brauer_image_p_torsion` | 21 |  |
| `padicEquiv_closedZpowers_zpowHat_idem` | `L20261018.Ch2.Hensel.Inertia.Step018_procyclic_l_part_sylow` | 136 | `line:9626` |
| `padicEquiv_of_procyclic` | `L20261018.Ch2.Hensel.Inertia.Step015_cd_p_procyclic_criterion` | 53 | `line:8` |
| `padicUnitV` | `L20261018.Witness.Step005_val_compat_qp` | 32 |  |
| `padicUnitV_uniformizer` | `L20261018.Witness.Step005_val_compat_qp` | 42 |  |
| `pair_linearIndependent` | `L20261018.Ch4.Step011_transition_paragraph_4_1_4_2` | 43 | `line:1596; line:1599` |
| `pair_linearIndependent_free` | `L20261018.Ch4.Step014_ramified_vanishing_hensel_level` | 68 | `line:1608` |
| `paperCup` | `L20261018.Ch3.BiKummer.Step017_rank_barrier_unconditional` | 41 | `label:thm:rank-barrier` |
| `paperFormulas_iff_obligation` | `L20261018.Ch2.Hensel.ResidueMap.Step045_residue_prop_two_literal` | 73 | `line:1052` |
| `paperUseSpan` | `L20261018.Ch4.Step020_delta_two_eq_res_carrier` | 47 |  |
| `phi_apply_eq_zero_of_residueSpan_eq_top` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step018_b_logical_tension` | 73 |  |
| `phi_comp` | `L20261018.Ch4.Step008_rank_contradiction_single_phi` | 69 | `line:1646` |
| `phi_comp_free` | `L20261018.Ch4.Step018_single_carrier_thm_ramified` | 65 | `line:1636; line:1637` |
| `phi_range_map` | `L20261018.Ch4.Step008_rank_contradiction_single_phi` | 79 | `line:1646` |
| `phi_range_map_free` | `L20261018.Ch4.Step018_single_carrier_thm_ramified` | 78 | `line:1636; line:1637` |
| `pi` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 84 |  |
| `piO` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 99 |  |
| `piT` | `L20261018.Witness.Step033_f7t_mun_rep_cup_nonzero` | 46 |  |
| `pi_decomp` | `L20261018.Witness.Step030_f7t_pi_power_decomposition` | 40 |  |
| `pi_fin` | `L20261018.Witness.Step024_f7t_not_cube` | 100 |  |
| `pi_hπ` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 120 |  |
| `pi_irred` | `L20261018.Witness.Step024_f7t_not_cube` | 95 |  |
| `pi_mem_O` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 95 |  |
| `pi_val` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 89 |  |
| `plane` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 92 | `label:lem:ramified-vanishing` |
| `powClassGen_of_cyclicUnits` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 114 |  |
| `powClassGen_of_divisible` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 178 |  |
| `powClassGen_of_finite` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 187 |  |
| `powClassGen_of_hensel` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step012_units_cup_vanish_unconditional` | 78 |  |
| `pow_mem_normGroup` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step002_units_cup_vanish_reduction` | 62 |  |
| `pow_ne_uniformizer` | `L20261018.Ch2.Hensel.Valuation.Step004_adjoin_root_degree_p` | 46 |  |
| `pow_ne_uniformizer_unit` | `L20261018.Ch2.Hensel.Valuation.Step004_adjoin_root_degree_p` | 35 |  |
| `pow_surj_on_one_add_maximalIdeal` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step006_principal_units_pow_hensel` | 61 |  |
| `pow_surj_on_one_add_maximalIdeal_ofF` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step006_principal_units_pow_hensel` | 90 |  |
| `powerBasis_root_gen` | `L20261018.Ch2.Hensel.Valuation.Step010_power_basis_s` | 57 |  |
| `powerClass_eq_of_unitsResidue_eq` | `L20261018.Witness.Step028_f7t_same_cube_class` | 68 |  |
| `powerSeriesEquivO` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 97 |  |
| `powerSeriesEquivO_apply` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 102 |  |
| `powerSeriesToO` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 76 |  |
| `powerSeriesToO_coe` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 81 |  |
| `powerSeriesToO_injective` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 85 |  |
| `powerSeriesToO_surjective` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 91 |  |
| `primitiveRoot` | `L20261018.Ch2.Kummer.Step007_kummer_class_coefficient_bridge` | 57 |  |
| `primitiveRoot_spec` | `L20261018.Ch2.Kummer.Step007_kummer_class_coefficient_bridge` | 60 |  |
| `principalUnit_exists_pow_eq` | `L20261018.Ch2.Hensel.ResidueMap.Step002_unit_reduction_principal_units` | 48 | `label:lem:ramified-vanishing; label:prop:prelim-kummer-valuation; line:1017` |
| `principalUnit_mem_pow_range_of_eq_one` | `L20261018.Ch2.Hensel.ResidueMap.Step056_kummer_valuation_abstract_hensel` | 99 | `label:prop:prelim-kummer-valuation` |
| `principalUnit_pow_surjective` | `L20261018.Ch2.Hensel.ResidueMap.Step001_open_residual_advance` | 58 | `line:1017` |
| `principalUnit_pow_surjective_of_hensel` | `L20261018.Ch2.Hensel.Valuation.Step002_principal_units_without_completeness` | 62 | `line:1017; line:1622` |
| `principalUnit_pow_surjective_prime` | `L20261018.Ch2.Hensel.ResidueMap.Step001_open_residual_advance` | 64 | `line:1017` |
| `principalUnits_le_pow_range` | `L20261018.Ch2.Hensel.ResidueMap.Step002_unit_reduction_principal_units` | 43 | `label:lem:ramified-vanishing; label:prop:prelim-kummer-valuation; line:1017` |
| `prod_carryFun` | `L20261018.Ch2.Brauer.Step019_y_pow_eq_b` | 44 |  |
| `prod_diagonal_mem` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 346 |  |
| `prod_pointwise` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 369 |  |
| `proj` | `L20261018.Infra.Cohomology.Boundary.Step003_coinduced_quotient` | 70 |  |
| `projI` | `L20261018.Infra.Cohomology.Coinduced.Step018_iota_delta_zero_zero` | 55 |  |
| `projI_apply` | `L20261018.Infra.Cohomology.Coinduced.Step018_iota_delta_zero_zero` | 75 |  |
| `projI_comp_inclI` | `L20261018.Infra.Cohomology.Coinduced.Step018_iota_delta_zero_zero` | 95 |  |
| `projI_quotient_smul` | `L20261018.Infra.Cohomology.Coinduced.Step018_iota_delta_zero_zero` | 80 |  |
| `projLin` | `L20261018.Ch2.Hensel.ResidueMap.Step069_hcup_injectivity` | 86 |  |
| `projLin_apply` | `L20261018.Ch4.Step046_exists_residue_map` | 193 |  |
| `projLin_infl1ResToVKG_eq` | `L20261018.Ch4.Step046_exists_residue_map` | 202 |  |
| `projLin_infl1ResToVKG_ne_zero` | `L20261018.Ch4.Step046_exists_residue_map` | 241 |  |
| `projLin_injective` | `L20261018.Ch4.Step046_exists_residue_map` | 278 |  |
| `projRestr` | `L20261018.Infra.Cohomology.Coinduced.Step018_iota_delta_zero_zero` | 148 |  |
| `proj_apply` | `L20261018.Infra.Cohomology.Boundary.Step003_coinduced_quotient` | 74 |  |
| `proj_eq_zero_iff` | `L20261018.Infra.Cohomology.Boundary.Step003_coinduced_quotient` | 84 |  |
| `proj_equivariant` | `L20261018.Infra.Cohomology.Boundary.Step004_coinduced_ses_acyclic` | 71 |  |
| `proj_surjective` | `L20261018.Infra.Cohomology.Boundary.Step003_coinduced_quotient` | 77 |  |
| `proj_surjective_primeToPTateModule` | `L20261018.Ch2.Hensel.Inertia.Step019_tame_module_l_part_infinite` | 70 |  |
| `prop_3_4_first_three` | `L20261018.Core.Step001_bi_kummer_data` | 718 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `prop_3_4_galo` | `L20261018.Ch3.NormImage.Step006_hs_special_five_term` | 42 | `label:prop:hs-special` |
| `q7D` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 65 |  |
| `q7D_val` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 75 |  |
| `q7Pi` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 45 |  |
| `q7Pi_fin` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 61 |  |
| `q7Pi_hπ` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 54 |  |
| `q7Pi_irred` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 58 |  |
| `q7Pi_notpow` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 51 |  |
| `q7Pi_zval` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 48 |  |
| `qSES` | `L20261018.Infra.Cohomology.ResidueLES.Step002_t_cokernel_constructed` | 51 |  |
| `qSES_X₁` | `L20261018.Infra.Cohomology.ResidueLES.Step002_t_cokernel_constructed` | 56 |  |
| `qSES_X₂` | `L20261018.Infra.Cohomology.ResidueLES.Step002_t_cokernel_constructed` | 59 |  |
| `qSES_X₃` | `L20261018.Infra.Cohomology.ResidueLES.Step002_t_cokernel_constructed` | 63 |  |
| `qSES_g_comp_deltaZeroBar` | `L20261018.Infra.Cohomology.ResidueLES.Step004_i_star_delta_zero_bar` | 61 |  |
| `qti_smul_eq_self` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 75 |  |
| `quotientAddEquivOfEq` | `L20261018.Ch3.NormImage.Step017_three_six_quotient_transport` | 28 |  |
| `quotientConjAction` | `L20261018.Infra.Cohomology.Boundary.Step030_conj_action_descends` | 68 |  |
| `quotientConjActionH1` | `L20261018.Infra.Cohomology.Boundary.Step031_quotient_action_explicit_model` | 63 |  |
| `quotientConjAction_mk_smul` | `L20261018.Infra.Cohomology.Coinduced.Step007_delta_zero_quotient_morphism` | 56 |  |
| `quotientMk_mul_mem_eq` | `L20261018.Infra.Cohomology.ResidueLES.Step020_pull_back_map` | 44 |  |
| `quotientToInvariants_ρ_mk` | `L20261018.Infra.Cohomology.Boundary.Step018_delta_two_conditional` | 68 | `line:9498` |
| `quotient_smul_eq_self` | `L20261018.Infra.Cohomology.Conjugation.Step010_h_conj1_implies_f5` | 53 |  |
| `quotient_smul_mk` | `L20261018.Infra.Cohomology.Conjugation.Step004_gamma_scalar_action` | 78 |  |
| `quotient_smul_mk_h1` | `L20261018.Infra.Cohomology.Conjugation.Step005_gamma_complete` | 105 |  |
| `quotient_smul_muPInv_trivial` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 77 |  |
| `quotient_smul_zmod_trivial` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 83 |  |
| `ramified_vanishing` | `L20261018.Ch4.Step003_ramified_vanishing_paper_objects` | 106 | `label:lem:ramified-vanishing; label:prop:prelim-residue` |
| `ramified_vanishing_explicit` | `L20261018.Ch4.Step003_ramified_vanishing_paper_objects` | 167 | `label:lem:ramified-vanishing; label:prop:prelim-residue` |
| `ramified_vanishing_ker_tame` | `L20261018.Ch2.Hensel.ResidueMap.Step019_hens_residue_data_nine_fields` | 68 |  |
| `ramified_vanishing_kummer` | `L20261018.Ch4.Step003_ramified_vanishing_paper_objects` | 131 | `label:lem:ramified-vanishing; label:prop:prelim-residue` |
| `ramified_vanishing_paper` | `L20261018.Ch4.Step044_ch4_hypothesis_deflation_audit` | 78 |  |
| `ramified_vanishing_paper_route` | `L20261018.Ch4.Step012_ramified_vanishing_paper_route` | 201 | `line:1608` |
| `ramified_vanishing_reduced` | `L20261018.Ch2.Hensel.ResidueMap.Step005_residue_cup_data_fields_reduced` | 105 | `label:lem:ramified-vanishing` |
| `ramified_vanishing_reduced3` | `L20261018.Ch2.Hensel.ResidueMap.Step006_tame_pi_u_of` | 61 | `label:lem:ramified-vanishing` |
| `ramified_vanishing_unconditional` | `L20261018.Ch2.Hensel.ResidueMap.Step022_ramified_vanishing_no_tame_symbol` | 88 | `label:lem:ramified-vanishing` |
| `ramified_vanishing_units` | `L20261018.Ch2.Hensel.ResidueMap.Step009_tame_uu_of_units` | 36 |  |
| `ramified_vanishing_units'` | `L20261018.Ch2.Hensel.ResidueMap.Step018_huu_discharged` | 55 | `label:lem:ramified-vanishing` |
| `range_fin2` | `L20261018.Core.Step001_bi_kummer_data` | 167 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `range_infl2Canon_eq_bot_of_subsingleton` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 178 |  |
| `range_infl2Res_eq_bot_of_subsingleton` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 175 |  |
| `range_inflH2_eq_bot_of_subsingleton` | `L20261018.Ch2.Hensel.ResidueMap.Step060_h_kappa_h2_zero` | 107 |  |
| `range_kummerCor_subset_of_mk_eq` | `L20261018.Ch3.BiKummer.Step015_h_nrd_kummer_form` | 71 | `label:lem:basic-inclusions` |
| `range_kummerCor_subset_of_nrd` | `L20261018.Ch3.BiKummer.Step015_h_nrd_kummer_form` | 92 | `label:lem:basic-inclusions` |
| `range_pair_eq` | `L20261018.Ch4.Step013_basis_selection_u` | 27 | `line:1596` |
| `range_pair_eq_free` | `L20261018.Ch4.Step014_ramified_vanishing_hensel_level` | 54 | `line:1608` |
| `range_stable` | `L20261018.Infra.Cohomology.Coinduced.Step016_gs617_ses1` | 92 |  |
| `rank_range_eq` | `L20261018.Ch4.Step008_rank_contradiction_single_phi` | 109 | `line:1646` |
| `rank_range_eq_free` | `L20261018.Ch4.Step018_single_carrier_thm_ramified` | 102 | `line:1636; line:1637` |
| `ratIntShortExact` | `L20261018.Infra.Cohomology.Step005_cont_integral_dual_shift` | 129 | `label:sec:cohomology-complete-dv` |
| `ratOverZDimShift` | `L20261018.Infra.Cohomology.Step005_cont_integral_dual_shift` | 139 | `label:sec:cohomology-complete-dv` |
| `ratOverZDimShift_hom_eq_delta` | `L20261018.Infra.Cohomology.Step005_cont_integral_dual_shift` | 160 | `label:sec:cohomology-complete-dv` |
| `ratOverZDimShift_nonempty` | `L20261018.Infra.Cohomology.Step005_cont_integral_dual_shift` | 152 | `label:sec:cohomology-complete-dv` |
| `reassoc` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 281 |  |
| `redEquiv` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 135 |  |
| `redEquiv1` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 142 |  |
| `redEquiv1_map_smul` | `L20261018.Ch2.Brauer.Step031_brauer_of_h2_smul` | 78 |  |
| `redEquiv1_symm_kummerClass` | `L20261018.Ch2.Kummer.Step024_r1_sigma_residual_is_t1_bridge` | 46 |  |
| `redEquiv_cup` | `L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier` | 166 |  |
| `redEquiv_eq_smul` | `L20261018.Ch2.Kummer.Step016_zeta_independence_carrier` | 171 |  |
| `redEquiv_map_smul` | `L20261018.Ch2.Brauer.Step031_brauer_of_h2_smul` | 72 |  |
| `redLin` | `L20261018.Ch2.Brauer.Step031_brauer_of_h2_smul` | 46 |  |
| `redLin1` | `L20261018.Ch2.Brauer.Step031_brauer_of_h2_smul` | 54 |  |
| `redLin1_eq` | `L20261018.Ch2.Brauer.Step031_brauer_of_h2_smul` | 67 |  |
| `redLin_eq` | `L20261018.Ch2.Brauer.Step031_brauer_of_h2_smul` | 62 |  |
| `rel` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 80 |  |
| `repC` | `L20261018.Ch2.Hensel.TameSymbol.Step013_tame_symbol_factors_closed` | 52 |  |
| `repC_spec` | `L20261018.Ch2.Hensel.TameSymbol.Step013_tame_symbol_factors_closed` | 55 |  |
| `repr_smul_coeff` | `L20261018.Ch2.Hensel.Valuation.Step018_left_mul_matrix_entrywise` | 47 |  |
| `res1V` | `L20261018.Ch2.Hensel.Inertia.Step034_inertia_restriction_res1` | 104 |  |
| `res1V_apply` | `L20261018.Ch2.Hensel.Inertia.Step034_inertia_restriction_res1` | 110 |  |
| `res1V_eq_zero_iff_exists_unit` | `L20261018.Ch2.Hensel.Inertia.Step035_ker_v_eq_ker_res1` | 134 |  |
| `res1V_h1ToVEquiv` | `L20261018.Infra.Cohomology.Coinduced.Step036_res_h1_type_equiv_vkg` | 105 |  |
| `res1V_infl1Res_eq_zero` | `L20261018.Infra.Cohomology.Coinduced.Step036_res_h1_type_equiv_vkg` | 188 |  |
| `res1V_kummerClass_eq` | `L20261018.Ch2.Hensel.Inertia.Step034_inertia_restriction_res1` | 117 |  |
| `res1V_kummerClass_eq_zero_iff` | `L20261018.Ch2.Hensel.Inertia.Step035_ker_v_eq_ker_res1` | 118 |  |
| `res1V_kummerClass_ne_zero_of_uniformizer` | `L20261018.Ch2.Hensel.ResidueMap.Step065_partial_one_inputs` | 110 |  |
| `res1V_kummerClass_spec` | `L20261018.Ch2.Hensel.ResidueMap.Step070_partial_one_pi_generator` | 71 |  |
| `res1V_kummerClass_zmultiples_eq_top` | `L20261018.Ch2.Hensel.ResidueMap.Step070_partial_one_pi_generator` | 53 |  |
| `res1V_mem_H1ConjInvariants` | `L20261018.Ch2.Hensel.ResidueMap.Step065_partial_one_inputs` | 96 |  |
| `resMG` | `L20261018.Ch3.NormImage.Step002_five_term_mg_k2_data` | 26 |  |
| `resMG_eq_zero_iff_explicitRes1` | `L20261018.Ch3.NormImage.Step008_three_five_u_wiring` | 100 | `label:thm:hs-tate-exact-sequences` |
| `resMG_kummerExplicit_eq_zero_iff` | `L20261018.Ch3.NormImage.Step008_three_five_u_wiring` | 126 | `label:thm:hs-tate-exact-sequences` |
| `resRestrictScalarsIntMap_coeffIdHom_eq_pair` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 151 |  |
| `res_comp_infl_cup_pi` | `L20261018.Ch2.Hensel.ResidueMap.Step033_residue_sequence_exact_split` | 97 | `label:prop:prelim-residue` |
| `res_cup_eq` | `L20261018.Ch2.Hensel.TameSymbol.Step001_tame_symbol_general_formula` | 73 | `label:eq:prelim-tame` |
| `res_cup_eq_unitParts` | `L20261018.Ch2.Hensel.TameSymbol.Step002_tame_symbol_formula` | 125 | `label:eq:prelim-tame` |
| `res_cup_infl_pi` | `L20261018.Ch2.Hensel.TameSymbol.Step002_tame_symbol_formula` | 88 | `label:eq:prelim-tame` |
| `res_cup_pi_infl` | `L20261018.Ch2.Hensel.TameSymbol.Step002_tame_symbol_formula` | 92 | `label:eq:prelim-tame` |
| `res_cup_pi_pi` | `L20261018.Ch2.Hensel.TameSymbol.Step002_tame_symbol_formula` | 96 | `label:eq:prelim-tame` |
| `res_delta_zero_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step077_cont_delta_res_naturality` | 48 |  |
| `res_eq_on_paperUseSpan` | `L20261018.Ch4.Step020_delta_two_eq_res_carrier` | 54 |  |
| `res_explicitH1` | `L20261018.Infra.Galois.Step001_explicit_h1_res` | 10 |  |
| `res_explicitH1_kummerMap_eq_zero_iff` | `L20261018.Ch3.BiKummer.Step008_restriction_canonical_h1` | 28 |  |
| `res_kummerClass_eq_zero_iff` | `L20261018.Ch3.BiKummer.Step010_restriction_kernel_paper_v` | 86 |  |
| `res_restrictScalarsIntEquiv_comm` | `L20261018.Ch3.BiKummer.Step010_restriction_kernel_paper_v` | 57 |  |
| `res_surjective` | `L20261018.Ch2.Hensel.ResidueMap.Step033_residue_sequence_exact_split` | 65 | `label:prop:prelim-residue` |
| `res_tame_values` | `L20261018.Ch4.Step020_delta_two_eq_res_carrier` | 40 |  |
| `residueAct` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 169 |  |
| `residueAct_apply_residue` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 182 |  |
| `residueAct_ker` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 191 |  |
| `residueAtRoot` | `L20261018.Ch2.Hensel.Valuation.Step006_residue_map_subring` | 40 |  |
| `residueAtRoot_C` | `L20261018.Ch2.Hensel.Valuation.Step006_residue_map_subring` | 61 |  |
| `residueAtRoot_root` | `L20261018.Ch2.Hensel.Valuation.Step006_residue_map_subring` | 53 |  |
| `residueAtRoot_surjective` | `L20261018.Ch2.Hensel.Valuation.Step006_residue_map_subring` | 71 |  |
| `residueChar` | `L20261018.Ch2.Hensel.Inertia.Step017_tame_module_procyclic` | 50 | `line:8` |
| `residueCoeff` | `L20261018.Infra.Cohomology.Boundary.Step032_delta_zero_explicit_model` | 63 |  |
| `residueCoeffMatrix` | `L20261018.Ch2.Hensel.Valuation.Step022_norm_congruence` | 41 |  |
| `residueCupDataOfKer` | `L20261018.Ch2.Hensel.ResidueMap.Step005_residue_cup_data_fields_reduced` | 57 | `label:lem:ramified-vanishing` |
| `residueCupData_explicit` | `L20261018.Ch4.Step007_corollary_four_four_no_d` | 47 | `line:1646` |
| `residueCupData_explicit_cup` | `L20261018.Ch4.Step007_corollary_four_four_no_d` | 65 | `line:1646` |
| `residueCupData_explicit_of_D` | `L20261018.Ch4.Step016_corollary_four_four_sec_2_4_only` | 51 | `line:1648` |
| `residueCupData_explicit_val` | `L20261018.Ch4.Step007_corollary_four_four_no_d` | 57 | `line:1646` |
| `residueEquiv` | `L20261018.Witness.Step022_f7t_hensel_finite_residue` | 145 |  |
| `residueFieldMap` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step036_integral_closure_ring_map` | 91 |  |
| `residueFieldMap_residue` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step036_integral_closure_ring_map` | 97 |  |
| `residueMap` | `L20261018.Infra.Cohomology.Step006_rv_complex_assembly` | 88 |  |
| `residueMap_comp_eq_zero` | `L20261018.Infra.Cohomology.Step006_rv_complex_assembly` | 124 |  |
| `residueMap_exact` | `L20261018.Infra.Cohomology.Step006_rv_complex_assembly` | 101 |  |
| `residuePhi` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 71 | `line:1050; line:1608; line:1636; line:1648` |
| `residuePhi_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 78 | `line:1050; line:1608; line:1636; line:1648` |
| `residuePhi_injective_iff_kummer` | `L20261018.Ch2.Hensel.Valuation.Step002_principal_units_without_completeness` | 146 | `line:1017; line:1622` |
| `residuePhi_injective_iff_norm_of_bridge` | `L20261018.Ch2.Hensel.Valuation.Step003_r1_norm_form` | 93 |  |
| `residuePhi_injective_iff_norm_of_scaled_bridge` | `L20261018.Ch2.Hensel.ResidueMap.Step030_r1_scaled_bridge` | 79 |  |
| `residuePhi_injective_muNRep` | `L20261018.Ch4.Step029_r1_two_carriers_wired` | 111 |  |
| `residuePhi_injective_muNRep'` | `L20261018.Ch2.Hensel.ResidueMap.Step031_r1_without_bridge_or_completeness` | 116 |  |
| `residuePhi_injective_of_bridgeKc` | `L20261018.Ch2.Kummer.Step024_r1_sigma_residual_is_t1_bridge` | 79 |  |
| `residuePhi_injective_of_norm_form` | `L20261018.Ch2.Hensel.ResidueMap.Step028_residue_phi_injective` | 69 |  |
| `residuePhi_injective_of_norm_form'` | `L20261018.Ch2.Hensel.ResidueMap.Step029_model_field_from_hypothesis` | 35 | `label:prop:prelim-residue` |
| `residuePhi_injective_of_norm_form_scaled` | `L20261018.Ch2.Hensel.ResidueMap.Step030_r1_scaled_bridge` | 112 |  |
| `residuePhi_injective_of_t1` | `L20261018.Ch2.Kummer.Step033_t1_closed` | 215 |  |
| `residuePhi_injective_t1` | `L20261018.Ch2.Hensel.ResidueMap.Step031_r1_without_bridge_or_completeness` | 101 |  |
| `residuePhi_injective_transport` | `L20261018.Ch4.Step028_r1_linear_transport` | 77 |  |
| `residueRingAct` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 144 |  |
| `residueRingAct_apply_residue` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 161 |  |
| `residueSpan` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 82 | `line:1050; line:1608; line:1636; line:1648` |
| `residueSpan_Galo_eq_bot_of_muNRep` | `L20261018.Ch4.Step030_unramified_decomposition_algebraic` | 246 |  |
| `residueSpan_Galo_eq_bot_of_muNRep'` | `L20261018.Ch2.Hensel.ResidueMap.Step031_r1_without_bridge_or_completeness` | 185 |  |
| `residueSpan_eq_bot_of_dependent` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step017_one_dimensionality_is_the_engine` | 61 |  |
| `residueSpan_eq_bot_of_finrank_le_one` | `L20261018.Ch2.Hensel.ResidueMap.Step055_r2_exact_boundary` | 111 |  |
| `residueSpan_eq_bot_of_isCyclic` | `L20261018.Ch2.Hensel.ResidueMap.Step055_r2_exact_boundary` | 76 |  |
| `residueSpan_eq_bot_of_le_range` | `L20261018.Ch4.Step027_residue_span_bot_skeleton` | 51 |  |
| `residueSpan_eq_bot_of_norm` | `L20261018.Ch4.Step030_unramified_decomposition_algebraic` | 157 |  |
| `residueSpan_eq_bot_of_subsingleton_H2` | `L20261018.Ch2.Hensel.ResidueMap.Step060_h_kappa_h2_zero` | 166 |  |
| `residueSpan_eq_bot_of_subsingleton_H2_residue` | `L20261018.Ch4.Step038_ch4_proof_structure_index` | 74 |  |
| `residueSpan_eq_bot_of_subsingleton_H2canon` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 238 |  |
| `residueSpan_eq_bot_of_tsen` | `L20261018.Ch2.Rost.Step002_tsen_cd_p_le_one` | 176 |  |
| `residueSpan_eq_bot_of_units` | `L20261018.Ch4.Step030_unramified_decomposition_algebraic` | 115 |  |
| `residueSpan_le_ker_of_units` | `L20261018.Infra.Cohomology.ResidueLES.Step015_vkg_kummer_decomposition` | 78 |  |
| `residueSpan_le_ker_res` | `L20261018.Ch2.Hensel.ResidueMap.Step042_residue_span_subset_ker_res` | 73 |  |
| `residueSpan_le_range_infl2Canon` | `L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier` | 201 |  |
| `residueSpan_le_range_infl2Res` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 187 |  |
| `residueSpan_le_range_infl2Res_of_kummer` | `L20261018.Ch2.Hensel.Inertia.Step033_unramified_kummer_hyp` | 74 |  |
| `residueSpan_le_range_inflH2` | `L20261018.Ch2.Hensel.ResidueMap.Step060_h_kappa_h2_zero` | 131 |  |
| `residueSpan_ne_top_of_exists_phi_ne_zero` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step018_b_logical_tension` | 87 |  |
| `residueUnits` | `L20261018.Ch2.Hensel.ResidueMap.Step056_kummer_valuation_abstract_hensel` | 71 | `label:prop:prelim-kummer-valuation` |
| `residueUnitsEquiv` | `L20261018.Ch2.Hensel.ResidueMap.Step039_residue_classes_linear_dependent` | 33 |  |
| `residueUnits_injective_on_pow_eq_one` | `L20261018.Ch2.Hensel.ResidueMap.Step059_mu_p_into_residue_units` | 116 |  |
| `residue_action_welldef` | `L20261018.Ch2.Hensel.Inertia.Step031_residue_action_well_defined` | 55 |  |
| `residue_dependent` | `L20261018.Ch2.Hensel.ResidueMap.Step039_residue_classes_linear_dependent` | 53 |  |
| `residue_det_coeffMatrix` | `L20261018.Ch2.Hensel.Valuation.Step022_norm_congruence` | 56 |  |
| `residue_exists_mul_pow_inv_mem_range` | `L20261018.Ch2.Hensel.ResidueMap.Step015_huu_residue_field_power_relation` | 30 |  |
| `residue_mem_pow_range_iff` | `L20261018.Ch2.Hensel.ResidueMap.Step056_kummer_valuation_abstract_hensel` | 111 | `label:prop:prelim-kummer-valuation` |
| `residue_not_pow_of_kummerClass_ne_zero` | `L20261018.Ch4.Step011_transition_paragraph_4_1_4_2` | 144 | `line:1596; line:1599` |
| `residue_pow_of_pow` | `L20261018.Ch2.Hensel.ResidueMap.Step043_units_mod_pth_powers_paper_level` | 108 | `label:prop:prelim-kummer-valuation; line:992` |
| `residue_uniformizer_image_eq_zero` | `L20261018.Ch2.Hensel.Valuation.Step022_norm_congruence` | 45 |  |
| `residue_units_eq_one_iff` | `L20261018.Ch2.Hensel.ResidueMap.Step056_kummer_valuation_abstract_hensel` | 75 | `label:prop:prelim-kummer-valuation` |
| `resolutionMap_zero_eq` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 68 |  |
| `restrictEquiv_comp_symm` | `L20261018.Ch2.Kummer.Step030_t1_bridge_gm_bypass` | 55 |  |
| `restrictScalarsH1` | `L20261018.Ch2.Hensel.ResidueMap.Step051_h1_z_equiv_galo_v` | 114 | `line:1050` |
| `restrictScalarsIntEquiv_map` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 97 |  |
| `restrictScalarsInt_available` | `L20261018.Ch2.Kummer.Step045_kummer_coeff_zmod_instance` | 50 |  |
| `restrictScalarsInt_muP` | `L20261018.Infra.Cohomology.ResidueLES.Step008_base_ring_alignment` | 63 |  |
| `restrictScalars_muPQuot_eq` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 123 |  |
| `restrictScalars_muP_eq` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 128 |  |
| `restrictTameInertia` | `L20261018.Ch2.Hensel.Inertia.Step024_hom_inertia_tame` | 102 |  |
| `restrictTameInertia_bijective` | `L20261018.Ch2.Hensel.Inertia.Step024_hom_inertia_tame` | 192 |  |
| `restrictTameInertia_injective` | `L20261018.Ch2.Hensel.Inertia.Step024_hom_inertia_tame` | 108 |  |
| `restrictTameInertia_surjective` | `L20261018.Ch2.Hensel.Inertia.Step024_hom_inertia_tame` | 118 |  |
| `restrict_delta_zero_comp_projCoeff` | `L20261018.Infra.Cohomology.Coinduced.Step018_iota_delta_zero_zero` | 135 |  |
| `restrictedCoindAcyclic_bot` | `L20261018.Infra.Cohomology.ResidueLES.Step033_restricted_coind_acyclic_nonempty` | 46 |  |
| `rho` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step012_units_cup_vanish_unconditional` | 34 |  |
| `rho` | `L20261018.Witness.Step024_f7t_not_cube` | 57 |  |
| `rho_twoO` | `L20261018.Witness.Step024_f7t_not_cube` | 67 |  |
| `rootUnit` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step041_res_inertia_kummer_class_zero` | 77 |  |
| `rootUnit_coe` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step041_res_inertia_kummer_class_zero` | 83 |  |
| `rootUnit_pow_eq` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step041_res_inertia_kummer_class_zero` | 87 |  |
| `root_mul_eq_zero_iff` | `L20261018.Ch2.Hensel.Valuation.Step028_reindex_eliminate_s` | 60 |  |
| `root_mul_left_cancel` | `L20261018.Ch2.Hensel.Valuation.Step028_reindex_eliminate_s` | 82 |  |
| `root_ne_zero_of_ne_zero` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step003_norm_group_adjoin_root` | 69 |  |
| `root_pow_eq` | `L20261018.Ch2.Hensel.Valuation.Step014_reduced_power_formula` | 39 |  |
| `root_pow_eq_of` | `L20261018.Ch2.Hensel.Valuation.Step010_power_basis_s` | 31 |  |
| `root_pow_eq_of_lt` | `L20261018.Ch2.Hensel.Valuation.Step014_reduced_power_formula` | 47 |  |
| `root_pow_eq_zero_adjoinRoot` | `L20261018.Infra.Algebra.Step001_norm_monoid_hom` | 63 |  |
| `root_pow_mul` | `L20261018.Ch2.Hensel.Valuation.Step010_power_basis_s` | 51 |  |
| `rootsOfUnityModule` | `L20261018.Ch2.Kummer.Step042_mu_p_module_structure` | 68 |  |
| `rootsOfUnityResidue_injective` | `L20261018.Ch2.Hensel.ResidueMap.Step059_mu_p_into_residue_units` | 156 |  |
| `rootsOfUnity_isIntegral` | `L20261018.Ch2.Hensel.Inertia.Step011_kummer_coeff_to_knr` | 48 | `line:8152; line:8160` |
| `rootsOfUnity_nsmul_eq_zero` | `L20261018.Ch2.Kummer.Step042_mu_p_module_structure` | 58 |  |
| `s_mul_hpart` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step020_tg_definition` | 80 |  |
| `scaled_bridge_of_bridgeKc` | `L20261018.Ch2.Kummer.Step024_r1_sigma_residual_is_t1_bridge` | 54 |  |
| `scaled_bridge_uncond` | `L20261018.Ch2.Hensel.ResidueMap.Step031_r1_without_bridge_or_completeness` | 45 |  |
| `sesCoind1` | `L20261018.Infra.Cohomology.Coinduced.Step016_gs617_ses1` | 103 |  |
| `seven_irred_Q7` | `L20261018.Witness.Step015_q7_hk1` | 70 |  |
| `seven_mem_maximalIdeal` | `L20261018.Witness.Step007_l1_witness_q7` | 57 |  |
| `seven_not_cube_Q7` | `L20261018.Witness.Step015_q7_hk1` | 42 |  |
| `shiftedHom` | `L20261018.Ch2.Hensel.Inertia.Step026_hom_inertia_mu_p_eq_zmod` | 105 |  |
| `shiftedHom_apply_zeta` | `L20261018.Ch2.Hensel.Inertia.Step026_hom_inertia_mu_p_eq_zmod` | 145 |  |
| `sigma` | `L20261018.Witness.Step031_f7t_finite_cube_classes` | 49 |  |
| `sigma_surjective` | `L20261018.Witness.Step031_f7t_finite_cube_classes` | 60 |  |
| `smulHom` | `L20261018.Ch2.Kummer.Step037_kc_scalar_transfer` | 32 |  |
| `smulPairingB` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 116 |  |
| `smulPairingB_equivariant` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 142 |  |
| `smulPairingC` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 98 |  |
| `smulPairingC_apply` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 112 |  |
| `smulPairingC_equivariant` | `L20261018.Infra.Cohomology.Coinduced.Step037_h0_leibniz_parts` | 135 |  |
| `smulPairingH1` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 91 |  |
| `smulPairingH1_apply` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 115 |  |
| `smulPairingH1_continuous` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 120 |  |
| `smulPairingH1_quotient_smul` | `L20261018.Ch2.Hensel.ResidueMap.Step075_cont_m_cup` | 127 |  |
| `smul_bL` | `L20261018.Ch2.Brauer.Step013_carry_cocycle_index` | 38 |  |
| `smul_mk` | `L20261018.Infra.Cohomology.Boundary.Step004_coinduced_ses_acyclic` | 49 |  |
| `smul_pow_bL` | `L20261018.Ch2.Brauer.Step014_carry_cocycle_two_cocycle` | 41 |  |
| `span_monomials_eq_top` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 351 |  |
| `stdBiKummer` | `L20261018.Core.Step001_bi_kummer_data` | 542 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `stdCup` | `L20261018.Core.Step001_bi_kummer_data` | 534 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `steinbergGen` | `L20261018.Ch2.Hensel.TameSymbol.Step015_tame_symbol_hyp_from_merkurjev_suslin` | 122 |  |
| `subOne` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 197 | `line:739` |
| `subOne_coe` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 206 | `line:739` |
| `sub_one_mem_maximalIdeal_of_residue_eq_one` | `L20261018.Ch2.Hensel.Valuation.Step002_principal_units_without_completeness` | 69 | `line:1017; line:1622` |
| `subgroupMap_conjNormal` | `L20261018.Infra.Cohomology.Conjugation.Step012_h_conj1_entry` | 101 |  |
| `submodule_sup_toAddSubgroup` | `L20261018.Ch3.NormImage.Step015_three_six_assembly_u_alignment` | 28 |  |
| `subringAct` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 87 |  |
| `subringAct_apply_symm` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 116 |  |
| `subringAct_coe` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 95 |  |
| `subringAct_comp_self` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 100 |  |
| `subringAct_isLocalHom` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 139 |  |
| `subringAct_isLocalMap` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 131 |  |
| `subringAct_mul` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 122 |  |
| `subringAct_self_comp` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 105 |  |
| `subringAct_symm_apply` | `L20261018.Ch2.Hensel.Inertia.Step032_residue_action_kernel` | 110 |  |
| `subsingleton_H1_contC` | `L20261018.Infra.Cohomology.ResidueLES.Step031_inf_c_inverse_hypothesis` | 37 |  |
| `subsingleton_H1_contC_inertia` | `L20261018.Infra.Cohomology.ResidueLES.Step032_inf_c_inverse_narrowed` | 67 |  |
| `subsingleton_H1_discreteCoind_bot_self` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 215 |  |
| `subsingleton_H1_int_absGal` | `L20261018.Infra.Cohomology.Step003_q_first_acyclicity` | 54 |  |
| `subsingleton_H1_of_continuousCohomology` | `L20261018.Infra.Cohomology.Coinduced.Step006_inf_h1_iso_closed_subgroup` | 85 |  |
| `subsingleton_H1_quot_subgroup` | `L20261018.Infra.Cohomology.Coinduced.Step003_coind_subgroup_acyclic_one` | 76 |  |
| `subsingleton_H1_quot_subgroup_of_isClosed` | `L20261018.Infra.Cohomology.Coinduced.Step005_closed_subgroup_acyclicity` | 88 |  |
| `subsingleton_H1_rat_disc_absGal` | `L20261018.Infra.Cohomology.Step004_q_discrete_h1_acyclic` | 52 |  |
| `subsingleton_H2` | `L20261018.Ch2.Hensel.Inertia.Step013_inertia_pro_p_sylow_data` | 115 | `line:9625; line:9627` |
| `subsingleton_H2_complex` | `L20261018.Witness.Step039_tsen_hyp_nonempty` | 95 |  |
| `subsingleton_H2_of_TsenHyp` | `L20261018.Ch2.Rost.Step002_tsen_cd_p_le_one` | 141 |  |
| `subsingleton_H2_of_cohomologicalDimensionLE` | `L20261018.Ch2.Rost.Step002_tsen_cd_p_le_one` | 130 |  |
| `subsingleton_H2_of_isSepClosed` | `L20261018.Witness.Step039_tsen_hyp_nonempty` | 90 |  |
| `subsingleton_H2_of_procyclic` | `L20261018.Ch2.Hensel.Inertia.Step015_cd_p_procyclic_criterion` | 81 | `line:8` |
| `subsingleton_H2_padicInt` | `L20261018.Ch2.Rost.Step001_cd_p_z_p_le_one` | 123 | `label:prop-cd-Z-hat; line:9625; line:9627` |
| `subsingleton_H2_padicInt_of_module_zmod` | `L20261018.Ch2.Rost.Step001_cd_p_z_p_le_one` | 139 | `label:prop-cd-Z-hat; line:9625; line:9627` |
| `subsingleton_H2_padicInt_zmod_p_witness` | `L20261018.Ch2.Rost.Step001_cd_p_z_p_le_one` | 162 | `label:prop-cd-Z-hat; line:9625; line:9627` |
| `subsingleton_H_quot_coindBot_invariants` | `L20261018.Infra.Cohomology.Coinduced.Step014_coinduced_invariants` | 90 |  |
| `subsingleton_Hq` | `L20261018.Ch2.Hensel.Inertia.Step013_inertia_pro_p_sylow_data` | 107 | `line:9625; line:9627` |
| `subsingleton_algEquiv_bot` | `L20261018.Ch2.Brauer.Step004_degenerate_crossed_product_trivial` | 73 |  |
| `subsingleton_cohomology_quot` | `L20261018.Infra.Cohomology.Boundary.Step004_coinduced_ses_acyclic` | 86 |  |
| `subsingleton_cohomology_quot_subgroup` | `L20261018.Infra.Cohomology.Coinduced.Step001_coind_subgroup_acyclic_hyp` | 110 |  |
| `subsingleton_cohomology_three_of_acyclic` | `L20261018.Infra.Cohomology.Boundary.Step001_acyclicity_short_exact` | 45 |  |
| `subsingleton_cohomology_three_of_coind` | `L20261018.Infra.Cohomology.Boundary.Step001_acyclicity_short_exact` | 76 |  |
| `subsingleton_contInvB` | `L20261018.Infra.Cohomology.ResidueLES.Step024_top_rep_iso_coind` | 107 |  |
| `subsingleton_continuousCohomology_ofDiscreteModule_iff` | `L20261018.Ch2.Rost.Step002_tsen_cd_p_le_one` | 32 |  |
| `subsingleton_continuousCohomology_one_coindBot` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 228 |  |
| `subsingleton_continuousCohomology_padicInt_of_two_le` | `L20261018.Ch2.Rost.Step001_cd_p_z_p_le_one` | 114 | `label:prop-cd-Z-hat; line:9625; line:9627` |
| `subsingleton_continuousCohomology_rat_disc` | `L20261018.Infra.Cohomology.Step005_cont_integral_dual_shift` | 115 | `label:sec:cohomology-complete-dv` |
| `subsingleton_continuousCohomology_rat_disc_of_pos` | `L20261018.Infra.Cohomology.Step005_cont_integral_dual_shift` | 121 | `label:sec:cohomology-complete-dv` |
| `subsingleton_continuousCoindBot` | `L20261018.Infra.Cohomology.ResidueLES.Step017_delta_t_iso_upper` | 86 |  |
| `subsingleton_of_exact_delta` | `L20261018.Infra.Cohomology.Boundary.Step033_subgroup_acyclicity_gap` | 67 |  |
| `subsingleton_of_exact_delta'` | `L20261018.Infra.Cohomology.Boundary.Step033_subgroup_acyclicity_gap` | 81 |  |
| `subsingleton_of_knrResidueReduced` | `L20261018.Ch2.Hensel.ResidueMap.Step054_delta_two_candidate_refuted` | 189 |  |
| `subsingleton_of_topRep_iso` | `L20261018.Infra.Cohomology.ResidueLES.Step017_delta_t_iso_upper` | 34 |  |
| `subsingleton_resH2Type_top` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 252 |  |
| `subtypeCompCoeffInclH1` | `L20261018.Ch4.Step046_exists_residue_map` | 109 |  |
| `subtype_comp_coeffSubAddHom` | `L20261018.Infra.Cohomology.Coinduced.Step031_coefficient_bridge_explicit_model` | 49 |  |
| `sumCoeff` | `L20261018.Ch2.Hensel.Valuation.Step018_left_mul_matrix_entrywise` | 27 |  |
| `sumCoeffShift` | `L20261018.Ch2.Hensel.Valuation.Step018_left_mul_matrix_entrywise` | 32 |  |
| `sumCoeff_eq_root_mul` | `L20261018.Ch2.Hensel.Valuation.Step028_reindex_eliminate_s` | 100 |  |
| `sumCoeff_mul_basis` | `L20261018.Ch2.Hensel.Valuation.Step018_left_mul_matrix_entrywise` | 37 |  |
| `sum_div_range` | `L20261018.Ch2.Brauer.Step018_product_cocycle_sum` | 33 |  |
| `sum_range_eq_sumCoeff` | `L20261018.Ch2.Hensel.Valuation.Step024_normalization_sum_coeff` | 29 |  |
| `sum_range_split` | `L20261018.Ch2.Hensel.Valuation.Step027_leading_term_split` | 36 |  |
| `sum_range_split_adjoinRoot` | `L20261018.Ch2.Hensel.Valuation.Step027_leading_term_split` | 56 |  |
| `sum_range_split_last` | `L20261018.Ch2.Hensel.Valuation.Step028_reindex_eliminate_s` | 44 |  |
| `sup_U_Uperp_eq_top` | `L20261018.Core.Step001_bi_kummer_data` | 180 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `symbolAlg` | `L20261018.Ch3.BiKummer.Step014_splitting_field` | 68 |  |
| `symbolAlg_brauerClass_eq` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 289 |  |
| `symbolAlg_brauerClass_eq_verbatim` | `L20261018.Ch2.Kummer.Step012_symbol_cup` | 76 | `label:cor:symbol-cup` |
| `symbolAlg_of_isPow` | `L20261018.Ch3.BiKummer.Step014_splitting_field` | 73 |  |
| `symm_gen'_pow` | `L20261018.Ch2.Brauer.Step027_adjoin_root_to_intermediate_field` | 149 |  |
| `symm_twoO` | `L20261018.Witness.Step024_f7t_not_cube` | 61 |  |
| `sσ` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step020_tg_definition` | 69 |  |
| `t1_closed` | `L20261018.Ch2.Kummer.Step033_t1_closed` | 202 |  |
| `t1_closed'` | `L20261018.Ch2.Kummer.Step039_t1_without_completeness` | 225 |  |
| `t1_closed_of_hζ` | `L20261018.Ch2.Kummer.Step033_t1_closed` | 103 |  |
| `t1_closed_of_hζ'` | `L20261018.Ch2.Kummer.Step039_t1_without_completeness` | 128 |  |
| `t1_of_thetaTwo` | `L20261018.Ch2.Kummer.Step027_t1_mu_n_rep_factorization` | 248 |  |
| `tameChainCond` | `L20261018.Ch2.Hensel.TameSymbol.Step010_tame_symbol_two_chain_criterion` | 48 |  |
| `tameChainCond_of_tameSumCond` | `L20261018.Ch2.Hensel.TameSymbol.Step011_tame_sum_condition` | 63 |  |
| `tameChainCond_of_tameSymbolFactors` | `L20261018.Ch2.Hensel.TameSymbol.Step010_tame_symbol_two_chain_criterion` | 52 |  |
| `tameCharLoc` | `L20261018.Ch2.Hensel.Inertia.Step040_tame_character_galois_invariant` | 188 |  |
| `tameCharLoc_apply` | `L20261018.Ch2.Hensel.Inertia.Step040_tame_character_galois_invariant` | 195 |  |
| `tameCharLoc_conj` | `L20261018.Ch2.Hensel.Inertia.Step040_tame_character_galois_invariant` | 212 |  |
| `tameCharLoc_ne_one` | `L20261018.Ch2.Hensel.Inertia.Step040_tame_character_galois_invariant` | 200 |  |
| `tameExpr` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 91 | `label:eq:prelim-tame; line:1050` |
| `tameExpr_add_left` | `L20261018.Ch2.Hensel.TameSymbol.Step008_tame_symbol_bilinear` | 65 | `label:eq:prelim-tame` |
| `tameExpr_add_right` | `L20261018.Ch2.Hensel.TameSymbol.Step008_tame_symbol_bilinear` | 59 | `label:eq:prelim-tame` |
| `tameExpr_coe` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 94 | `label:eq:prelim-tame; line:1050` |
| `tameExpr_collinear` | `L20261018.Ch2.Hensel.TameSymbol.Step008_tame_symbol_bilinear` | 83 | `label:eq:prelim-tame` |
| `tameExpr_congr_of_tameSymbolFactors` | `L20261018.Ch2.Hensel.TameSymbol.Step009_tame_symbol_factors_descent` | 48 |  |
| `tameExpr_eq_zero_iff` | `L20261018.Ch2.Hensel.TameSymbol.Step008_tame_symbol_bilinear` | 49 | `label:eq:prelim-tame` |
| `tameExpr_eq_zero_of_tameSymbolFactors` | `L20261018.Ch2.Hensel.TameSymbol.Step008_tame_symbol_bilinear` | 88 | `label:eq:prelim-tame` |
| `tameExpr_kummerClass_oneSub` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 293 | `line:739` |
| `tameExpr_kummerClass_oneSub_coe` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 375 | `line:739` |
| `tameExpr_kummerClass_subOne` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 387 | `line:739` |
| `tameExpr_of_res` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 133 | `label:eq:prelim-tame; line:1050` |
| `tameExpr_pi_pi` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 116 | `label:eq:prelim-tame; line:1050` |
| `tameExpr_pi_u` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 110 | `label:eq:prelim-tame; line:1050` |
| `tameExpr_skew` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 121 | `label:eq:prelim-tame; line:1050` |
| `tameExpr_smul_left` | `L20261018.Ch2.Hensel.TameSymbol.Step008_tame_symbol_bilinear` | 77 | `label:eq:prelim-tame` |
| `tameExpr_smul_right` | `L20261018.Ch2.Hensel.TameSymbol.Step008_tame_symbol_bilinear` | 71 | `label:eq:prelim-tame` |
| `tameExpr_sum_eq_zero_of_tameSymbolFactors` | `L20261018.Ch2.Hensel.TameSymbol.Step009_tame_symbol_factors_descent` | 55 |  |
| `tameExpr_u_pi` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 104 | `label:eq:prelim-tame; line:1050` |
| `tameExpr_uu` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 98 | `label:eq:prelim-tame; line:1050` |
| `tameExpr_zero_left` | `L20261018.Ch2.Hensel.TameSymbol.Step009_tame_symbol_factors_descent` | 70 |  |
| `tameExpr_zero_right` | `L20261018.Ch2.Hensel.TameSymbol.Step009_tame_symbol_factors_descent` | 66 |  |
| `tameImage` | `L20261018.Infra.Cohomology.ResidueLES.Step002_t_cokernel_constructed` | 81 |  |
| `tameInertia_compactSpace` | `L20261018.Ch2.Hensel.Inertia.Step021_inertia_sylow_z_l` | 100 |  |
| `tameKernelCond` | `L20261018.Ch2.Hensel.TameSymbol.Step012_tame_symbol_finsupp` | 66 |  |
| `tameKernelCond_iff_ker_le` | `L20261018.Ch2.Hensel.TameSymbol.Step012_tame_symbol_finsupp` | 70 |  |
| `tameKernelCond_of_merkurjevSuslin` | `L20261018.Ch2.Hensel.TameSymbol.Step015_tame_symbol_hyp_from_merkurjev_suslin` | 224 |  |
| `tameLC` | `L20261018.Ch2.Hensel.TameSymbol.Step012_tame_symbol_finsupp` | 61 |  |
| `tameLC_bilinGen_eq_zero` | `L20261018.Ch2.Hensel.TameSymbol.Step015_tame_symbol_hyp_from_merkurjev_suslin` | 186 |  |
| `tameLC_eq_zero_of_mem_span` | `L20261018.Ch2.Hensel.TameSymbol.Step015_tame_symbol_hyp_from_merkurjev_suslin` | 205 |  |
| `tameLC_steinbergGen_eq_zero` | `L20261018.Ch2.Hensel.TameSymbol.Step015_tame_symbol_hyp_from_merkurjev_suslin` | 160 |  |
| `tameModelEquivTameInertia` | `L20261018.Ch2.Hensel.Inertia.Step021_inertia_sylow_z_l` | 104 |  |
| `tamePChar` | `L20261018.Ch2.Hensel.Inertia.Step040_tame_character_galois_invariant` | 104 |  |
| `tamePCharHom` | `L20261018.Ch2.Hensel.Inertia.Step040_tame_character_galois_invariant` | 89 |  |
| `tamePChar_conj` | `L20261018.Ch2.Hensel.Inertia.Step040_tame_character_galois_invariant` | 148 |  |
| `tamePChar_ne_one` | `L20261018.Ch2.Hensel.Inertia.Step040_tame_character_galois_invariant` | 114 |  |
| `tamePointwise_of_tameChainCond` | `L20261018.Ch2.Hensel.TameSymbol.Step010_tame_symbol_two_chain_criterion` | 63 |  |
| `tameResidueFacts_Galo_noBridge` | `L20261018.Ch4.Step033_ch4_three_and_exists_d` | 71 | `line:1050; line:1608; line:1636; line:1648` |
| `tameResidueFacts_Galo_noBridge_of_hζ` | `L20261018.Ch4.Step033_ch4_three_and_exists_d` | 57 | `line:1050; line:1608; line:1636; line:1648` |
| `tameResidueFacts_Galo_of_finrank_ker_le_one` | `L20261018.Ch2.Hensel.ResidueMap.Step055_r2_exact_boundary` | 142 |  |
| `tameResidueFacts_Galo_of_residueMap` | `L20261018.Ch2.Hensel.ResidueMap.Step036_residue_cup_product_interface` | 59 | `label:lemma-residue-cup-product; line:1608; line:1636; line:1648` |
| `tameResidueFacts_Galo_of_residueSpan_eq_bot` | `L20261018.Ch4.Step038_ch4_proof_structure_index` | 88 |  |
| `tameResidueFacts_Galo_of_span_eq_bot` | `L20261018.Ch4.Step029_r1_two_carriers_wired` | 158 |  |
| `tameResidueFacts_Galo_of_unitsCupVanish` | `L20261018.Ch2.Hensel.ResidueMap.Step041_residue_map_single_hypothesis` | 85 | `line:1023` |
| `tameResidueFacts_Galo_of_units_cup` | `L20261018.Ch4.Step030_unramified_decomposition_algebraic` | 279 |  |
| `tameResidueFacts_of_complete` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 277 | `line:1050; line:1608; line:1636; line:1648` |
| `tameResidueFacts_of_data` | `L20261018.Ch2.Hensel.ResidueMap.Step042_residue_span_subset_ker_res` | 103 |  |
| `tameResidueFacts_of_disjoint` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step015_b_reduced_to_disjoint` | 87 |  |
| `tameResidueFacts_of_hd_cup_pi` | `L20261018.Ch2.Hensel.ResidueMap.Step064_delta_two_definition` | 100 |  |
| `tameResidueFacts_of_henselResidueData` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 177 | `line:1050; line:1608; line:1636; line:1648` |
| `tameResidueFacts_of_isCyclic` | `L20261018.Ch2.Hensel.ResidueMap.Step055_r2_exact_boundary` | 103 |  |
| `tameResidueFacts_of_le_range` | `L20261018.Ch4.Step027_residue_span_bot_skeleton` | 66 |  |
| `tameResidueFacts_of_merkurjevSuslin` | `L20261018.Ch4.Step039_ch4_four_without_finite_residue` | 81 | `line:1050; line:1608; line:1636; line:1648` |
| `tameResidueFacts_of_norm_form` | `L20261018.Ch2.Hensel.ResidueMap.Step028_residue_phi_injective` | 90 |  |
| `tameResidueFacts_of_norm_form'` | `L20261018.Ch2.Hensel.ResidueMap.Step029_model_field_from_hypothesis` | 50 | `label:prop:prelim-residue` |
| `tameResidueFacts_of_residueMap` | `L20261018.Ch2.Hensel.ResidueMap.Step034_delta_two_replaces_finite_residue` | 51 |  |
| `tameResidueFacts_of_residueSpan_eq_bot` | `L20261018.Ch2.Hensel.ResidueMap.Step055_r2_exact_boundary` | 96 |  |
| `tameResidueFacts_of_scaled_bridge` | `L20261018.Ch2.Hensel.ResidueMap.Step030_r1_scaled_bridge` | 134 |  |
| `tameResidueFacts_of_span_eq_bot` | `L20261018.Ch4.Step026_residue_span_bot_reduction` | 65 |  |
| `tameResidueFacts_of_tameSymbolFactors` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 165 | `label:eq:prelim-tame; line:1050` |
| `tameResidueFacts_of_units_cup` | `L20261018.Ch4.Step030_unramified_decomposition_algebraic` | 191 |  |
| `tameResidueFacts_uncond` | `L20261018.Ch4.Step046_exists_residue_map` | 409 |  |
| `tameResidueFacts_witness_Q7` | `L20261018.Witness.Step008_tame_residue_facts_q7` | 158 | `label:prop:prelim-residue` |
| `tameSumCond` | `L20261018.Ch2.Hensel.TameSymbol.Step011_tame_sum_condition` | 46 |  |
| `tameSumCond_of_tameSymbolFactors` | `L20261018.Ch2.Hensel.TameSymbol.Step011_tame_sum_condition` | 51 |  |
| `tameSymbolFactors_iff` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 230 | `label:eq:prelim-tame; line:1050` |
| `tameSymbolFactors_of_merkurjevSuslin` | `L20261018.Ch2.Hensel.TameSymbol.Step015_tame_symbol_hyp_from_merkurjev_suslin` | 236 |  |
| `tameSymbolFactors_of_tameKernelCond` | `L20261018.Ch2.Hensel.TameSymbol.Step013_tame_symbol_factors_closed` | 60 |  |
| `tameSymbolFactors_of_tameResidueFacts` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 190 | `label:eq:prelim-tame; line:1050` |
| `tame_pi_u` | `L20261018.Witness.Step008_tame_residue_facts_q7` | 97 | `label:prop:prelim-residue` |
| `tame_pi_u_of` | `L20261018.Ch2.Hensel.ResidueMap.Step006_tame_pi_u_of` | 15 | `label:lem:ramified-vanishing` |
| `tame_pi_u_of_general` | `L20261018.Ch2.Hensel.TameSymbol.Step002_tame_symbol_formula` | 156 | `label:eq:prelim-tame` |
| `tame_pi_u_redundant` | `L20261018.Ch4.Step023_tame_residue_facts_reduction` | 49 |  |
| `tame_u_pi_of_general` | `L20261018.Ch2.Hensel.TameSymbol.Step002_tame_symbol_formula` | 148 | `label:eq:prelim-tame` |
| `tame_uu_of_general` | `L20261018.Ch2.Hensel.TameSymbol.Step002_tame_symbol_formula` | 139 | `label:eq:prelim-tame` |
| `tame_uu_of_units` | `L20261018.Ch2.Hensel.ResidueMap.Step009_tame_uu_of_units` | 15 |  |
| `tensor` | `L20261018.Ch3.BiKummer.Step014_splitting_field` | 53 |  |
| `tensorSymbolAlg` | `L20261018.Ch3.BiKummer.Step014_splitting_field` | 83 |  |
| `tensorSymbolAlg_of_isPow` | `L20261018.Ch3.BiKummer.Step014_splitting_field` | 91 |  |
| `tgCocycle` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step026_partial_y_descent` | 74 |  |
| `tgCocycle_add` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step027_tg_additive_component` | 83 |  |
| `tgCocycle_cocycle` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step028_tg_cochain_internal_check` | 75 |  |
| `tgCocycle_eq_zero_of_cocycle` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step029_first_segment_exactness` | 43 |  |
| `tgCocycle_sec_indep` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step028_tg_cochain_internal_check` | 49 |  |
| `tgCocycle_sub_eq` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step030_tg_well_defined_complete` | 76 |  |
| `tgDescend` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step029_first_segment_exactness` | 77 |  |
| `tgLift` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step020_tg_definition` | 87 |  |
| `tgLift_apply_h_mul_section` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step021_tg_compatibility` | 113 |  |
| `tgLift_apply_hpart` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step020_tg_definition` | 104 |  |
| `tgLift_apply_section` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step021_tg_compatibility` | 93 |  |
| `tgLift_hii_add` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step027_tg_additive_component` | 65 |  |
| `tgLift_hiii_add` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step027_tg_additive_component` | 74 |  |
| `tgLift_hleft_sub` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step029_first_segment_exactness` | 69 |  |
| `tgLift_hright_sub` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step029_first_segment_exactness` | 61 |  |
| `tgLift_mul_left` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step021_tg_compatibility` | 137 |  |
| `tgLift_mul_right` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step020_tg_definition` | 119 |  |
| `tgLift_z_mem_fixed` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step025_descent_lemma_well_defined` | 70 |  |
| `tgLift_z_quot_eq` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step030_tg_well_defined_complete` | 44 |  |
| `tgLift_z_right_invariant` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step025_descent_lemma_well_defined` | 54 |  |
| `tgMap` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step031_tg_normal_form` | 72 |  |
| `tgMap_cocycle` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step031_tg_normal_form` | 77 |  |
| `tgMap_sec_indep` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step031_tg_normal_form` | 84 |  |
| `tgSectionOf` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step032_tg_section_exists` | 38 |  |
| `tgSection_nonempty` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step032_tg_section_exists` | 53 |  |
| `tgYs` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step031_tg_normal_form` | 50 |  |
| `tgYs_hii` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step031_tg_normal_form` | 62 |  |
| `tgYs_hiii` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step031_tg_normal_form` | 67 |  |
| `tgYs_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step031_tg_normal_form` | 54 |  |
| `tgYs_restrict` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step031_tg_normal_form` | 58 |  |
| `theorem_3_2_1` | `L20261018.Core.Step001_bi_kummer_data` | 251 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `theorem_3_2_1_kummer'` | `L20261018.Ch3.BiKummer.Step017_rank_barrier_unconditional` | 17 | `label:thm:rank-barrier` |
| `theorem_3_2_1_kummer'` | `L20261018.Ch3.BiKummer.Step017_rank_barrier_unconditional` | 48 | `label:thm:rank-barrier` |
| `theorem_3_2_2` | `L20261018.Core.Step001_bi_kummer_data` | 260 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `theorem_3_2_2_kummer'` | `L20261018.Ch3.BiKummer.Step017_rank_barrier_unconditional` | 65 | `label:thm:rank-barrier` |
| `theorem_3_2_reduction` | `L20261018.Core.Step001_bi_kummer_data` | 225 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `theorem_3_5_1` | `L20261018.Core.Step001_bi_kummer_data` | 411 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `theorem_3_5_1_explicit` | `L20261018.Ch3.NormImage.Step008_three_five_u_wiring` | 249 | `label:thm:hs-tate-exact-sequences` |
| `theorem_3_5_1_galo` | `L20261018.Ch3.NormImage.Step005_three_five_one_first_ses` | 70 | `label:thm:hs-tate-exact-sequences` |
| `theorem_3_5_2` | `L20261018.Core.Step001_bi_kummer_data` | 327 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `theorem_3_5_2_explicit` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 190 | `label:thm:hs-tate-exact-sequences` |
| `theorem_3_6` | `L20261018.Core.Step001_bi_kummer_data` | 557 | `label:thm:dimension; label:thm:hs-tate-exact-sequences` |
| `theorem_3_6_explicit` | `L20261018.Ch3.NormImage.Step022_dimension_paper_objects` | 19 | `label:thm:dimension` |
| `theta1` | `L20261018.Ch4.Step006_thm_ramified_no_d` | 54 | `label:thm:ramified` |
| `theta1_apply` | `L20261018.Ch4.Step006_thm_ramified_no_d` | 64 | `label:thm:ramified` |
| `theta1_free` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 49 | `line:1636; line:1648` |
| `theta1_free_apply` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 59 | `line:1636; line:1648` |
| `theta1_free_kummerClass` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 67 | `line:1636; line:1648` |
| `theta1_kummerClass` | `L20261018.Ch4.Step006_thm_ramified_no_d` | 147 | `label:thm:ramified` |
| `theta1_kummerClass_F` | `L20261018.Ch2.Kummer.Step041_theta_bridge_true_hypothesis` | 97 |  |
| `theta1_kummerClass_lc` | `L20261018.Ch2.Kummer.Step041_theta_bridge_true_hypothesis` | 71 |  |
| `theta1g` | `L20261018.Ch2.Kummer.Step040_theta_bridge_without_local_field` | 39 |  |
| `theta1g_apply` | `L20261018.Ch2.Kummer.Step040_theta_bridge_without_local_field` | 49 |  |
| `theta2` | `L20261018.Ch4.Step006_thm_ramified_no_d` | 59 | `label:thm:ramified` |
| `theta2_apply` | `L20261018.Ch4.Step006_thm_ramified_no_d` | 67 | `label:thm:ramified` |
| `theta2_free` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 54 | `line:1636; line:1648` |
| `theta2_free_apply` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 62 | `line:1636; line:1648` |
| `theta2g` | `L20261018.Ch2.Kummer.Step040_theta_bridge_without_local_field` | 44 |  |
| `theta2g_apply` | `L20261018.Ch2.Kummer.Step040_theta_bridge_without_local_field` | 52 |  |
| `thetaTwo` | `L20261018.Ch2.Kummer.Step027_t1_mu_n_rep_factorization` | 217 |  |
| `thm_ramified_1` | `L20261018.Ch4.Step004_thm_ramified_assembly` | 50 | `label:thm:ramified` |
| `thm_ramified_1_F` | `L20261018.Witness.Step036_f7t_thm_ramified_witness_paper_objects` | 103 | `line:1636` |
| `thm_ramified_1_general` | `L20261018.Ch4.Step036_ch4_three_without_finite_residue` | 76 |  |
| `thm_ramified_1_noBridge` | `L20261018.Ch4.Step033_ch4_three_and_exists_d` | 118 | `line:1050; line:1608; line:1636; line:1648` |
| `thm_ramified_1_noFinite` | `L20261018.Ch2.Hensel.ResidueMap.Step036_residue_cup_product_interface` | 99 | `label:lemma-residue-cup-product; line:1608; line:1636; line:1648` |
| `thm_ramified_1_of_D` | `L20261018.Ch4.Step015_thm_ramified_1_sec_2_4_only` | 99 | `line:1636` |
| `thm_ramified_1_of_D_free` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 135 | `line:1636; line:1648` |
| `thm_ramified_1_of_D_free_nofin` | `L20261018.Ch4.Step037_ch4_without_finite_dimensional_v` | 172 | `line:1636` |
| `thm_ramified_1_of_cyclicUnits` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 242 |  |
| `thm_ramified_1_of_discrete_valuation` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 203 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `thm_ramified_1_of_discrete_valuation'` | `L20261018.Ch4.Step031_ch4_closed_units_cup_vanish` | 75 | `line:1608; line:1636; line:1648` |
| `thm_ramified_1_of_discrete_valuation''` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step013_exists_d_and_ch4_unconditional` | 78 |  |
| `thm_ramified_1_of_discrete_valuation_nofin` | `L20261018.Ch4.Step037_ch4_without_finite_dimensional_v` | 242 | `line:1636` |
| `thm_ramified_1_of_disjoint` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step015_b_reduced_to_disjoint` | 123 |  |
| `thm_ramified_1_of_merkurjevSuslin` | `L20261018.Ch4.Step039_ch4_four_without_finite_residue` | 115 | `line:1050; line:1608; line:1636; line:1648` |
| `thm_ramified_1_of_residue_facts` | `L20261018.Ch2.Hensel.ResidueMap.Step024_delta_two_refined` | 345 | `line:1050; line:1608; line:1636; line:1648` |
| `thm_ramified_1_paper` | `L20261018.Ch4.Step037_ch4_without_finite_dimensional_v` | 302 | `line:1636` |
| `thm_ramified_1_uncond` | `L20261018.Ch4.Step006_thm_ramified_no_d` | 183 | `label:thm:ramified` |
| `thm_ramified_1_viaResidue` | `L20261018.Ch4.Step047_ch4_three_d_free` | 119 | `line:1608; line:1636; line:1648` |
| `thm_ramified_2` | `L20261018.Ch4.Step004_thm_ramified_assembly` | 89 | `label:thm:ramified` |
| `thm_ramified_2_explicit` | `L20261018.Ch4.Step018_single_carrier_thm_ramified` | 118 | `line:1636; line:1637` |
| `thm_ramified_2_paper` | `L20261018.Ch4.Step041_thm_ramified_two_rank_barrier` | 49 | `line:1635` |
| `thm_ramified_combined` | `L20261018.Ch4.Step018_single_carrier_thm_ramified` | 134 | `line:1636; line:1637` |
| `three_five_one_Bex` | `L20261018.Ch3.NormImage.Step020_three_six_first_ses_paper_u` | 32 |  |
| `three_five_one_add` | `L20261018.Ch3.NormImage.Step004_three_five_one_abelian` | 33 |  |
| `three_isUnit_F` | `L20261018.Witness.Step007_l1_witness_q7` | 129 |  |
| `three_isUnit_O` | `L20261018.Witness.Step007_l1_witness_q7` | 126 |  |
| `three_isUnit_O` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 133 |  |
| `three_isUnit_laurentSeries` | `L20261018.Witness.Step021_f7t_mu3_transport` | 52 |  |
| `three_ne_zero_laurentSeries` | `L20261018.Witness.Step021_f7t_mu3_transport` | 45 |  |
| `toAdd_eq_one_iff` | `L20261018.Ch2.Hensel.ResidueMap.Step008_exists_unit_rep` | 13 | `label:prop:prelim-kummer-valuation` |
| `toAdd_eq_zero_of_pow_eq_one` | `L20261018.Ch2.Hensel.ResidueMap.Step062_mu_p_residue_full_chain` | 56 |  |
| `toAdd_inv'` | `L20261018.Ch2.Hensel.ResidueMap.Step007_valuation_to_add_tools` | 10 |  |
| `toAdd_mul'` | `L20261018.Ch2.Hensel.ResidueMap.Step003_residue_valuation_h1` | 43 | `label:prop:prelim-kummer-valuation` |
| `toAdd_one'` | `L20261018.Ch2.Hensel.ResidueMap.Step008_exists_unit_rep` | 10 | `label:prop:prelim-kummer-valuation` |
| `toAdd_pow` | `L20261018.Witness.Step003_nondegenerate_nonzero_cup` | 75 |  |
| `toAdd_pow'` | `L20261018.Ch2.Hensel.ResidueMap.Step003_residue_valuation_h1` | 46 | `label:prop:prelim-kummer-valuation` |
| `toAdd_pow_int` | `L20261018.Ch4.Step021_d_elementary_block` | 47 |  |
| `toAdd_vCompatHom` | `L20261018.Ch2.Hensel.Valuation.Step033_val_compat_exists` | 37 |  |
| `toAdd_val_eq_zero_of_isUnit` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 166 | `line:739` |
| `toAdd_val_mul_pow` | `L20261018.Ch2.Hensel.ResidueMap.Step008_exists_unit_rep` | 23 | `label:prop:prelim-kummer-valuation` |
| `toAdd_val_mul_pow_inv` | `L20261018.Ch2.Hensel.ResidueMap.Step007_valuation_to_add_tools` | 22 |  |
| `toAdd_val_neg_one` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 122 | `line:739` |
| `toAdd_val_nonneg_of_mem_integer` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 178 | `line:739` |
| `toAdd_val_oneSub` | `L20261018.Ch2.Hensel.TameSymbol.Step014_tame_steinberg_relation` | 216 | `line:739` |
| `toAdd_val_pi_pow` | `L20261018.Ch2.Hensel.ResidueMap.Step007_valuation_to_add_tools` | 14 |  |
| `toAdd_val_zpow'` | `L20261018.Ch2.Hensel.ResidueMap.Step026_unit_norm_pth_power_from_valuation` | 57 |  |
| `toAdd_zpow'` | `L20261018.Ch2.Hensel.ResidueMap.Step026_unit_norm_pth_power_from_valuation` | 44 |  |
| `toFun` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 104 |  |
| `toFunFun` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 92 |  |
| `toFun_invFun` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 166 |  |
| `toFun_smul` | `L20261018.Infra.Cohomology.Coinduced.Step004_finite_index_coset_decomposition` | 188 |  |
| `toHenselResidueData` | `L20261018.Witness.Step008_tame_residue_facts_q7` | 113 | `label:prop:prelim-residue` |
| `toLinearMap` | `L20261018.Ch3.NormImage.Step014_three_six_assembly_linearize` | 32 |  |
| `toLinearMapOfAddEquiv` | `L20261018.Ch3.NormImage.Step021_three_six_first_ses_submodule` | 33 |  |
| `toLinearMapOfAddEquiv_injective` | `L20261018.Ch3.NormImage.Step021_three_six_first_ses_submodule` | 51 |  |
| `toLinearMapOfAddEquiv_surjective` | `L20261018.Ch3.NormImage.Step021_three_six_first_ses_submodule` | 44 |  |
| `toLinearMap_apply` | `L20261018.Ch3.NormImage.Step014_three_six_assembly_linearize` | 39 |  |
| `toLinearMap_injective` | `L20261018.Ch3.NormImage.Step014_three_six_assembly_linearize` | 45 |  |
| `toLinearMap_surjective` | `L20261018.Ch3.NormImage.Step014_three_six_assembly_linearize` | 51 |  |
| `toMatrix_mulRight_inc` | `L20261018.Ch2.Brauer.Step002_reduced_norm_maximal_subfield` | 56 |  |
| `toResidueCupData` | `L20261018.Ch4.Step003_ramified_vanishing_paper_objects` | 89 | `label:lem:ramified-vanishing; label:prop:prelim-residue` |
| `toTameInertia` | `L20261018.Ch2.Hensel.Inertia.Step020_inertia_sylow_mod_ramification` | 77 |  |
| `toTameInertia_subgroupMap_injective` | `L20261018.Ch2.Hensel.Inertia.Step021_inertia_sylow_z_l` | 142 |  |
| `toTameInertia_surjective` | `L20261018.Ch2.Hensel.Inertia.Step020_inertia_sylow_mod_ramification` | 88 |  |
| `toValuationSubring` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step036_integral_closure_ring_map` | 64 |  |
| `toValuationSubring_coe` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step036_integral_closure_ring_map` | 72 |  |
| `toyBiKummer` | `L20261018.Witness.Step001_bi_kummer_data_nonempty` | 42 |  |
| `toyCross` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 251 | `label:eq:prelim-tame; line:1050` |
| `toyCross_pi` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 284 | `label:eq:prelim-tame; line:1050` |
| `toyCross_skew` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 280 | `label:eq:prelim-tame; line:1050` |
| `toyCup` | `L20261018.Witness.Step001_bi_kummer_data_nonempty` | 31 |  |
| `toyHenselResidueData` | `L20261018.Ch2.Hensel.ResidueMap.Step001_open_residual_advance` | 75 | `line:1017` |
| `toyHenselResidueData_nonempty` | `L20261018.Ch2.Hensel.ResidueMap.Step001_open_residual_advance` | 110 | `line:1017` |
| `toyHensel_toResidueCupData` | `L20261018.Ch2.Hensel.ResidueMap.Step001_open_residual_advance` | 116 | `line:1017` |
| `toyPi` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 272 | `label:eq:prelim-tame; line:1050` |
| `toyRes` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 292 | `label:eq:prelim-tame; line:1050` |
| `toyResFun` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 289 | `label:eq:prelim-tame; line:1050` |
| `toyResidueCupData` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 220 | `label:lem:ramified-vanishing` |
| `toyVal` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 274 | `label:eq:prelim-tame; line:1050` |
| `toyVal_toyPi` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 277 | `label:eq:prelim-tame; line:1050` |
| `toy_hypotheses` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 265 | `label:lem:ramified-vanishing` |
| `toy_residueSpan_ne_bot` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 316 | `label:eq:prelim-tame; line:1050` |
| `toy_tameSymbolFactors` | `L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit` | 303 | `label:eq:prelim-tame; line:1050` |
| `toy_vanishing` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 278 | `label:lem:ramified-vanishing` |
| `transport_apply` | `L20261018.Infra.Cohomology.Conjugation.Step012_h_conj1_entry` | 79 |  |
| `triple` | `L20261018.Ch2.Kummer.Step003_triple_cup_product` | 58 |  |
| `triple_cyclic` | `L20261018.Ch2.Kummer.Step003_triple_cup_product` | 90 |  |
| `triple_eq_cupH` | `L20261018.Ch2.Kummer.Step003_triple_cup_product` | 67 |  |
| `triple_swap12` | `L20261018.Ch2.Kummer.Step003_triple_cup_product` | 76 |  |
| `triple_swap23` | `L20261018.Ch2.Kummer.Step003_triple_cup_product` | 83 |  |
| `trivialBotAction` | `L20261018.Infra.Cohomology.Step007_additive_hilbert90` | 74 | `label:lemma-additive-hilbert90` |
| `trivialPairing` | `L20261018.Ch2.Hensel.ResidueMap.Step057_residue_span_inflation` | 105 |  |
| `tsenHyp_of_isSepClosed` | `L20261018.Witness.Step039_tsen_hyp_nonempty` | 81 |  |
| `tsenHyp_of_subsingleton_galois` | `L20261018.Witness.Step039_tsen_hyp_nonempty` | 73 |  |
| `twoO` | `L20261018.Witness.Step024_f7t_not_cube` | 51 |  |
| `twoUnit` | `L20261018.Witness.Step012_q7_exists_nonzero_cup` | 51 |  |
| `twoUnitF` | `L20261018.Witness.Step025_f7t_hne_hval` | 60 | `line:1608` |
| `two_isUnit_O` | `L20261018.Witness.Step010_q7_nonzero_cup` | 65 |  |
| `two_isUnit_O` | `L20261018.Witness.Step025_f7t_hne_hval` | 73 | `line:1608` |
| `two_mem_O` | `L20261018.Witness.Step024_f7t_not_cube` | 45 |  |
| `two_ne_one_zmod7` | `L20261018.Witness.Step019_f7_two_order_three` | 20 |  |
| `two_ne_zero_laurentSeries` | `L20261018.Witness.Step025_f7t_hne_hval` | 51 | `line:1608` |
| `two_pow_three_zmod7` | `L20261018.Witness.Step019_f7_two_order_three` | 17 |  |
| `two_sq_ne_one_zmod7` | `L20261018.Witness.Step019_f7_two_order_three` | 23 |  |
| `u_ne_zero` | `L20261018.Ch2.Hensel.Inertia.Step026_hom_inertia_mu_p_eq_zmod` | 156 |  |
| `uliftZModCoeffIso` | `L20261018.Ch2.Hensel.ResidueMap.Step051_h1_z_equiv_galo_v` | 102 | `line:1050` |
| `uniformizer_mem_integer` | `L20261018.Ch2.Hensel.Valuation.Step011_uniformizer_clear_denominators` | 31 |  |
| `uniformizer_mem_maximalIdeal` | `L20261018.Ch2.Hensel.Valuation.Step005_eisenstein_uniformizer` | 54 |  |
| `uniformizer_notMem_maximalIdeal_sq` | `L20261018.Ch2.Hensel.Valuation.Step005_eisenstein_uniformizer` | 62 |  |
| `uniformizer_pow_mul_mem_integer_mono` | `L20261018.Ch2.Hensel.Valuation.Step011_uniformizer_clear_denominators` | 40 |  |
| `unique_decomp_linear` | `L20261018.Ch2.Hensel.ResidueMap.Step004_valuation_decomposition_unique` | 56 | `label:prop:prelim-kummer-valuation` |
| `unitBase` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step041_res_inertia_kummer_class_zero` | 73 |  |
| `unitBase_coe` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step041_res_inertia_kummer_class_zero` | 80 |  |
| `unitPow_iff_residuePow` | `L20261018.Ch2.Hensel.ResidueMap.Step002_unit_reduction_principal_units` | 64 | `label:lem:ramified-vanishing; label:prop:prelim-kummer-valuation; line:1017` |
| `unitQuotPowEquiv` | `L20261018.Ch2.Hensel.ResidueMap.Step056_kummer_valuation_abstract_hensel` | 144 | `label:prop:prelim-kummer-valuation` |
| `unitQuotPowEquiv_ofF` | `L20261018.Ch2.Hensel.ResidueMap.Step056_kummer_valuation_abstract_hensel` | 202 | `label:prop:prelim-kummer-valuation` |
| `unitRoot` | `L20261018.Ch2.Kummer.Step016_zeta_independence_carrier` | 83 |  |
| `unitRoot_isPrimitiveRoot` | `L20261018.Ch2.Kummer.Step016_zeta_independence_carrier` | 87 |  |
| `unitValOf` | `L20261018.Ch2.Hensel.Valuation.Step038_valuation_extension_bridge` | 55 |  |
| `unitValOf_apply` | `L20261018.Ch2.Hensel.Valuation.Step038_valuation_extension_bridge` | 61 |  |
| `unitValOf_eq_one_iff` | `L20261018.Ch2.Hensel.Valuation.Step038_valuation_extension_bridge` | 68 |  |
| `unitVal_root_eq_one` | `L20261018.Ch2.Hensel.Valuation.Step037_nu_pth_root_zero` | 80 |  |
| `unit_mem_pow_range_of_residue_mem_ofF` | `L20261018.Ch2.Hensel.ResidueMap.Step056_kummer_valuation_abstract_hensel` | 216 | `label:prop:prelim-kummer-valuation` |
| `unit_pow_dependence` | `L20261018.Ch2.Hensel.ResidueMap.Step016_huu_unit_power_dependence` | 34 |  |
| `unit_pow_iff_residue_pow_of_hensel` | `L20261018.Ch2.Hensel.ResidueMap.Step043_units_mod_pth_powers_paper_level` | 137 | `label:prop:prelim-kummer-valuation; line:992` |
| `unit_pow_of_residue_pow` | `L20261018.Ch2.Hensel.ResidueMap.Step002_unit_reduction_principal_units` | 76 | `label:lem:ramified-vanishing; label:prop:prelim-kummer-valuation; line:1017` |
| `unit_pow_of_residue_pow_of_hensel` | `L20261018.Ch2.Hensel.Valuation.Step002_principal_units_without_completeness` | 80 | `line:1017; line:1622` |
| `unit_pow_range_iff_residue_pow_range_ofF` | `L20261018.Ch2.Hensel.ResidueMap.Step056_kummer_valuation_abstract_hensel` | 209 | `label:prop:prelim-kummer-valuation` |
| `unitsCoe` | `L20261018.Ch2.Hensel.Inertia.Step037_unramified_kummer_paper_level` | 62 |  |
| `unitsCoe_apply` | `L20261018.Ch2.Hensel.Inertia.Step037_unramified_kummer_paper_level` | 66 |  |
| `unitsCupVanish` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step012_units_cup_vanish_unconditional` | 121 |  |
| `unitsCupVanish_complete` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step001_units_cup_vanish_complete` | 74 |  |
| `unitsCupVanish_of_cyclicUnits` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 161 |  |
| `unitsCupVanish_of_divisible` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 195 |  |
| `unitsCupVanish_of_finite` | `L20261018.Ch2.Hensel.ResidueMap.Step041_residue_map_single_hypothesis` | 140 | `line:1023` |
| `unitsCupVanish_of_finite'` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step014_units_cup_vanish_true_statement` | 204 |  |
| `unitsCupVanish_of_powClassGen` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step005_units_cup_vanish_final_form` | 99 |  |
| `unitsCupVanish_of_residueSpan_eq_bot` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step001_units_cup_vanish_complete` | 100 |  |
| `unitsCupVanish_of_subsingleton` | `L20261018.Ch4.Step030_unramified_decomposition_algebraic` | 177 |  |
| `unitsResidue` | `L20261018.Witness.Step027_f7t_unit_cube_from_residue` | 46 |  |
| `unitsResidue_surjective` | `L20261018.Witness.Step028_f7t_same_cube_class` | 44 |  |
| `unitsToF` | `L20261018.Witness.Step027_f7t_unit_cube_from_residue` | 41 |  |
| `unramifiedKummer` | `L20261018.Ch2.Hensel.Inertia.Step037_unramified_kummer_paper_level` | 202 |  |
| `unramifiedKummer_of_inertia` | `L20261018.Ch2.Hensel.Inertia.Step036_unramified_kummer_theorem` | 296 |  |
| `unramifiedKummer_of_subsingleton` | `L20261018.Ch2.Hensel.Inertia.Step033_unramified_kummer_hyp` | 62 |  |
| `upCLM` | `L20261018.Ch2.Kummer.Step010_cup_fp_eq_galo_cup` | 50 |  |
| `up_intertwining` | `L20261018.Ch2.Kummer.Step010_cup_fp_eq_galo_cup` | 63 |  |
| `vCompatHom` | `L20261018.Ch2.Hensel.Valuation.Step032_val_compat_multiplicative` | 97 |  |
| `valAddHom` | `L20261018.Ch2.Hensel.ResidueMap.Step003_residue_valuation_h1` | 89 | `label:prop:prelim-kummer-valuation` |
| `valAddHomOf` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 89 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `valCompat_O` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 126 |  |
| `valCompat_exists_pow_mul_mem_integer` | `L20261018.Ch2.Hensel.Valuation.Step021_val_compat_elementwise` | 64 |  |
| `valCompat_mem_integer_of_localField` | `L20261018.Witness.Step006_val_compat_complete_field` | 35 |  |
| `valCompat_mem_maximalIdeal_of_localField` | `L20261018.Witness.Step006_val_compat_complete_field` | 40 |  |
| `valCompat_normalizedValuation` | `L20261018.Witness.Step038_val_compat_nonempty` | 67 |  |
| `valCompat_normalizedValuation_Q7` | `L20261018.Witness.Step014_q7_val_compat` | 38 |  |
| `valCompat_of_dvr` | `L20261018.Ch2.Hensel.Valuation.Step033_val_compat_exists` | 92 |  |
| `valCompat_of_localField` | `L20261018.Witness.Step006_val_compat_complete_field` | 67 |  |
| `valCompat_pow_mul_mem_integer_mono` | `L20261018.Ch2.Hensel.Valuation.Step021_val_compat_elementwise` | 92 |  |
| `valCompat_uniformizer_mem_integer` | `L20261018.Ch2.Hensel.Valuation.Step021_val_compat_elementwise` | 51 |  |
| `valCompat_uniformizer_mem_maximalIdeal` | `L20261018.Ch2.Hensel.Valuation.Step021_val_compat_elementwise` | 56 |  |
| `valCompat_witness_padic` | `L20261018.Witness.Step038_val_compat_nonempty` | 105 |  |
| `valFiltrationCompat_false` | `L20261018.Witness.Step004_val_filtration_compat_empty` | 35 |  |
| `valH1Gen` | `L20261018.Ch4.Step021_d_elementary_block` | 106 |  |
| `valH1Gen_kummerClass` | `L20261018.Ch4.Step021_d_elementary_block` | 111 |  |
| `valH1Gen_kummerClass_pi` | `L20261018.Ch4.Step021_d_elementary_block` | 128 |  |
| `valH1LinearGen` | `L20261018.Ch4.Step022_d_residue_field` | 85 |  |
| `valH1LinearGen_redEquiv1` | `L20261018.Ch4.Step029_r1_two_carriers_wired` | 89 |  |
| `valH1LinearGen_redEquiv1_smul` | `L20261018.Ch2.Hensel.ResidueMap.Step031_r1_without_bridge_or_completeness` | 60 |  |
| `valLin` | `L20261018.Ch2.Hensel.ResidueMap.Step003_residue_valuation_h1` | 118 | `label:prop:prelim-kummer-valuation` |
| `valLinOf` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 120 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `valLinOf_eq_zero_iff` | `L20261018.Ch2.Hensel.ResidueMap.Step031_r1_without_bridge_or_completeness` | 74 |  |
| `valLinOf_eq_zero_iff_exists_unit` | `L20261018.Ch2.Hensel.Inertia.Step035_ker_v_eq_ker_res1` | 179 |  |
| `valLinOf_eq_zero_iff_exists_unit_of_valCompat` | `L20261018.Ch2.Hensel.Inertia.Step037_unramified_kummer_paper_level` | 144 |  |
| `valLinOf_eq_zero_iff_res1V_eq_zero` | `L20261018.Ch2.Hensel.Inertia.Step035_ker_v_eq_ker_res1` | 228 |  |
| `valLinOf_eq_zero_iff_res1V_eq_zero_of_valCompat` | `L20261018.Ch2.Hensel.Inertia.Step037_unramified_kummer_paper_level` | 190 |  |
| `valLinOf_explicitInfl1_coeffInclH1` | `L20261018.Ch4.Step046_exists_residue_map` | 181 |  |
| `valLinOf_kummerClass` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 126 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `valLinOf_pi` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 137 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `valLin_eq_valLinOf_normalizedValuation` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 155 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `valLin_kummerClass` | `L20261018.Ch2.Hensel.ResidueMap.Step003_residue_valuation_h1` | 124 | `label:prop:prelim-kummer-valuation` |
| `valLin_pi` | `L20261018.Ch2.Hensel.ResidueMap.Step003_residue_valuation_h1` | 133 | `label:prop:prelim-kummer-valuation` |
| `valMonoidGen` | `L20261018.Ch4.Step021_d_elementary_block` | 58 |  |
| `valMonoidGen_ker` | `L20261018.Ch4.Step021_d_elementary_block` | 75 |  |
| `valOfUnit` | `L20261018.Ch2.Hensel.ResidueMap.Step003_residue_valuation_h1` | 40 | `label:prop:prelim-kummer-valuation` |
| `valOfUnitOf` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 55 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `valOfUnitOf_eq_of_kummerClass_eq` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 68 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `valOfUnitOf_eq_zero_of_val_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step019_b_tension_resolved` | 55 |  |
| `valOfUnitOf_mul` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 58 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `valOfUnitOf_one` | `L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness` | 64 | `label:prop:prelim-kummer-valuation; line:1608; line:1636; line:1648` |
| `valOfUnit_eq_of_kummerClass_eq` | `L20261018.Ch2.Hensel.ResidueMap.Step003_residue_valuation_h1` | 62 | `label:prop:prelim-kummer-valuation` |
| `valOfUnit_mul` | `L20261018.Ch2.Hensel.ResidueMap.Step003_residue_valuation_h1` | 53 | `label:prop:prelim-kummer-valuation` |
| `valOfUnit_one` | `L20261018.Ch2.Hensel.ResidueMap.Step003_residue_valuation_h1` | 58 | `label:prop:prelim-kummer-valuation` |
| `valQuotGen` | `L20261018.Ch4.Step021_d_elementary_block` | 88 |  |
| `valQuotGenAdd` | `L20261018.Ch4.Step021_d_elementary_block` | 93 |  |
| `valSubring_stable` | `L20261018.Ch2.Hensel.Valuation.Step040_integral_closure_value_preserving` | 63 |  |
| `val_algMap_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step034_n4_paper_form` | 107 |  |
| `val_eq_of_decomp` | `L20261018.Ch2.Hensel.ResidueMap.Step004_valuation_decomposition_unique` | 103 | `label:prop:prelim-kummer-valuation` |
| `val_eq_of_decomp_linear` | `L20261018.Ch2.Hensel.ResidueMap.Step004_valuation_decomposition_unique` | 50 | `label:prop:prelim-kummer-valuation` |
| `val_eq_of_split` | `L20261018.Ch2.Hensel.TameSymbol.Step002_tame_symbol_formula` | 67 | `label:eq:prelim-tame` |
| `val_eq_of_split'` | `L20261018.Ch2.Hensel.TameSymbol.Step002_tame_symbol_formula` | 72 | `label:eq:prelim-tame` |
| `val_eq_one_of_inv_mem` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step034_n4_paper_form` | 66 |  |
| `val_eq_one_of_mem_unitFiltration_zero` | `L20261018.Ch2.Hensel.Inertia.Step037_unramified_kummer_paper_level` | 83 |  |
| `val_kc_pi` | `L20261018.Witness.Step033_f7t_mun_rep_cup_nonzero` | 53 |  |
| `val_mul_uniformizer_zpow` | `L20261018.Ch4.Step022_d_residue_field` | 55 |  |
| `val_root_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step033_inertia_fixed_unit_pth_root` | 157 |  |
| `val_surjective` | `L20261018.Ch4.Step005_corollary_four_four_dimension` | 39 | `line:1646` |
| `vanishing` | `L20261018.Ch4.Step002_residue_cup_data_shape` | 159 | `label:lem:ramified-vanishing` |
| `vanishing_of_ker` | `L20261018.Ch2.Hensel.ResidueMap.Step005_residue_cup_data_fields_reduced` | 81 | `label:lem:ramified-vanishing` |
| `vanishing_of_ker3` | `L20261018.Ch2.Hensel.ResidueMap.Step006_tame_pi_u_of` | 33 | `label:lem:ramified-vanishing` |
| `wildInertia_le_ker_zmodDual` | `L20261018.Ch2.Hensel.Inertia.Step024_hom_inertia_tame` | 58 |  |
| `witness_decomp_eq_top` | `L20261018.Ch2.Hensel.Inertia.Step003_knr_galois_quotient` | 194 | `label:sec:cohomology-complete-dv` |
| `witness_hypotheses` | `L20261018.Ch2.Hensel.Inertia.Step003_knr_galois_quotient` | 202 | `label:sec:cohomology-complete-dv` |
| `witness_isClosed` | `L20261018.Ch2.Hensel.Inertia.Step003_knr_galois_quotient` | 178 | `label:sec:cohomology-complete-dv` |
| `witness_nonempty` | `L20261018.Infra.Cohomology.Conjugation.Step008_conj1_trivial_hyp` | 88 |  |
| `witness_normal` | `L20261018.Ch2.Hensel.Inertia.Step003_knr_galois_quotient` | 188 | `label:sec:cohomology-complete-dv` |
| `x` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 93 |  |
| `xF` | `L20261018.Witness.Step025_f7t_hne_hval` | 113 | `line:1608` |
| `xF_ne_zero` | `L20261018.Witness.Step025_f7t_hne_hval` | 118 | `line:1608` |
| `xQ7` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 82 |  |
| `xQ7_ne_zero` | `L20261018.Witness.Step013_q7_ramified_vanishing_witness` | 85 |  |
| `x_one_eq_zero` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step021_tg_compatibility` | 56 |  |
| `x_pow` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 103 |  |
| `x_pow_eq_smul` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 219 |  |
| `xval` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 278 |  |
| `xval_injective` | `L20261018.Ch2.Brauer.Step006_symbol_algebra_degenerate` | 293 |  |
| `y` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 97 |  |
| `y_mul_x` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 127 |  |
| `y_mul_x_pow` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 176 |  |
| `y_mul_x_smul` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 171 |  |
| `y_pow` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 115 |  |
| `y_pow_eq_smul` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 226 |  |
| `y_pow_mul_x_pow` | `L20261018.Ch2.Brauer.Step005_symbol_algebra_normal_form` | 194 |  |
| `zeta3` | `L20261018.Witness.Step007_l1_witness_q7` | 133 |  |
| `zeta3_spec` | `L20261018.Witness.Step007_l1_witness_q7` | 135 |  |
| `zetaF` | `L20261018.Witness.Step025_f7t_hne_hval` | 44 | `line:1608` |
| `zetaF_spec` | `L20261018.Witness.Step025_f7t_hne_hval` | 47 | `line:1608` |
| `zetaUnit` | `L20261018.Ch2.Kummer.Step042_mu_p_module_structure` | 103 |  |
| `zmod7_cube_dependent_closed` | `L20261018.Ch2.Hensel.ResidueMap.Step039_residue_classes_linear_dependent` | 46 |  |
| `zmodEquivMuP` | `L20261018.Ch2.Hensel.Inertia.Step040_tame_character_galois_invariant` | 84 |  |
| `zmodEquivRootsOfUnity_eq_comp` | `L20261018.Ch2.Kummer.Step015_primitive_root_scalar` | 51 |  |
| `zmodEquivRootsOfUnity_eq_comp_natCast` | `L20261018.Ch2.Kummer.Step015_primitive_root_scalar` | 42 |  |
| `zmodEquivRootsOfUnity_symm_eq_smul` | `L20261018.Ch2.Kummer.Step015_primitive_root_scalar` | 63 |  |
| `zmodLinearEquivOfCardPrime` | `L20261018.Ch2.Hensel.Inertia.Step039_h1_inertia_zmod` | 57 |  |
| `zmodMulPairing` | `L20261018.Ch3.BiKummer.Step012_basic_inclusions_cor_subset` | 42 | `label:lem:basic-inclusions` |
| `zmodMulPairing_eq_muPairing` | `L20261018.Ch2.Kummer.Step022_pairing_compatibility` | 32 |  |
| `zmodMulPairing_eq_muPairing_free` | `L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free` | 33 | `line:1636; line:1648` |
| `zmodMulPairing_flip` | `L20261018.Ch3.NormImage.Step007_three_five_two_real_objects` | 118 | `label:thm:hs-tate-exact-sequences` |
| `zmod_smul_eq_val_nsmul` | `L20261018.Ch2.Kummer.Step033_t1_closed` | 54 |  |
| `zmod_smul_eq_val_nsmul'` | `L20261018.Ch2.Kummer.Step039_t1_without_completeness` | 82 |  |
| `zmod_smul_val` | `L20261018.Ch2.Kummer.Step042_mu_p_module_structure` | 72 |  |
| `zmultiples_eq_top_of_natCard_prime` | `L20261018.Infra.Cohomology.Conjugation.Step007_conj_trivial_unconditional` | 56 |  |
| `znat` | `L20261018.Ch2.Hensel.Valuation.Step030_val_compat_order_function` | 38 |  |
| `znat_eq_zero_of_isUnit` | `L20261018.Witness.Step010_q7_nonzero_cup` | 35 |  |
| `znat_le_iff_dvd` | `L20261018.Ch2.Hensel.Valuation.Step030_val_compat_order_function` | 65 |  |
| `znat_mul` | `L20261018.Ch2.Hensel.Valuation.Step030_val_compat_order_function` | 53 |  |
| `znat_one` | `L20261018.Ch2.Hensel.Valuation.Step030_val_compat_order_function` | 44 |  |
| `znat_sub_eq_of_mul_eq` | `L20261018.Ch2.Hensel.Valuation.Step031_val_compat_well_defined` | 50 |  |
| `znat_zero` | `L20261018.Ch2.Hensel.Valuation.Step030_val_compat_order_function` | 41 |  |
| `zpowers_eq_top_of_pow_eq_one` | `L20261018.Ch2.Hensel.UnitsCupVanish.Step009_units_group_lemma` | 50 |  |
| `zsie_symm_cup_eq` | `L20261018.Ch2.Hensel.ResidueMap.Step081_explicit_cup01` | 99 |  |
| `zsie_symm_explicitH2OfDiscrete` | `L20261018.Ch2.Hensel.ResidueMap.Step081_explicit_cup01` | 83 |  |
| `zval` | `L20261018.Ch2.Hensel.Valuation.Step032_val_compat_multiplicative` | 59 |  |
| `zval_eq_znat` | `L20261018.Ch2.Hensel.Valuation.Step033_val_compat_exists` | 41 |  |
| `zval_inv` | `L20261018.Witness.Step029_f7t_zval_powers` | 42 |  |
| `zval_mul` | `L20261018.Ch2.Hensel.Valuation.Step032_val_compat_multiplicative` | 73 |  |
| `zval_one` | `L20261018.Ch2.Hensel.Valuation.Step032_val_compat_multiplicative` | 68 |  |
| `zval_pi` | `L20261018.Witness.Step023_f7t_dvr_val_compat` | 114 |  |
| `zval_pi_pow` | `L20261018.Witness.Step029_f7t_zval_powers` | 32 |  |
| `zval_pi_zpow` | `L20261018.Witness.Step029_f7t_zval_powers` | 49 |  |
| `zval_pow` | `L20261018.Ch2.Hensel.Valuation.Step034_discharge_pi_hypotheses` | 37 |  |
| `zval_pow` | `L20261018.Ch2.Hensel.Valuation.Step036_exists_unit_rep_val_lin` | 45 |  |
| `zval_spec` | `L20261018.Ch2.Hensel.Valuation.Step032_val_compat_multiplicative` | 63 |  |
| `zval_twoUnitF` | `L20261018.Ch2.Hensel.ResidueMap.Step040_ker_v_finrank_le_one` | 42 | `line:1648` |
| `zval_uniformizer` | `L20261018.Ch2.Hensel.Valuation.Step034_discharge_pi_hypotheses` | 48 |  |
| `zval_unit_eq_zero` | `L20261018.Witness.Step010_q7_nonzero_cup` | 43 |  |
| `α` | `L20261018.Ch2.Brauer.Step011_kummer_extension_generator` | 36 |  |
| `α_pow` | `L20261018.Ch2.Brauer.Step011_kummer_extension_generator` | 39 |  |
| `σ` | `L20261018.Ch2.Brauer.Step011_kummer_extension_generator` | 46 |  |
| `σ_α` | `L20261018.Ch2.Brauer.Step011_kummer_extension_generator` | 50 |  |
