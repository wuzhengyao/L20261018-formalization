# `L20261018/` — the development, organised by the paper

576 modules in 20 directories.  [Root README](../README.md) · [`DECLARATIONS.md`](../DECLARATIONS.md) · [`RENAME-MAP.tsv`](../RENAME-MAP.tsv) · [`PROVENANCE.tsv`](../PROVENANCE.tsv) · [`WORKFLOW.md`](../WORKFLOW.md)

Every module is a `StepNNN_<slug>` whose number is order preserving inside its
directory (so reading upwards reads the proof in the order it was built) and whose
slug says what the step proves.  `import L20261018` pulls in everything.

## Directories

| directory | modules | declarations | what is there |
|---|---|---|---|
| [`Ch2/Brauer/`](Ch2/Brauer/README.md) | 35 | 228 | sec. 2.1 · central simple algebras, Brauer group, crossed and symbol algebras |
| [`Ch2/Hensel/Inertia/`](Ch2/Hensel/Inertia/README.md) | 40 | 277 | sec. 2.4 · inertia, K_nr, the cohomological dimension of I |
| [`Ch2/Hensel/ResidueMap/`](Ch2/Hensel/ResidueMap/README.md) | 84 | 359 | sec. 2.4 · the residue map, its exact sequence, (R1) and (R2) |
| [`Ch2/Hensel/TameSymbol/`](Ch2/Hensel/TameSymbol/README.md) | 16 | 104 | sec. 2.4 · the tame symbol and the Merkurjev-Suslin closure |
| [`Ch2/Hensel/UnitsCupVanish/`](Ch2/Hensel/UnitsCupVanish/README.md) | 41 | 184 | sec. 2.4 · the named hypothesis `UnitsCupVanish` and its discharge |
| [`Ch2/Hensel/Valuation/`](Ch2/Hensel/Valuation/README.md) | 40 | 129 | sec. 2.4 · valuations, integrality, the uniformizer, Hensel |
| [`Ch2/Kummer/`](Ch2/Kummer/README.md) | 51 | 183 | sec. 2.2 · Kummer theory, cup products, the cyclic norm criterion |
| [`Ch2/Rost/`](Ch2/Rost/README.md) | 2 | 18 | sec. 2.5 · Rost invariant, Suslin groups, cohomological dimension |
| [`Ch3/BiKummer/`](Ch3/BiKummer/README.md) | 17 | 72 | sec. 3.1 · the bi-Kummer structure, the rank barrier, the norm image |
| [`Ch3/NormImage/`](Ch3/NormImage/README.md) | 22 | 89 | sec. 3.2 · the short exact sequence of the norm image, the dimension formula |
| [`Ch4/`](Ch4/README.md) | 48 | 213 | sec. 4 · Hensel valuations and ramification in the first slot |
| [`Core/`](Core/README.md) | 2 | 44 | carriers of the paper's objects; the master abstract statements |
| [`Infra/Algebra/`](Infra/Algebra/README.md) | 3 | 8 | general algebra: linear algebra, group theory, adjoin-root tooling |
| [`Infra/Cohomology/`](Infra/Cohomology/README.md) | 10 | 41 | general cohomology infrastructure; no single paper statement owns it |
| [`Infra/Cohomology/Boundary/`](Infra/Cohomology/Boundary/README.md) | 35 | 135 | sec. 2.3 · the Hochschild-Serre boundary map, assembled |
| [`Infra/Cohomology/Coinduced/`](Infra/Cohomology/Coinduced/README.md) | 41 | 164 | sec. 2.3 · coinduced modules, invariants, GS (6.17) |
| [`Infra/Cohomology/Conjugation/`](Infra/Cohomology/Conjugation/README.md) | 14 | 51 | sec. 2.3/2.4 · conjugation invariance of H^1(I, mu_p) |
| [`Infra/Cohomology/ResidueLES/`](Infra/Cohomology/ResidueLES/README.md) | 33 | 138 | sec. 2.4 · the continuous residue long exact sequence |
| [`Infra/Galois/`](Infra/Galois/README.md) | 2 | 5 | absolute Galois group carriers and subgroup plumbing |
| [`Witness/`](Witness/README.md) | 40 | 188 | concrete witnesses (Q_7, F_7((t)), ...) for the nonemptiness obligations |

## Items of `raw/L20261018.tex`

The paper's own statements, in the paper's order (the section is the one the
label lives in).  A module appears here when its `@source` annotation names
that label.  Raw `line:` anchors come last -- statements the paper leaves
unnumbered.

| paper label | modules |
|---|---|
| `cor:symbol-cup` | [`Step012_symbol_cup`](Ch2/Kummer/Step012_symbol_cup.lean) |
| `prop:prelim-kummer-valuation` | [`Step002_unit_reduction_principal_units`](Ch2/Hensel/ResidueMap/Step002_unit_reduction_principal_units.lean), [`Step003_residue_valuation_h1`](Ch2/Hensel/ResidueMap/Step003_residue_valuation_h1.lean), [`Step004_valuation_decomposition_unique`](Ch2/Hensel/ResidueMap/Step004_valuation_decomposition_unique.lean), [`Step008_exists_unit_rep`](Ch2/Hensel/ResidueMap/Step008_exists_unit_rep.lean), [`Step043_units_mod_pth_powers_paper_level`](Ch2/Hensel/ResidueMap/Step043_units_mod_pth_powers_paper_level.lean), [`Step056_kummer_valuation_abstract_hensel`](Ch2/Hensel/ResidueMap/Step056_kummer_valuation_abstract_hensel.lean), [`Step001_residue_valuation_without_completeness`](Ch2/Hensel/Valuation/Step001_residue_valuation_without_completeness.lean), [`Step017_kummer_class_pow_identities`](Ch2/Kummer/Step017_kummer_class_pow_identities.lean) |
| `prop:prelim-residue` | [`Step012_bridge_kc_unit_cup_zero`](Ch2/Hensel/ResidueMap/Step012_bridge_kc_unit_cup_zero.lean), [`Step013_huu_reduced_to_linear_dependence`](Ch2/Hensel/ResidueMap/Step013_huu_reduced_to_linear_dependence.lean), [`Step017_hdep_huu_are_theorems`](Ch2/Hensel/ResidueMap/Step017_hdep_huu_are_theorems.lean), [`Step029_model_field_from_hypothesis`](Ch2/Hensel/ResidueMap/Step029_model_field_from_hypothesis.lean), [`Step032_hskew_discharged`](Ch2/Hensel/ResidueMap/Step032_hskew_discharged.lean), [`Step033_residue_sequence_exact_split`](Ch2/Hensel/ResidueMap/Step033_residue_sequence_exact_split.lean), [`Step003_ramified_vanishing_paper_objects`](Ch4/Step003_ramified_vanishing_paper_objects.lean), [`Step034_exists_d_unconditional`](Ch4/Step034_exists_d_unconditional.lean), [`Step008_tame_residue_facts_q7`](Witness/Step008_tame_residue_facts_q7.lean) |
| `eq:prelim-tame` | [`Step001_tame_symbol_general_formula`](Ch2/Hensel/TameSymbol/Step001_tame_symbol_general_formula.lean), [`Step002_tame_symbol_formula`](Ch2/Hensel/TameSymbol/Step002_tame_symbol_formula.lean), [`Step006_tame_symbol_explicit`](Ch2/Hensel/TameSymbol/Step006_tame_symbol_explicit.lean), [`Step007_tame_symbol_triviality`](Ch2/Hensel/TameSymbol/Step007_tame_symbol_triviality.lean), [`Step008_tame_symbol_bilinear`](Ch2/Hensel/TameSymbol/Step008_tame_symbol_bilinear.lean) |
| `lem:orthogonal` | [`Step002_basic_inclusions_paper_objects`](Ch3/BiKummer/Step002_basic_inclusions_paper_objects.lean), [`Step013_orthogonal_roots_trivial`](Ch3/BiKummer/Step013_orthogonal_roots_trivial.lean) |
| `thm:rank-barrier` | [`Step017_rank_barrier_unconditional`](Ch3/BiKummer/Step017_rank_barrier_unconditional.lean) |
| `lem:basic-inclusions` | [`Step002_basic_inclusions_paper_objects`](Ch3/BiKummer/Step002_basic_inclusions_paper_objects.lean), [`Step012_basic_inclusions_cor_subset`](Ch3/BiKummer/Step012_basic_inclusions_cor_subset.lean), [`Step015_h_nrd_kummer_form`](Ch3/BiKummer/Step015_h_nrd_kummer_form.lean) |
| `prop:hs-special` | [`Step006_hs_special_five_term`](Ch3/NormImage/Step006_hs_special_five_term.lean) |
| `thm:hs-tate-exact-sequences` | [`Step005_three_five_one_first_ses`](Ch3/NormImage/Step005_three_five_one_first_ses.lean), [`Step007_three_five_two_real_objects`](Ch3/NormImage/Step007_three_five_two_real_objects.lean), [`Step008_three_five_u_wiring`](Ch3/NormImage/Step008_three_five_u_wiring.lean), [`Step001_bi_kummer_data`](Core/Step001_bi_kummer_data.lean) |
| `thm:dimension` | [`Step022_dimension_paper_objects`](Ch3/NormImage/Step022_dimension_paper_objects.lean), [`Step001_bi_kummer_data`](Core/Step001_bi_kummer_data.lean) |
| `lem:basis-change` | [`Step001_basis_change_first_slot`](Ch4/Step001_basis_change_first_slot.lean), [`Step010_basis_change_brauer_class`](Ch4/Step010_basis_change_brauer_class.lean) |
| `lem:ramified-vanishing` | [`Step002_unit_reduction_principal_units`](Ch2/Hensel/ResidueMap/Step002_unit_reduction_principal_units.lean), [`Step005_residue_cup_data_fields_reduced`](Ch2/Hensel/ResidueMap/Step005_residue_cup_data_fields_reduced.lean), [`Step006_tame_pi_u_of`](Ch2/Hensel/ResidueMap/Step006_tame_pi_u_of.lean), [`Step018_huu_discharged`](Ch2/Hensel/ResidueMap/Step018_huu_discharged.lean), [`Step002_residue_cup_data_shape`](Ch4/Step002_residue_cup_data_shape.lean), [`Step003_ramified_vanishing_paper_objects`](Ch4/Step003_ramified_vanishing_paper_objects.lean) |
| `thm:ramified` | [`Step004_thm_ramified_assembly`](Ch4/Step004_thm_ramified_assembly.lean), [`Step006_thm_ramified_no_d`](Ch4/Step006_thm_ramified_no_d.lean) |
| `line:1646` | [`Step005_corollary_four_four_dimension`](Ch4/Step005_corollary_four_four_dimension.lean), [`Step007_corollary_four_four_no_d`](Ch4/Step007_corollary_four_four_no_d.lean), [`Step008_rank_contradiction_single_phi`](Ch4/Step008_rank_contradiction_single_phi.lean), [`Step009_dk_eq_one_is_a_theorem`](Ch4/Step009_dk_eq_one_is_a_theorem.lean), [`Step040_corollary_four_four_paper_level`](Ch4/Step040_corollary_four_four_paper_level.lean) |
| `line:1017` | [`Step001_open_residual_advance`](Ch2/Hensel/ResidueMap/Step001_open_residual_advance.lean), [`Step002_unit_reduction_principal_units`](Ch2/Hensel/ResidueMap/Step002_unit_reduction_principal_units.lean), [`Step002_principal_units_without_completeness`](Ch2/Hensel/Valuation/Step002_principal_units_without_completeness.lean) |
| `line:1023` | [`Step041_residue_map_single_hypothesis`](Ch2/Hensel/ResidueMap/Step041_residue_map_single_hypothesis.lean), [`Step016_d_witness_finite_residue`](Witness/Step016_d_witness_finite_residue.lean) |
| `line:1050` | [`Step024_delta_two_refined`](Ch2/Hensel/ResidueMap/Step024_delta_two_refined.lean), [`Step051_h1_z_equiv_galo_v`](Ch2/Hensel/ResidueMap/Step051_h1_z_equiv_galo_v.lean), [`Step053_exists_d_three_properties`](Ch2/Hensel/ResidueMap/Step053_exists_d_three_properties.lean), [`Step004_tame_symbol_hyp_divisible_residue`](Ch2/Hensel/TameSymbol/Step004_tame_symbol_hyp_divisible_residue.lean), [`Step006_tame_symbol_explicit`](Ch2/Hensel/TameSymbol/Step006_tame_symbol_explicit.lean), [`Step016_tame_symbol_hyp_merkurjev_suslin`](Ch2/Hensel/TameSymbol/Step016_tame_symbol_hyp_merkurjev_suslin.lean), [`Step033_ch4_three_and_exists_d`](Ch4/Step033_ch4_three_and_exists_d.lean), [`Step039_ch4_four_without_finite_residue`](Ch4/Step039_ch4_four_without_finite_residue.lean) |
| `line:1052` | [`Step045_residue_prop_two_literal`](Ch2/Hensel/ResidueMap/Step045_residue_prop_two_literal.lean) |
| `line:1596` | [`Step011_transition_paragraph_4_1_4_2`](Ch4/Step011_transition_paragraph_4_1_4_2.lean), [`Step013_basis_selection_u`](Ch4/Step013_basis_selection_u.lean) |
| `line:1599` | [`Step011_transition_paragraph_4_1_4_2`](Ch4/Step011_transition_paragraph_4_1_4_2.lean) |
| `line:1608` | [`Step024_delta_two_refined`](Ch2/Hensel/ResidueMap/Step024_delta_two_refined.lean), [`Step036_residue_cup_product_interface`](Ch2/Hensel/ResidueMap/Step036_residue_cup_product_interface.lean), [`Step001_residue_valuation_without_completeness`](Ch2/Hensel/Valuation/Step001_residue_valuation_without_completeness.lean), [`Step012_ramified_vanishing_paper_route`](Ch4/Step012_ramified_vanishing_paper_route.lean), [`Step014_ramified_vanishing_hensel_level`](Ch4/Step014_ramified_vanishing_hensel_level.lean), [`Step031_ch4_closed_units_cup_vanish`](Ch4/Step031_ch4_closed_units_cup_vanish.lean), [`Step033_ch4_three_and_exists_d`](Ch4/Step033_ch4_three_and_exists_d.lean), [`Step039_ch4_four_without_finite_residue`](Ch4/Step039_ch4_four_without_finite_residue.lean), [`Step047_ch4_three_d_free`](Ch4/Step047_ch4_three_d_free.lean), [`Step025_f7t_hne_hval`](Witness/Step025_f7t_hne_hval.lean), [`Step032_f7t_v_finite_dimensional`](Witness/Step032_f7t_v_finite_dimensional.lean) |
| `line:1622` | [`Step002_principal_units_without_completeness`](Ch2/Hensel/Valuation/Step002_principal_units_without_completeness.lean) |
| `line:1635` | [`Step041_thm_ramified_two_rank_barrier`](Ch4/Step041_thm_ramified_two_rank_barrier.lean) |
| `line:1636` | [`Step036_residue_cup_product_interface`](Ch2/Hensel/ResidueMap/Step036_residue_cup_product_interface.lean), [`Step001_residue_valuation_without_completeness`](Ch2/Hensel/Valuation/Step001_residue_valuation_without_completeness.lean), [`Step017_thm_ramified_and_corollary_class_free`](Ch4/Step017_thm_ramified_and_corollary_class_free.lean), [`Step018_single_carrier_thm_ramified`](Ch4/Step018_single_carrier_thm_ramified.lean), [`Step031_ch4_closed_units_cup_vanish`](Ch4/Step031_ch4_closed_units_cup_vanish.lean), [`Step033_ch4_three_and_exists_d`](Ch4/Step033_ch4_three_and_exists_d.lean), [`Step037_ch4_without_finite_dimensional_v`](Ch4/Step037_ch4_without_finite_dimensional_v.lean), [`Step039_ch4_four_without_finite_residue`](Ch4/Step039_ch4_four_without_finite_residue.lean), [`Step047_ch4_three_d_free`](Ch4/Step047_ch4_three_d_free.lean), [`Step036_f7t_thm_ramified_witness_paper_objects`](Witness/Step036_f7t_thm_ramified_witness_paper_objects.lean) |
| `line:1637` | [`Step018_single_carrier_thm_ramified`](Ch4/Step018_single_carrier_thm_ramified.lean) |
| `line:1648` | [`Step036_residue_cup_product_interface`](Ch2/Hensel/ResidueMap/Step036_residue_cup_product_interface.lean), [`Step040_ker_v_finrank_le_one`](Ch2/Hensel/ResidueMap/Step040_ker_v_finrank_le_one.lean), [`Step001_residue_valuation_without_completeness`](Ch2/Hensel/Valuation/Step001_residue_valuation_without_completeness.lean), [`Step017_thm_ramified_and_corollary_class_free`](Ch4/Step017_thm_ramified_and_corollary_class_free.lean), [`Step031_ch4_closed_units_cup_vanish`](Ch4/Step031_ch4_closed_units_cup_vanish.lean), [`Step033_ch4_three_and_exists_d`](Ch4/Step033_ch4_three_and_exists_d.lean), [`Step039_ch4_four_without_finite_residue`](Ch4/Step039_ch4_four_without_finite_residue.lean), [`Step047_ch4_three_d_free`](Ch4/Step047_ch4_three_d_free.lean) |
| `line:739` | [`Step014_tame_steinberg_relation`](Ch2/Hensel/TameSymbol/Step014_tame_steinberg_relation.lean) |
| `line:992` | [`Step043_units_mod_pth_powers_paper_level`](Ch2/Hensel/ResidueMap/Step043_units_mod_pth_powers_paper_level.lean) |

Section of each labelled item: `cor:symbol-cup` (sec. 2.2); `prop:prelim-kummer-valuation` (sec. 2.4); `prop:prelim-residue` (sec. 2.4); `eq:prelim-tame` (sec. 2.4); `lem:orthogonal` (sec. 3.1); `thm:rank-barrier` (sec. 3.1); `lem:basic-inclusions` (sec. 3.1); `prop:hs-special` (sec. 3.2); `thm:hs-tate-exact-sequences` (sec. 3.2); `thm:dimension` (sec. 3.2); `lem:basis-change` (sec. 4); `lem:ramified-vanishing` (sec. 4); `thm:ramified` (sec. 4); `line:1646` (sec. 4.4 (unnumbered)).

## Items of `raw/GilleSzamuely2017.tex`

Statements the development quotes from this source rather than from the
paper.  The label is shown bare here; in `DECLARATIONS.md` and in the
per-directory tables it is prefixed with the source, `GS2017/<label>`, so that it cannot be
confused with a paper label.

| label | modules |
|---|---|
| `cons-residue-map-finite-coefficients-2` | [`Step014_cd_p_inertia_instance`](Ch2/Hensel/Inertia/Step014_cd_p_inertia_instance.lean) |
| `lemma-additive-hilbert90` | [`Step007_additive_hilbert90`](Infra/Cohomology/Step007_additive_hilbert90.lean) |
| `lemma-residue-cup-product` | [`Step036_residue_cup_product_interface`](Ch2/Hensel/ResidueMap/Step036_residue_cup_product_interface.lean) |
| `line:3580` | [`Step017_h0_conj_compatibility`](Infra/Cohomology/Boundary/Step017_h0_conj_compatibility.lean) |
| `line:3585` | [`Step016_delta_zero_naturality`](Infra/Cohomology/Boundary/Step016_delta_zero_naturality.lean) |
| `line:8152` | [`Step007_knr_correct_carrier`](Ch2/Hensel/Inertia/Step007_knr_correct_carrier.lean), [`Step011_kummer_coeff_to_knr`](Ch2/Hensel/Inertia/Step011_kummer_coeff_to_knr.lean) |
| `line:8156` | [`Step006_knr_coefficient_action`](Ch2/Hensel/Inertia/Step006_knr_coefficient_action.lean), [`Step009_galois_preserves_knr`](Ch2/Hensel/Inertia/Step009_galois_preserves_knr.lean) |
| `line:8160` | [`Step006_knr_coefficient_action`](Ch2/Hensel/Inertia/Step006_knr_coefficient_action.lean), [`Step009_galois_preserves_knr`](Ch2/Hensel/Inertia/Step009_galois_preserves_knr.lean), [`Step010_knr_continuous_smul`](Ch2/Hensel/Inertia/Step010_knr_continuous_smul.lean), [`Step011_kummer_coeff_to_knr`](Ch2/Hensel/Inertia/Step011_kummer_coeff_to_knr.lean), [`Step044_residue_map_unramified_units`](Ch2/Hensel/ResidueMap/Step044_residue_map_unramified_units.lean), [`Step052_delta_two_candidate_zero`](Ch2/Hensel/ResidueMap/Step052_delta_two_candidate_zero.lean) |
| `line:8162` | [`Step005_knr_explicit_laurent`](Ch2/Hensel/Inertia/Step005_knr_explicit_laurent.lean), [`Step008_gs61_on_correct_knr`](Ch2/Hensel/Inertia/Step008_gs61_on_correct_knr.lean), [`Step010_knr_continuous_smul`](Ch2/Hensel/Inertia/Step010_knr_continuous_smul.lean) |
| `line:8163` | [`Step008_gs61_on_correct_knr`](Ch2/Hensel/Inertia/Step008_gs61_on_correct_knr.lean), [`Step044_residue_map_unramified_units`](Ch2/Hensel/ResidueMap/Step044_residue_map_unramified_units.lean) |
| `line:8165` | [`Step005_knr_explicit_laurent`](Ch2/Hensel/Inertia/Step005_knr_explicit_laurent.lean) |
| `line:8176` | [`Step012_kummer_coeff_equivariant`](Ch2/Hensel/Inertia/Step012_kummer_coeff_equivariant.lean) |
| `line:9497` | [`Step015_rep_quotient_structure`](Infra/Cohomology/Boundary/Step015_rep_quotient_structure.lean) |
| `line:9498` | [`Step018_delta_two_conditional`](Infra/Cohomology/Boundary/Step018_delta_two_conditional.lean) |
| `line:9528` | [`Step012_continuous_t_carrier`](Infra/Cohomology/ResidueLES/Step012_continuous_t_carrier.lean) |
| `line:9625` | [`Step013_inertia_pro_p_sylow_data`](Ch2/Hensel/Inertia/Step013_inertia_pro_p_sylow_data.lean), [`Step001_cd_p_z_p_le_one`](Ch2/Rost/Step001_cd_p_z_p_le_one.lean) |
| `line:9626` | [`Step018_procyclic_l_part_sylow`](Ch2/Hensel/Inertia/Step018_procyclic_l_part_sylow.lean) |
| `line:9627` | [`Step013_inertia_pro_p_sylow_data`](Ch2/Hensel/Inertia/Step013_inertia_pro_p_sylow_data.lean), [`Step014_cd_p_inertia_instance`](Ch2/Hensel/Inertia/Step014_cd_p_inertia_instance.lean), [`Step022_cd_p_inertia_unconditional`](Ch2/Hensel/Inertia/Step022_cd_p_inertia_unconditional.lean), [`Step001_cd_p_z_p_le_one`](Ch2/Rost/Step001_cd_p_z_p_le_one.lean) |
| `prop-cd-Z-hat` | [`Step001_cd_p_z_p_le_one`](Ch2/Rost/Step001_cd_p_z_p_le_one.lean) |
| `prop-residue-map-long-exact` | [`Step001_f2_delta_zero_vanishes`](Infra/Cohomology/ResidueLES/Step001_f2_delta_zero_vanishes.lean), [`Step003_f1_square`](Infra/Cohomology/ResidueLES/Step003_f1_square.lean), [`Step013_continuous_f1`](Infra/Cohomology/ResidueLES/Step013_continuous_f1.lean) |
| `prop-units-cohomology` | [`Step052_delta_two_candidate_zero`](Ch2/Hensel/ResidueMap/Step052_delta_two_candidate_zero.lean) |
| `sec:cohomology-complete-dv` | [`Step003_knr_galois_quotient`](Ch2/Hensel/Inertia/Step003_knr_galois_quotient.lean), [`Step004_knr_galois_zhat`](Ch2/Hensel/Inertia/Step004_knr_galois_zhat.lean), [`Step005_cont_integral_dual_shift`](Infra/Cohomology/Step005_cont_integral_dual_shift.lean) |

## Items of `scratch/lean-l20261018/serre-p67-prop7-cors.txt`

Statements the development quotes from this source rather than from the
paper.  The label is shown bare here; in `DECLARATIONS.md` and in the
per-directory tables it is prefixed with the source so that it cannot be
confused with a paper label.

| label | modules |
|---|---|
| `line:8` | [`Step015_cd_p_procyclic_criterion`](Ch2/Hensel/Inertia/Step015_cd_p_procyclic_criterion.lean), [`Step016_inertia_loc_carrier_alignment`](Ch2/Hensel/Inertia/Step016_inertia_loc_carrier_alignment.lean), [`Step017_tame_module_procyclic`](Ch2/Hensel/Inertia/Step017_tame_module_procyclic.lean) |

## Provenance of the annotations

Every `@source` annotation is checked against the sources in `raw/` by `scripts/check-provenance.py`, whose verdict is `PROVENANCE.tsv`: 20 labelled items are present in the file their annotation names; 0 labelled elsewhere; 0 not found; 31 line anchors (which a label search cannot check); 0 annotation whose file is absent.

## What the comparators check, and where it lives

Taken from the `specs` list of each `comparator/*/Solution.lean`, so this table
cannot drift from what the official tool actually re-checks.  The build of this
page fails if a target is not a declaration of the development.

**`ch3u`** — chapter 3, 8 declarations, unconditional at the paper's hypothesis level

| target | declaration | module |
|---|---|---|
| `tm_3u_1_1` | `L20261018.lemma_3_1_1_kummer` (line 33) | [`Step002_basic_inclusions_paper_objects`](Ch3/BiKummer/Step002_basic_inclusions_paper_objects.lean) |
| `tm_3u_1_2` | `RootsOfUnityExists.lemma_3_1_2_galo'` (line 57) | [`Step013_orthogonal_roots_trivial`](Ch3/BiKummer/Step013_orthogonal_roots_trivial.lean) |
| `tm_3u_1_3` | `L20261018.lemma_3_1_3_kummer` (line 45) | [`Step002_basic_inclusions_paper_objects`](Ch3/BiKummer/Step002_basic_inclusions_paper_objects.lean) |
| `tm_3u_2_1` | `L20261018.theorem_3_2_1_kummer'` (line 17) | [`Step017_rank_barrier_unconditional`](Ch3/BiKummer/Step017_rank_barrier_unconditional.lean) |
| `tm_3u_2_2` | `L20261018.theorem_3_2_2_kummer'` (line 65) | [`Step017_rank_barrier_unconditional`](Ch3/BiKummer/Step017_rank_barrier_unconditional.lean) |
| `tm_3u_3_1` | `CrossedProductNrd.hNrd_crossedProduct` (line 43) | [`Step003_h_nrd_from_field_norm`](Ch3/BiKummer/Step003_h_nrd_from_field_norm.lean) |
| `tm_3u_3_3` | `L20261018.lemma_3_3_3_kummer` (line 61) | [`Step002_basic_inclusions_paper_objects`](Ch3/BiKummer/Step002_basic_inclusions_paper_objects.lean) |
| `tm_3u_5_1` | `GaloFive.theorem_3_5_1_galo` (line 70) | [`Step005_three_five_one_first_ses`](Ch3/NormImage/Step005_three_five_one_first_ses.lean) |

**`ch4u`** — chapter 4, 7 declarations, unconditional (`d` is constructed)

| target | declaration | module |
|---|---|---|
| `tm_u_d` | `L20261018.exists_residueMap` (line 323) | [`Step046_exists_residue_map`](Ch4/Step046_exists_residue_map.lean) |
| `tm_u_trf` | `L20261018.tameResidueFacts_uncond` (line 409) | [`Step046_exists_residue_map`](Ch4/Step046_exists_residue_map.lean) |
| `tm_u_4_2` | `L20261018.orth_eq_bot_viaResidue` (line 76) | [`Step047_ch4_three_d_free`](Ch4/Step047_ch4_three_d_free.lean) |
| `tm_u_4_3_1` | `L20261018.thm_ramified_1_viaResidue` (line 119) | [`Step047_ch4_three_d_free`](Ch4/Step047_ch4_three_d_free.lean) |
| `tm_u_4_4` | `L20261018.corollary_4_4_viaResidue` (line 174) | [`Step047_ch4_three_d_free`](Ch4/Step047_ch4_three_d_free.lean) |
| `tm_u_hyp` | `L20261018.ch4TameSymbolHyp_viaResidue` (line 72) | [`Step040_tame_symbol_hyp_witness`](Witness/Step040_tame_symbol_hyp_witness.lean) |
| `tm_u_disj` | `L20261018.disjoint_viaResidue` (line 100) | [`Step040_tame_symbol_hyp_witness`](Witness/Step040_tame_symbol_hyp_witness.lean) |

