# `L20261018/Ch3/BiKummer` — sec. 3.1 · the bi-Kummer structure, the rank barrier, the norm image

17 modules.  Part of the development's [index](../../README.md); see also [`DECLARATIONS.md`](../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../RENAME-MAP.tsv).

Paper items formalised here: `lem:basic-inclusions`, `lem:orthogonal`, `thm:rank-barrier`.

| module | paper | declarations | lines |
|---|---|---|---|
| [`Step001_bi_kummer_data_from_kummer`](Step001_bi_kummer_data_from_kummer.lean) |  | `biKummerDataKummer`, `biKummerDataKummer_a1`, `biKummerDataKummer_a2`, `neZero_two_zmod` | 63 |
| [`Step002_basic_inclusions_paper_objects`](Step002_basic_inclusions_paper_objects.lean) | `lem:basic-inclusions`, `lem:orthogonal` | `lemma_3_1_1_kummer`, `lemma_3_1_3_kummer`, `lemma_3_3_3_kummer` | 71 |
| [`Step003_h_nrd_from_field_norm`](Step003_h_nrd_from_field_norm.lean) |  | `hNrd_crossedProduct` | 55 |
| [`Step004_h_nrd_well_defined`](Step004_h_nrd_well_defined.lean) |  | `algEquivToLinearEquiv`, `mulRight_conj`, `nrd_algEquiv`, `nrd_algEquivOfCoboundary` (+1 more) | 97 |
| [`Step005_kummer_class_generators`](Step005_kummer_class_generators.lean) |  | `kummerClassHom`, `kummerClassHom_apply`, `kummerClass_eq_iff`, `kummerRes_kummerMap_eq_one_of_mem_sup` (+2 more) | 99 |
| [`Step006_explicit_restriction_kernel`](Step006_explicit_restriction_kernel.lean) |  | `kummerCoeffMap_bijective`, `kummerCoeffMap_smul_comp`, `kummerRes_toAdd_eq`, `kummerRes_eq_one_iff_explicitRes1_eq_zero` (+3 more) | 151 |
| [`Step007_restriction_coefficient_change`](Step007_restriction_coefficient_change.lean) |  | `explicitRes1_explicitMap1_id` | 50 |
| [`Step008_restriction_canonical_h1`](Step008_restriction_canonical_h1.lean) |  | `res_explicitH1_kummerMap_eq_zero_iff` | 71 |
| [`Step009_h_nrd_presentation_independent`](Step009_h_nrd_presentation_independent.lean) |  | `nrd_one`, `nrd_inv_unit`, `nrd_conj_unit`, `nrd_algEquiv_self` (+3 more) | 157 |
| [`Step010_restriction_kernel_paper_v`](Step010_restriction_kernel_paper_v.lean) |  | `res_restrictScalarsIntEquiv_comm`, `res_kummerClass_eq_zero_iff` | 108 |
| [`Step011_restriction_kernel_eq_u`](Step011_restriction_kernel_eq_u.lean) |  | `kummerClass_surjective`, `kummerClass_mul`, `kummerClass_inv`, `kummerClass_mem_span_of_mem_closure` (+3 more) | 188 |
| [`Step012_basic_inclusions_cor_subset`](Step012_basic_inclusions_cor_subset.lean) | `lem:basic-inclusions` | `zmodMulPairing`, `kummerExplicit`, `explicitRes1_kummerExplicit_eq_zero`, `lemma_3_3_2_explicit` | 114 |
| [`Step013_orthogonal_roots_trivial`](Step013_orthogonal_roots_trivial.lean) | `lem:orthogonal` | `exists_pow_eq_algebraMap`, `hroots`, `lemma_3_1_2_galo'` | 72 |
| [`Step014_splitting_field`](Step014_splitting_field.lean) |  | `IsSplit`, `of_algEquiv`, `tensor`, `symbolAlg` (+3 more) | 102 |
| [`Step015_h_nrd_kummer_form`](Step015_h_nrd_kummer_form.lean) | `lem:basic-inclusions` | `kummerCor_kummerMap_eq`, `exists_kummerCor_eq_kummerMap_of_nrd`, `range_kummerCor_subset_of_mk_eq`, `range_kummerCor_subset_of_nrd` (+1 more) | 133 |
| [`Step016_hind_kummer`](Step016_hind_kummer.lean) |  | `index_self_eq_one`, `index_self_le`, `notMem_pow_of_notMem_powerSubgroup`, `indOfH2_le_of_class_one` (+1 more) | 178 |
| [`Step017_rank_barrier_unconditional`](Step017_rank_barrier_unconditional.lean) | `thm:rank-barrier` | `theorem_3_2_1_kummer'`, `paperCup`, `theorem_3_2_1_kummer'`, `theorem_3_2_2_kummer'` | 84 |
