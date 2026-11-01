# `L20261018/Infra/Cohomology` — general cohomology infrastructure; no single paper statement owns it

10 modules.  Part of the development's [index](../../README.md); see also [`DECLARATIONS.md`](../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../RENAME-MAP.tsv).

Paper items formalised here: `lemma-additive-hilbert90`, `sec:cohomology-complete-dv`.

| module | paper | declarations | lines |
|---|---|---|---|
| [`Step001_coeff_map_scalar_restriction`](Step001_coeff_map_scalar_restriction.lean) |  | `coeffMap_restrictScalarsIntEquiv_comm` | 63 |
| [`Step002_map_coefficient_restriction`](Step002_map_coefficient_restriction.lean) |  | `map_restrictScalarsIntEquiv_comm` | 56 |
| [`Step003_q_first_acyclicity`](Step003_q_first_acyclicity.lean) |  | `subsingleton_H1_int_absGal` | 61 |
| [`Step004_q_discrete_h1_acyclic`](Step004_q_discrete_h1_acyclic.lean) |  | `Qdisc`, `subsingleton_H1_rat_disc_absGal` | 58 |
| [`Step005_cont_integral_dual_shift`](Step005_cont_integral_dual_shift.lean) | `sec:cohomology-complete-dv` | `QoverZdisc`, `QdiscRep`, `subsingleton_continuousCohomology_rat_disc`, `subsingleton_continuousCohomology_rat_disc_of_pos` (+6 more) | 199 |
| [`Step006_rv_complex_assembly`](Step006_rv_complex_assembly.lean) |  | `dimShiftEquiv`, `dimShiftEquiv_injective`, `residueMap`, `residueMap_exact` (+1 more) | 138 |
| [`Step007_additive_hilbert90`](Step007_additive_hilbert90.lean) | `lemma-additive-hilbert90` | `trivialBotAction`, `fB`, `locB`, `mkB` (+9 more) | 200 |
| [`Step008_recon_availability_lock`](Step008_recon_availability_lock.lean) |  | `brauer_h2_equiv_available`, `kummer_injective_available`, `kummer_range_available`, `muP_trivial_available` | 71 |
| [`Step009_h2_p_torsion`](Step009_h2_p_torsion.lean) |  | `nsmulAddMonoidHom_kummerCoeff_eq_zero`, `kummerCoeffH2_nsmul_eq_zero` | 61 |
| [`Step010_trivial_action_fixed_points`](Step010_trivial_action_fixed_points.lean) |  | `fixedPoints_zmod_eq_top`, `fixedPointsZModEquiv` | 79 |
