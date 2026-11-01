# `L20261018/Ch2/Hensel/TameSymbol` — sec. 2.4 · the tame symbol and the Merkurjev-Suslin closure

16 modules.  Part of the development's [index](../../../README.md); see also [`DECLARATIONS.md`](../../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../../RENAME-MAP.tsv).

Source items formalised here: `eq:prelim-tame`; 2 line anchors.

| module | source item | declarations | lines |
|---|---|---|---|
| [`Step001_tame_symbol_general_formula`](Step001_tame_symbol_general_formula.lean) | `eq:prelim-tame` | `cup_pi_pi_eq_zero`, `res_cup_eq` | 97 |
| [`Step002_tame_symbol_formula`](Step002_tame_symbol_formula.lean) | `eq:prelim-tame` | `val_eq_of_split`, `val_eq_of_split'`, `infl_eq_of_split'`, `res_cup_infl_pi` (+7 more) | 175 |
| [`Step003_ch4_tame_symbol_hyp`](Step003_ch4_tame_symbol_hyp.lean) |  | `Ch4TameSymbolHyp`, `ch4TameSymbolHyp_iff_disjoint`, `ch4TameSymbolHyp_of_dependent` | 102 |
| [`Step004_tame_symbol_hyp_divisible_residue`](Step004_tame_symbol_hyp_divisible_residue.lean) | `line:1050` | `knrResidueObligation_of_divisibleResidue`, `ch4TameSymbolHyp_of_divisibleResidue`, `ch4TameSymbolHyp_of_finite'` | 107 |
| [`Step005_tame_symbol_hyp_iff_r1_r2`](Step005_tame_symbol_hyp_iff_r1_r2.lean) |  | `ch4TameSymbolHyp_iff_tameResidueFacts`, `not_ch4TameSymbolHyp_of_not_disjoint` | 99 |
| [`Step006_tame_symbol_explicit`](Step006_tame_symbol_explicit.lean) | `eq:prelim-tame`, `line:1050` | `tameExpr`, `tameExpr_coe`, `tameExpr_uu`, `tameExpr_u_pi` (+20 more) | 357 |
| [`Step007_tame_symbol_triviality`](Step007_tame_symbol_triviality.lean) | `eq:prelim-tame` | `kummerClass_neg_one`, `kummerClass_eq_zero_of_residue_eq_one` | 89 |
| [`Step008_tame_symbol_bilinear`](Step008_tame_symbol_bilinear.lean) | `eq:prelim-tame` | `tameExpr_eq_zero_iff`, `tameExpr_add_right`, `tameExpr_add_left`, `tameExpr_smul_right` (+3 more) | 105 |
| [`Step009_tame_symbol_factors_descent`](Step009_tame_symbol_factors_descent.lean) |  | `tameExpr_congr_of_tameSymbolFactors`, `tameExpr_sum_eq_zero_of_tameSymbolFactors`, `tameExpr_zero_right`, `tameExpr_zero_left` | 83 |
| [`Step010_tame_symbol_two_chain_criterion`](Step010_tame_symbol_two_chain_criterion.lean) |  | `tameChainCond`, `tameChainCond_of_tameSymbolFactors`, `tamePointwise_of_tameChainCond` | 82 |
| [`Step011_tame_sum_condition`](Step011_tame_sum_condition.lean) |  | `tameSumCond`, `tameSumCond_of_tameSymbolFactors`, `tameChainCond_of_tameSumCond` | 77 |
| [`Step012_tame_symbol_finsupp`](Step012_tame_symbol_finsupp.lean) |  | `cupLC`, `tameLC`, `tameKernelCond`, `tameKernelCond_iff_ker_le` | 87 |
| [`Step013_tame_symbol_factors_closed`](Step013_tame_symbol_factors_closed.lean) |  | `repC`, `repC_spec`, `tameSymbolFactors_of_tameKernelCond` | 113 |
| [`Step014_tame_steinberg_relation`](Step014_tame_steinberg_relation.lean) | `line:739` | `mem_maximalIdeal_iff_not_isUnit`, `isUnit_of_notMem_maximalIdeal`, `notMem_maximalIdeal_of_isUnit`, `toAdd_val_neg_one` (+15 more) | 411 |
| [`Step015_tame_symbol_hyp_from_merkurjev_suslin`](Step015_tame_symbol_hyp_from_merkurjev_suslin.lean) |  | `bilinGen`, `steinbergGen`, `MerkurjevSuslin`, `eq_oneSub_of_add_eq_one` (+7 more) | 344 |
| [`Step016_tame_symbol_hyp_merkurjev_suslin`](Step016_tame_symbol_hyp_merkurjev_suslin.lean) | `line:1050` | `ch4TameSymbolHyp_of_tameSymbolFactors`, `ch4TameSymbolHyp_of_merkurjevSuslin`, `nonempty_henselResidueData_of_merkurjevSuslin` | 118 |
