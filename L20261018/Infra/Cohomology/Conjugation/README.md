# `L20261018/Infra/Cohomology/Conjugation` — sec. 2.3/2.4 · conjugation invariance of H^1(I, mu_p)

14 modules.  Part of the development's [index](../../../README.md); see also [`DECLARATIONS.md`](../../../../DECLARATIONS.md) and [`RENAME-MAP.tsv`](../../../../RENAME-MAP.tsv).

| module | paper | declarations | lines |
|---|---|---|---|
| [`Step001_m_conj_equivariant`](Step001_m_conj_equivariant.lean) |  | `contDeltaZeroBar_conjNormal`, `contDeltaZeroBar_conjNormal_apply` | 68 |
| [`Step002_m_carrier_bridge_beta`](Step002_m_carrier_bridge_beta.lean) |  | `conjNormal_coe_eq_inverseConjugationHom`, `conjNormal_hequiv`, `conjNormalMap_comp_explicitH1`, `contH1_iso_conjNormal` (+1 more) | 132 |
| [`Step003_m_body_complete`](Step003_m_body_complete.lean) |  | `degreeZeroClass_congr`, `conjNormalMap_degreeZeroClass`, `explicitH0Iso_conjNormalMap_zero`, `contM` (+2 more) | 143 |
| [`Step004_gamma_scalar_action`](Step004_gamma_scalar_action.lean) |  | `h1_smul_eq_self_of_mem`, `instSMulQuotientH1`, `quotient_smul_mk` | 86 |
| [`Step005_gamma_complete`](Step005_gamma_complete.lean) |  | `conjEndH1`, `conjEndQuot`, `conjEndQuot_apply`, `instDistribMulActionQuotientH1` (+2 more) | 129 |
| [`Step006_conj_trivial_one_element`](Step006_conj_trivial_one_element.lean) |  | `conj1_eq_of_fixes_zmultiples_top` | 58 |
| [`Step007_conj_trivial_unconditional`](Step007_conj_trivial_unconditional.lean) |  | `zmultiples_eq_top_of_natCard_prime`, `conj1_eq_of_ne_zero` | 99 |
| [`Step008_conj1_trivial_hyp`](Step008_conj1_trivial_hyp.lean) |  | `Conj1Trivial`, `witness_nonempty`, `conj1Trivial_apply`, `conj1Trivial_of_ne_zero` | 123 |
| [`Step009_h_conj1_carrier_inputs`](Step009_h_conj1_carrier_inputs.lean) |  | `galois_fixes_rootsOfUnity_of_hasEnough`, `inertiaLoc_fixes_pow_eq_one` | 92 |
| [`Step010_h_conj1_implies_f5`](Step010_h_conj1_implies_f5.lean) |  | `quotient_smul_eq_self`, `h1InertiaAddEquiv`, `coeffChangeEquiv` | 114 |
| [`Step011_h_conj1_tauceti_interface`](Step011_h_conj1_tauceti_interface.lean) |  | `conjInvariants_eq_top_of_conj1Trivial`, `conj1Trivial_of_conjInvariants_eq_top`, `conj1Trivial_iff_conjInvariants_eq_top` | 75 |
| [`Step012_h_conj1_entry`](Step012_h_conj1_entry.lean) |  | `transport_apply`, `inertiaEquivInertiaLoc_coe`, `subgroupMap_conjNormal`, `inertiaEquivInertiaLoc_conj` (+2 more) | 167 |
| [`Step013_h_conj1_discharged`](Step013_h_conj1_discharged.lean) |  | `conj1Trivial_of_tameChar`, `conj1Trivial_of_tameChar`, `conjInvariants_eq_top`, `coeffChangeEquiv_uncond` | 127 |
| [`Step014_f5_landing`](Step014_f5_landing.lean) |  | `h1ToVEquiv_infl_valLinOf_eq_zero`, `inflToVAddHom`, `inflToVKG`, `F5_uncond` | 142 |
