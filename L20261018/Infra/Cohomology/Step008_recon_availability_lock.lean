import L20261018.Ch2.Hensel.ResidueMap.Step044_residue_map_unramified_units

/-!
# S40 R10：**外部/库内侦察的可用性锁定** —— 更正 `RECON-R3` §87.4 的「库内均无」

## 本件为什么存在

`RECON-R3` §87.4 与 `S40-FINAL-STATUS` §19.4 曾写「系数识别 `H²(G,K_nr^×) ≅ Br(F)`
**本仓与 TauCeti 均无**」。按规则 23（L46，外部侦察常态化）＋ 规则 24（L47，库内已有优先于自建）
做内容式侦察后，这句话**对其中两个最关键部件是错的**：

| 部件 | 实况 |
|---|---|
| `Br(K) ≅ H²(G_K, K_s^×)` | ✅ **`TauCeti.brauerCohomologyEquiv`**（一般，**不是**只 2-挠） |
| Kummer 桥 `H²(G,μ_n) ↪ H²(G,K_s^×)`，像 = `n`-挠 | ✅ **`TauCeti.h2KummerToUnits_injective` ＋ `_range`**（一般 `n`，需 `IsUnit (n:K)`） |
| 战役侧 `H2 F p` 的系数是**平凡** `Z/p` | ✅ `GaloBase.muP_ρ : ρ g x = x := rfl`（因 `char K ≠ p` ⟹ `χ = 1`，见 `Hyp451.chi_eq_one`） |

本件把这三条**机检锚定**（`Nonempty`／`Function.Injective`／`↔`），使后续轮次不必再"凭记忆相信库里有"。

## 本件不声称什么

* **不**声称系数识别已完成 —— 见 `RECON-R3` §88 的分件表：
  `H²(Gal(K_nr/F), K_nr^×) ≅ Br(F)`（inflation 同构，需 `Br(K_nr) = 0`）、
  `μ_p ≅ trivial Z/p` 的一般 `p` 版（库内只有 `n = 2` 的 `kummerCoeffIsoTrivialF2`）、
  cup／inflation 相容 —— **这三件仍未形式化**。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {K : Type} [Field K]

/-- ★★★★ **可用性锁定：`Br(K) ≅ H²(G_K, K_s^×)`（一般，非只 2-挠）**。
出处 `TauCeti.brauerCohomologyEquiv`（`raw/TauCeti/TauCeti/Algebra/CrossedProduct/Comparison.lean:267`）。 -/
theorem brauer_h2_equiv_available :
    Nonempty (Additive (BrauerGroup K) ≃+
      ↑(continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K)
        (UnitsCoeff K))).toModuleCat) :=
  ⟨TauCeti.brauerCohomologyEquiv K⟩

/-- ★★★★ **可用性锁定：Kummer 桥单射（一般 `n`，`n ∈ K^×`）**。
出处 `TauCeti.h2KummerToUnits_injective`。 -/
theorem kummer_injective_available {n : ℕ} (hn : IsUnit (n : K)) :
    Function.Injective ⇑(TopModuleCat.Hom.hom (TauCeti.h2KummerToUnits K n)) :=
  TauCeti.h2KummerToUnits_injective hn

/-- ★★★★★ **可用性锁定：Kummer 桥的像 = `n`-挠**。
出处 `TauCeti.h2KummerToUnits_range`。 -/
theorem kummer_range_available {n : ℕ} (hn : IsUnit (n : K))
    (x : ↑(continuousCohomology 2 (ofDiscreteModule ℤ (AbsoluteGaloisGroup K)
      (UnitsCoeff K))).toModuleCat) :
    (∃ y, (TopModuleCat.Hom.hom (TauCeti.h2KummerToUnits K n)) y = x) ↔ n • x = 0 :=
  TauCeti.h2KummerToUnits_range hn x

/-- ★★★★ **可用性锁定：战役侧的 `H2 F p` 用**平凡**系数**（`char K ≠ p` ⟹ 分圆特征 = 1）。
出处 `GaloBase.muP_ρ`（`rfl`）。 -/
theorem muP_trivial_available (p : ℕ) [Fact (Nat.Prime p)] :
    ∀ (g : TauCeti.AbsoluteGaloisGroup K) (x : (GaloBase.muP K p).V),
      (GaloBase.muP K p).ρ g x = x :=
  fun g x => GaloBase.muP_ρ (K := K) (p := p) g x

end L20261018

#print axioms L20261018.brauer_h2_equiv_available
#print axioms L20261018.kummer_injective_available
#print axioms L20261018.kummer_range_available
#print axioms L20261018.muP_trivial_available
