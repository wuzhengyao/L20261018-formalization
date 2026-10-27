import L20261018.Hyp96
/-!
# 3.6 的载体：`K₂` 升成子模（R922）

与 `MG`／`NG`（R921）同型的问题：`K₂` 是 `AddSubgroup (H2 (G⧸N₀) ↥(FixedPoints …))`，
`AddSubgroup` 上不会自动有 `Module` 实例。绕法一致：**不碰系数的子群作用实例**，
用 `p`-挠性直接 `AddCommGroup.zmodModule`：

1. 系数 `↥(FixedPoints N₀ (ZMod p))` 是 `ZMod p` 的子类型 ⟹ `p • y = 0` ⟹ `Module`；
2. `H2 (G⧸N₀) M` 因此可经 `instModuleZModH2`（R912 已移植）成模；
3. `K₂` 由此升成 `Submodule`。

## 主结果

* `moduleFixedPoints`／`moduleH2`；
* `K2sub`：`K₂` 的子模版（载体不变）；
* `module_K2`：`Module (ZMod p) ↥K2sub`。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Finiteness36

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]

/-- **不变量系数是 `ZMod p`-模**（`p`-挠性；`↥(FixedPoints …)` 是 `ZMod p` 的子类型）。 -/
noncomputable instance moduleFixedPoints :
    Module (ZMod p) ↥(FixedPoints.addSubgroup (↥E.fixingSubgroup) (ZMod p)) :=
  AddCommGroup.zmodModule (fun y => by
    refine Subtype.ext ?_
    show p • (y : ZMod p) = 0
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod p), CharP.cast_eq_zero (ZMod p) p, zero_smul])

/-- **`H²(G⧸N₀, M)` 是 `ZMod p`-模**（`instModuleZModH2` ＋ 上一条）。 -/
noncomputable instance moduleH2 :
    Module (ZMod p) (H2 ((AbsoluteGaloisGroup K) ⧸ E.fixingSubgroup)
      ↥(FixedPoints.addSubgroup (↥E.fixingSubgroup) (ZMod p))) :=
  instModuleZModH2

/-- **`K₂ = ker(inf)` 的子模版**（载体不变）。 -/
noncomputable def K2sub : Submodule (ZMod p) (H2 ((AbsoluteGaloisGroup K) ⧸ E.fixingSubgroup)
    ↥(FixedPoints.addSubgroup (↥E.fixingSubgroup) (ZMod p))) where
  __ := GaloFive.K2 K p E
  smul_mem' c x hx := by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact (GaloFive.K2 K p E).nsmul_mem hx c.val

/-- **`K₂` 是 `ZMod p`-模**（`A.theorem_3_6` 的 `[Module k K2]`）。 -/
noncomputable def module_K2 : Module (ZMod p) ↥(K2sub (K := K) (p := p) E) :=
  inferInstance

/-- **`K₂` 有限**（升级版；`A.theorem_3_6` 的 `[Module.Finite k K2]`）。 -/
theorem moduleFinite_K2' :
    Module.Finite (ZMod p) ↥(K2sub (K := K) (p := p) E) := by
  haveI : Finite ↥(K2sub (K := K) (p := p) E) := finite_K2 (K := K) (p := p) E
  exact Module.Finite.of_finite

end Finiteness36

#print axioms Finiteness36.module_K2
#print axioms Finiteness36.moduleFinite_K2'
