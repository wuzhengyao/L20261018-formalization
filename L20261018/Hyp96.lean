import L20261018.Hyp95
/-!
# 3.6 的载体：`H¹(↥N₀)` 的 `ZMod p`-模结构 ＋ `MG`／`NG` 升子模（R921）

**R919／R920 的两层根因**（已登记）：`MG ⊆ H¹(↥N₀, ZMod p)`，而 `↥N₀` 上**不能**照 `Hyp4` 的写法
补系数作用实例（本 pin 的 `DistribMulAction` 含 `smul` 字段：单给不够，加 `SMul` 又成钻石）。

**绕法**：完全不碰系数作用实例，改用 `H¹` 的 `p`-挠性直接造模结构
（与 `instModuleZModH1`／`instModuleZModH2` 同一手法）：`p • x = 0` ⟹ `AddCommGroup.zmodModule`。
关键是它**声明成 `instance`**（`E` 由目标类型推出）——放 `letI` 进证明体太晚（语句层就要实例）。

## 主结果

* `nsmul_H1_fixingSubgroup`／`moduleH1fixing`（**instance**）；
* `MGsub`／`NGsub`：`MG`／`NG` 的子模版（载体不变）；
* `moduleFinite_H0'`：`Module.Finite (ZMod p) (↥MGsub ⧸ NGsub)`。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Finiteness36

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

/-- `H¹(↥N₀, ZMod p)` 是 `p`-挠的。 -/
theorem nsmul_H1_fixingSubgroup (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E]
    (x : H1 (↥E.fixingSubgroup) (ZMod p)) : p • x = 0 :=
  nsmul_H1_eq_zero (fun m : ZMod p => by
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod p), CharP.cast_eq_zero (ZMod p) p, zero_smul]) x

/-- **`H¹(↥N₀, ZMod p)` 的 `ZMod p`-模结构**（经 `p`-挠性，不碰系数作用实例）。 -/
noncomputable instance moduleH1fixing (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E] :
    Module (ZMod p) (H1 (↥E.fixingSubgroup) (ZMod p)) :=
  AddCommGroup.zmodModule (nsmul_H1_fixingSubgroup (K := K) (p := p) E)

/-- **`MG = H¹(G_E, μ_p)^{G_F}` 的子模版**（载体不变）。 -/
noncomputable def MGsub (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    [IsGalois K E] : Submodule (ZMod p) (H1 (↥E.fixingSubgroup) (ZMod p)) where
  __ := GaloFive.MG K p E
  smul_mem' c x hx := by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact (GaloFive.MG K p E).nsmul_mem hx c.val

/-- **`NG = res(N)` 的子模版**（载体不变）。 -/
noncomputable def NGsub (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    [IsGalois K E] : Submodule (ZMod p) ↥(MGsub (K := K) (p := p) E) where
  __ := GaloFive.NG K p E
  smul_mem' c x hx := by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact (GaloFive.NG K p E).nsmul_mem hx c.val

/-- **`Ĥ⁰` 的载体是 `ZMod p`-模**（`MGsub`／`NGsub` 的直接后果）——
这正是 R918／R919 卡住的那一个实例，现在**不再是缺口**。 -/
noncomputable def module_H0 (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E] :
    Module (ZMod p) (↥(MGsub (K := K) (p := p) E) ⧸ NGsub (K := K) (p := p) E) :=
  inferInstance

/-- **`Ĥ⁰` 升级版有限**（`A.theorem_3_6` 的 `[Module.Finite k H0]`）。

R921 曾误判"`AddSubgroup` 商与 `Submodule` 商不 defeq"——**实测是 defeq**（`rfl` 过），
当时的失败只是 `haveI h := …` 把 `Finite` 注册在**旧写法**的类型上。
**修法：显式注明类型**（`haveI : Finite (↥MGsub ⧸ NGsub) := finite_H0 …`）。 -/
theorem moduleFinite_H0' (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    [IsGalois K E] [Finite (H1 (AbsoluteGaloisGroup K) (ZMod p))] :
    Module.Finite (ZMod p) (↥(MGsub (K := K) (p := p) E) ⧸ NGsub (K := K) (p := p) E) := by
  haveI : Finite (↥(MGsub (K := K) (p := p) E) ⧸ NGsub (K := K) (p := p) E) :=
    finite_H0 (K := K) (p := p) E
  exact Module.Finite.of_finite

end Finiteness36

#print axioms Finiteness36.nsmul_H1_fixingSubgroup
#print axioms Finiteness36.moduleFinite_H0'
