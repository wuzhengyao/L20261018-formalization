import L20261018.Hyp5
import TauCeti.RepresentationTheory.Homological.ContCohomology.H2ZMod

/-!
# 3.6 的有限性（一）：`K₂` 与商群（R917）

论文 `thm:dimension` 说「`κ`、`τ` 均有限」：`κ = dim K₂` 由 `H²(G, μ_p)` 有限维给出
（`prop:elementary-cohomology`），而 `τ = dim Ĥ⁰(G,M)` 由第一条 SES ＋ `d_F < ∞`。
本文件做**第一半**：`K₂` 的有限性。

链条（全部走 `Finite` 而非维数）：
* `[FiniteDimensional K E]` ⟹ `E.fixingSubgroup.FiniteIndex`
  （`IntermediateField.finrank_eq_fixingSubgroup_index`），进而 **`Finite (G ⧸ N₀)`**
  （库内无单独引理名：`Finite (G ⧸ H)` 是**实例**，`[H.FiniteIndex]` 直接 `inferInstance`；
  `QuotientGroup.finite` 只覆盖 `[Finite G]` 的情形）；
* 系数 `↥(FixedPoints N₀ (ZMod p))` 是 `ZMod p` 的子类型 ⟹ `Finite`；
* `Z2 G' M` 是 `(G' × G' → M)` 的子类型 ⟹ `Finite`；`H2` 是它的商 ⟹ `Finite`；
* `K₂ ⊆ H2` ⟹ `Finite ↥K₂` ⟹ `Module.Finite (ZMod p) ↥K₂`（`Module.Finite.of_finite`）。

## 主结果

* `finite_quotient_fixingSubgroup`／`finite_K2`
* **`moduleFinite_K2`**：`Module.Finite (ZMod p) ↥(K₂)` —— `A.theorem_3_6` 的 `[Module.Finite k K2]`。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Finiteness36

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

/-- `[E : K] < ∞ ⟹ N₀ = Gal(Kˢ/E) 有限指数`（`Hyp4` 的 `corN` 内的同一步）。 -/
theorem fixingSubgroup_finiteIndex (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] : E.fixingSubgroup.FiniteIndex := by
  rw [Subgroup.finiteIndex_iff,
    ← IntermediateField.finrank_eq_fixingSubgroup_index (E' := SeparableClosure K) E]
  exact Module.finrank_pos.ne'

/-- **`Gal(Kˢ/E)` 的商群有限**（`G ⧸ N₀`，即 Galois 群层）。 -/
theorem finite_quotient_fixingSubgroup (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] : Finite ((AbsoluteGaloisGroup K) ⧸ E.fixingSubgroup) := by
  haveI := fixingSubgroup_finiteIndex (K := K) E
  infer_instance

/-- **`K₂ = ker(inf)` 有限**：`G ⧸ N₀` 有限 ＋ 系数是 `ZMod p` 的子类型。 -/
theorem finite_K2 (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    [IsGalois K E] : Finite ↥(GaloFive.K2 K p E) := by
  haveI := finite_quotient_fixingSubgroup (K := K) E
  haveI : Finite ↥(FixedPoints.addSubgroup (↥E.fixingSubgroup) (ZMod p)) := Subtype.finite
  haveI : Finite (Z2 ((AbsoluteGaloisGroup K) ⧸ E.fixingSubgroup)
      ↥(FixedPoints.addSubgroup (↥E.fixingSubgroup) (ZMod p))) := Subtype.finite
  haveI : Finite (H2 ((AbsoluteGaloisGroup K) ⧸ E.fixingSubgroup)
      ↥(FixedPoints.addSubgroup (↥E.fixingSubgroup) (ZMod p))) := Quotient.finite _
  infer_instance

/-- **`Module.Finite (ZMod p) ↥K₂`** —— `A.theorem_3_6` 的 `[Module.Finite k K2]` 前提。 -/
theorem moduleFinite_K2 (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    [IsGalois K E] : Module.Finite (ZMod p) ↥(GaloFive.K2 K p E) := by
  haveI := finite_K2 (K := K) (p := p) E
  exact Module.Finite.of_finite

end Finiteness36

#print axioms Finiteness36.finite_quotient_fixingSubgroup
#print axioms Finiteness36.finite_K2
#print axioms Finiteness36.moduleFinite_K2
