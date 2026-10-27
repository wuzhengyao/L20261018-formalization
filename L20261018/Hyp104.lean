import L20261018.Hyp103
/-!
# 3.6 组装（七）：`Ĥ⁰`／`K₂` 的短名（R930）

最终装配的语句若写全 `↥(MGsub …) ⧸ NGsub …` 会到 40+ 行（R929 的失败根因）。
本文件给两个 `abbrev` 短名（`abbrev` 是 **reducible**，故实例搜索会展开它们，
`def` 不行）＋ 对它们的模结构／有限性重述。

## 主结果

* `H0ex`／`K2ex`：`Ĥ⁰(G,M)`／`K₂` 的载体短名；
* `moduleH0ex`／`moduleFinite_H0ex`／`moduleFinite_K2ex`。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Assemble36

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

/-- `Ĥ⁰(G,M) = M^G/N_G(M)` 的载体（短名）。 -/
noncomputable abbrev H0ex (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E] : Type :=
  ↥(Finiteness36.MGsub (K := K) (p := p) E) ⧸ Finiteness36.NGsub (K := K) (p := p) E

/-- `K₂ = ker(inf)` 的载体（短名）。 -/
noncomputable abbrev K2ex (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E] : Type :=
  ↥(Finiteness36.K2sub (K := K) (p := p) E)

/-- `H0ex` 的 `ZMod p`-模结构。 -/
noncomputable def moduleH0ex (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E] : Module (ZMod p) (H0ex (K := K) (p := p) E) :=
  Finiteness36.module_H0 (K := K) (p := p) E

/-- `H0ex` 有限。 -/
theorem moduleFinite_H0ex (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E] [Finite (H1 (AbsoluteGaloisGroup K) (ZMod p))] :
    Module.Finite (ZMod p) (H0ex (K := K) (p := p) E) :=
  Finiteness36.moduleFinite_H0' (K := K) (p := p) E

/-- `K2ex` 有限。 -/
theorem moduleFinite_K2ex (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E] :
    Module.Finite (ZMod p) (K2ex (K := K) (p := p) E) :=
  Finiteness36.moduleFinite_K2' (K := K) (p := p) E

end Assemble36

#print axioms Assemble36.moduleFinite_H0ex
#print axioms Assemble36.moduleFinite_K2ex
