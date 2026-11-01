import L20261018.Hyp128

/-!
# R972：路线 B 的收尾正规形 —— `muNRep` 的 `OfDiscrete` 比较 = 换标量 ∘ 显式比较

R971（`Hyp128`）把**路线 A** 的收尾化到 `muP` 的 `OfDiscrete` 比较；本轮把**路线 B** 的收尾
（`muNRep` 的 `OfDiscrete` 比较，即 `muNRepH1Equiv` 的最后一段）化到同一形状：

    (muNRep p F).explicitH1AddEquivContinuousCohomologyOfDiscrete x
      = restrictScalarsIntEquiv (muNRep p F) 1
          (explicitH1AddEquivContinuousCohomology G' (muNRep p F).V x)

底层仍是同一件事：`TopRep.ofDiscreteModule ℤ G X.V` 与 `TopRep.restrictScalarsInt.obj X`
**定义相等**，故 `ofDiscreteModuleRestrictScalarsIntEquiv` 里那个 `eqToHom` 在元素上是恒等
（收尾一步 `rfl`）。

**为何不写成「任意离散 `TopRep`」的一般形式**（本轮实测）：`muP`／`muNRep` 上
`ofDiscreteModule ℤ G X.V` 与 `restrictScalarsInt.obj X` 是**定义相等**，故等式可直接陈述；
但对**任意** `X`，Lean 在**陈述层**就拒绝合一（`restrictScalarsIntEquiv X 1` 的定义域是
`continuousCohomology 1 (restrictScalarsInt.obj X)`，与 `continuousCohomology 1 (ofDiscreteModule ℤ G X.V)`
不是同一表达式）——`TopRep` 携带的实例数据使「一般相等」只能以
`ofDiscreteModule_eq_restrictScalarsInt_obj` 为前提陈述。故本战役**逐载体**证
（`muP` 在 `Hyp128`，`muNRep` 在本文件）。
-/

set_option maxHeartbeats 2000000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p]

-- `X.V` 上的 `DistribMulAction` 来自 `X.ρ`；TauCeti 惯用局部实例（`MuNRep.lean` 同款）。
attribute [local instance] TopRep.distribMulAction

/-- **路线 B 的收尾正规形**：`muNRep` 的 `OfDiscrete` 比较就是「换标量 ∘ 显式 `H¹` 比较」。

与 `Hyp128.muP_explicitH1_eq_restrictScalars` 同构型、同证法（`2 rw ＋ rfl`），
是路线 B 侧与路线 A 侧对齐的最后一块载体拼图。 -/
theorem muNRep_explicitH1_eq_restrictScalars
    (x : H1 (Field.absoluteGaloisGroup F) (ClassFieldTheory.muNRep p F).V) :
    (ClassFieldTheory.muNRep p F).explicitH1AddEquivContinuousCohomologyOfDiscrete x
      = TauCeti.ContCohomology.restrictScalarsIntEquiv (ClassFieldTheory.muNRep p F) 1
          (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology
            (Field.absoluteGaloisGroup F) (ClassFieldTheory.muNRep p F).V x) := by
  rw [TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_apply,
    TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv_apply]
  rfl

end L20261018
#print axioms L20261018.muNRep_explicitH1_eq_restrictScalars
