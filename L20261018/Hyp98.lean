import L20261018.Hyp97
/-!
# 3.6 组装（一）：商上的 `ZMod p`-模结构 ＋ 第一条 SES 的线性化（R924）

`A.theorem_3_6` 要 `φ : V ⧸ (U+N) →ₗ H0`、`ψ : H0 →ₗ K2`，而 `GaloFive.theorem_3_5_1_galo`
给的是 `→+`。两个障碍，本轮**都用"p-挠性 + zmodModule"这一条模板**解决：

1. **商上的模结构**：`AddSubgroup` 的商（`V ⧸ A`、`↥MG ⧸ NG`）在库内没有 `Module` 实例；
   但它们是 `p`-挠的（`p • x = 0` 由 `V`／`↥MG` 的 `p`-挠性），故
   `AddCommGroup.zmodModule` 直接给出（`addSubgroupQuotientModule`）。
2. **`→+` → `→ₗ`**：`ZMod p` 是域 ⟹ 纯量即 `nsmul` ⟹ 任何加性同态都线性
   （`addMonoidHom_map_zmod_smul`，R912 已有）。

## 主结果

* `addSubgroupQuotientModule`：`Module (ZMod p) (M ⧸ A)`（任意 `p`-挠 `ZMod p`-模 `M`）。

**注意**：`→+` → `→ₗ` 的转换器本轮**未落成**（`LinearMap.map_smul'` 的纯量写法与
`Nat.cast_smul_eq_nsmul` 的目标形状不合）——下一轮直接用 `Hyp92` 的
`addMonoidHom_map_zmod_smul`（它就是 `map_smul'`，需 `import Hyp92`），见 ASSUMPTIONS 第 125 轮。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Assemble36

variable {p : ℕ} [NeZero p]

/-- **`AddSubgroup` 商的 `ZMod p`-模结构**（`M` 是 `p`-挠 `ZMod p`-模时）。

库内没有这条实例（`AddSubgroup` 的商按 `QuotientAddGroup` 定义，不带 `Module`），
但 `p • x = 0` 在商上成立 ⟹ `AddCommGroup.zmodModule`。 -/
noncomputable instance addSubgroupQuotientModule {M : Type*} [AddCommGroup M]
    [Module (ZMod p) M] (A : AddSubgroup M) : Module (ZMod p) (M ⧸ A) :=
  AddCommGroup.zmodModule (fun x => by
    induction x using QuotientAddGroup.induction_on with
    | H v =>
      rw [← QuotientAddGroup.mk_nsmul]
      have h : p • v = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (R := ZMod p), ZMod.natCast_self, zero_smul]
      rw [h, QuotientAddGroup.mk_zero])

end Assemble36

#print axioms Assemble36.addSubgroupQuotientModule
