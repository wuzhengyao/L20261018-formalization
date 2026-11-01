import Hyp719
import Hyp578

/-!
# S64 R11：**C2-F 在战役载体上已有机检件**（`Hyp576`／`Hyp578`）—— 本件补最后一块接口

**重大侦察发现（`L47`④ 的教科书案例）**：`S62-COEFF-PLAN.md` §4.4 把 `C2-F`
（`C^H → H¹(H,A)` 的 `G⧸H`-等变性）列为「未开工」，但**战役在 S47 R6 就做完了**：
* `Hyp576.contM` ＝ `Cᴵ → H¹(I, μ_p)`（显式载体，`= h1⁻¹ ∘ δ₀ ∘ h0`）；
* `Hyp576.contM_smul`（`Γ`-级）／**`Hyp578.contM_quotient_smul`（`Γ⧸I`-级，★★★★★）**；
* `Hyp577/578` 给了靶侧 `DistribMulAction (G⧸N) (H1 ↥N M)`（`instDistribMulActionQuotientH1`）。

本件把 `contM` 从**裸函数**升成 `explicitCoeff1` 所需的 `→+[Γ⧸I]`，从而 C2-F **完全落地**：

| 声明 | 内容 |
|---|---|
| `contM_add` / `contM_zero` | `contM` 的加性（三段桥分别是 `AddEquiv`／同态／同态的 `.hom`） |
| **`contMHom`** | ★★★★★ `contInvC →+[Γ ⧸ I] H1 ↥I (ZMod p)` |
| **`contM_coeffMap`** | ★★★★★ `H1 (Γ⧸I) (Cᴵ) →+ H1 (Γ⧸I) (H¹(I,μ_p))`（`explicitCoeff1`） |

**单条显式假设**：`[ContinuousSMul (Γ⧸I) (H1 ↥I (ZMod p))]` —— 即"靶侧商作用连续"，
对 `A = μ_p` 由 `H¹(I,μ_p)` 的**有限性**（库内 `Hyp520`／`Hyp521`：`≅ ℤ/p`）兑现；
`Hyp498` 所说的循环已随之解除（有限性已机检，不再是待证项）。

## 导入前提（R11 的三处改名，均已机检通过）

`import Hyp719` ＋ `import Hyp578` 原**冲突**三次：`Hyp713` 的两个 `local instance`
（`trivialActionZModInertiaLoc'`／`trivialContinuousSMulInertiaLoc'` 与 `Hyp518` 同名 ⟹ 改名加 `I` 后缀）
与 `Hyp719.deltaTwo`（与 `Hyp239` 同名 ⟹ 改名 `deltaTwoShift`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal] [CompactSpace ↥I]

/-- `contM` 保加法（`= h1⁻¹ ∘ δ₀ ∘ h0`，三段都保加法）。 -/
theorem contM_add (x y : contInvC (F := F) p I) :
    contM (F := F) p I (x + y) = contM (F := F) p I x + contM (F := F) p I y := by
  simp only [contM, map_add]

/-- `contM` 保零。 -/
theorem contM_zero : contM (F := F) p I (0 : contInvC (F := F) p I) = 0 := by
  simp only [contM, map_zero]

/-- ★★★★★ **`contM` 作为 `Γ⧸I`-等变加性映射**（`explicitCoeff1` 的输入形状）。 -/
noncomputable def contMHom : contInvC (F := F) p I →+[AbsoluteGaloisGroup F ⧸ I] H1 ↥I (ZMod p) where
  toFun := contM (F := F) p I
  map_zero' := contM_zero (F := F) p I
  map_add' := contM_add (F := F) p I
  map_smul' := contM_quotient_smul (F := F) p I

/-- ★★★★★ **C2-F 落地**：系数映射 `H¹(Γ⧸I, Cᴵ) →+ H¹(Γ⧸I, H¹(I,μ_p))`。 -/
noncomputable def contM_coeffMap
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ I) (H1 ↥I (ZMod p))] :
    H1 (AbsoluteGaloisGroup F ⧸ I) (contInvC (F := F) p I) →+
      H1 (AbsoluteGaloisGroup F ⧸ I) (H1 ↥I (ZMod p)) :=
  explicitCoeff1 (G := AbsoluteGaloisGroup F ⧸ I) (M := contInvC (F := F) p I)
    (N := H1 ↥I (ZMod p)) (contMHom (F := F) p I) continuous_of_discreteTopology

end L20261018

#print axioms L20261018.contM_add
#print axioms L20261018.contM_zero
#print axioms L20261018.contMHom
#print axioms L20261018.contM_coeffMap
