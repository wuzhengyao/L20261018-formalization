import Hyp161

/-!
# S59 R1：**驯符号的显式化 ＋ `(R2)` 严格弱于 `residueSpan = ⊥`**（`Hyp680`）

## 本轮的起点（`D20`／`L47`④：缺口清单用 `grep` 重生成，不继承上一轮提示词）

`PROMPT-S59` §① 把「给 `HenselResidueData` 造载体模型」当作本轮靶子。**扫描后判定：
该靶子早已完成**，且是**同一数学内容的第三种表述**：

| 件 | 声明 | 读数 |
|---|---|---|
| `Hyp161.nonempty_henselResidueData_iff` | `(∃ D, D.val = val) ⟺ TameResidueFacts` | 已在（R1013） |
| `Hyp161.henselResidueDataOfFacts` | `TameResidueFacts ⟹ D`（`VK := ker v̄`） | 已在 |
| `Hyp321.exists_henselResidueData_noBridge` | `∃ D`，**无 `hbridge`**（`[Finite (ResidueField)]` 下） | 已在（R1226） |
| `Hyp323.exists_henselResidueData_uncond_noBridge'` | `∃ D`，**`hskew` 也消去** | 已在（R1228） |

⟹ 「给 `D` 造模型」＝ `(R1) ＋ (R2)`，**不是**独立缺口（`D19` 的又一实例）。

## 本轮的实际交付：把 `(R2)` 的**判别式**精确到一层

**关键结构发现（本件的 §2 ＋ §3）**：`D` 的 11 个字段中 `res` 的全部内容压缩成**一条等式**

```
    res ∘ ∪  =  tame        （tame a b := [v̄(b)·a − v̄(a)·b] ∈ ker v̄）
```

* `tame` **不需要 `π`**：`v̄(b)·(a − v̄(a)π) − v̄(a)·(b − v̄(b)π) = v̄(b)·a − v̄(a)·b`，
  `π` 项相消。故 `tame` 是**规范**的（`tameExpr`，无选取）。
* 论文侧的身份：这正是 `eq:prelim-tame`（`raw/L20261018.tex:1027`）在 `p` 奇时的
  **加法（Kummer）写法**——论文自己指出 `(-1)^{v(a)v(b)}` 在 `K^×/K^{×p}` 中是零类。
* `TameSymbolFactors cup val ⟺ TameResidueFacts cup val π`（**§2，双向机检**）。
  ⟹ 审计 §3 偏差 ②（「`res` 是 `Classical.choice` 的左逆，与 `∂₂` 的同一性未证」）
  以**唯一可能的形式**关闭：`res` 的值公式**唯一确定**它，`D` 就是「驯符号下降到 `∪`」。

## `(R2)` **严格弱于** `residueSpan = ⊥`（§3 反模型，本轮最值钱的一格）

战役六档（`PROOF-MAP` §1）**全部**经 `residueSpan = ⊥` ⟹ 需要 `hUU`／`unitsCupVanish`。
本件机检一个**反模型**：`∃ cup val π, TameResidueFacts cup val π ∧ residueSpan cup val ≠ ⊥`
（`ℚ³` 上的叉积 `∪`，`ker v̄ = ⟨e₀,e₁⟩`，`residueSpan = ⟨e₂⟩`）。

⟹ **`residueSpan = ⊥` 是充分而非必要**：它是「无限残域」情形被判死的**唯一**原因
（`[Finite (ResidueField)]` ⟹ `κ^×` 循环 ⟹ `unitsCupVanish`，`Hyp302`），
而 `(R2)` 在无限残域下**不必**经 Tsen／`hκ`——只需「驯符号下降到 `∪`」（Hilbert 90／`K₂` 符号性）。
本件不证后者（`∅-open`），但把它的**形状**钉死为一条等式，且证明六档路线**不能**覆盖它。

## 机检件

| 声明 | 内容 |
|---|---|
| **`tameExpr`** | ★ 驯符号 `(a,b) ↦ v̄(b)·a − v̄(a)·b`（落 `ker v̄`，**无 `π`**） |
| `tameExpr_uu`／`tameExpr_u_pi`／`tameExpr_pi_u`／`tameExpr_pi_pi`／`tameExpr_skew` | 论文 `:1050` 三条值公式 ＋ 退化 ＋ 斜对称 |
| **`TameSymbolFactors`** | ★ 谓词：`∃ res, res ∘ ∪ = tame` |
| **`tameSymbolFactors_iff`** | ★★★ `TameSymbolFactors ⟺ TameResidueFacts`（双向） |
| **`nonempty_henselResidueData_iff_tameSymbolFactors`** | ★★★ `(∃D, D.val = val) ⟺ TameSymbolFactors` |
| **`exists_tameResidueFacts_of_residueSpan_ne_bot`** | ★★★★ **反模型**：`(R2)` 成立而 `residueSpan ≠ ⊥` |

## 诚实边界（三条）

1. **不**证 `TameSymbolFactors`（即不证 `(R2)`）：本件只证它与既有缺口形态**等价**，
   并把「六档路线」与它**分开**（反模型）。
2. 反模型是**抽象**（任意双线性 `∪`）：它证明「`TameResidueFacts ⟹ residueSpan = ⊥` 不成立」，
   **不**证明「真实载体上 `(R2)` 无需 Tsen」。后者需 `Hilbert 90／Steinitz` 层的下降（`∅-open`）。
3. 不增 CH4 覆盖率（CH4 = 9/9 陈述层已闭）；本件属 `(R2)` 的**精确化**。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section TameSymbol

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- 驯符号：`(a,b) ↦ v̄(b)·a − v̄(a)·b`，落在 `ker v̄` 里（`⟨π⟩` 方向已被消去）。

论文 `eq:prelim-tame` 的`(-1)^{v(a)v(b)}` 因子在 `p` 奇时于 `K^×/K^{×p}` 中为零类
（`raw/L20261018.tex:1044`），故本式就是 `∂₂` 的加法写法。 -/
-- @source file=raw/L20261018.tex locator=label:eq:prelim-tame quote="\partial_2\bigl((a)\cup(b)\bigr)=\left((-1)^{v(a)v(b)}\overline{a^{v(b)}b^{-v(a)}}\right)\quad\text{于 }K^\times/K^{\times p}."
def tameExpr (val : V →ₗ[k] k) (a b : V) : ↥(LinearMap.ker val) :=
  ⟨val b • a - val a • b, by simp [map_sub, mul_comm]⟩

@[simp] theorem tameExpr_coe (val : V →ₗ[k] k) (a b : V) :
    (tameExpr val a b : V) = val b • a - val a • b := rfl

-- @source file=raw/L20261018.tex locator=line:1050 quote="\partial_2((u)\cup(\pi))=(\bar u),\partial_2((\pi)\cup(u))=-(\bar u),\partial_2((u)\cup(w))=0."
theorem tameExpr_uu (val : V →ₗ[k] k) (y z : ↥(LinearMap.ker val)) :
    tameExpr val (y : V) (z : V) = 0 := by
  ext
  simp [tameExpr_coe]

-- @source file=raw/L20261018.tex locator=line:1050 quote="\partial_2((u)\cup(\pi))=(\bar u),\partial_2((\pi)\cup(u))=-(\bar u),\partial_2((u)\cup(w))=0."
theorem tameExpr_u_pi (val : V →ₗ[k] k) (π : V) (hπ : val π = 1)
    (y : ↥(LinearMap.ker val)) : tameExpr val (y : V) π = y := by
  ext
  simp [tameExpr_coe, hπ]

-- @source file=raw/L20261018.tex locator=line:1050 quote="\partial_2((u)\cup(\pi))=(\bar u),\partial_2((\pi)\cup(u))=-(\bar u),\partial_2((u)\cup(w))=0."
theorem tameExpr_pi_u (val : V →ₗ[k] k) (π : V) (hπ : val π = 1)
    (κ : V) (hκ : val κ = 1) (z : ↥(LinearMap.ker val)) :
    tameExpr val κ (z : V) = -z := by
  ext
  simp [tameExpr_coe, hκ]

theorem tameExpr_pi_pi (val : V →ₗ[k] k) (π : V) (hπ : val π = 1) :
    tameExpr val π π = 0 := by
  ext
  simp [tameExpr_coe]

theorem tameExpr_skew (val : V →ₗ[k] k) (a b : V) :
    tameExpr val a b = -tameExpr val b a := by
  ext
  simp only [tameExpr_coe, Submodule.coe_neg]
  abel

/-- ★ **驯符号下降到杯积**：存在 `H²` 上的线性映射，使其与 `∪` 的复合恰是驯符号。 -/
def TameSymbolFactors (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) : Prop :=
  ∃ res : H2 →ₗ[k] ↥(LinearMap.ker val), ∀ a b : V, res (cup a b) = tameExpr val a b

/-! ### 辅助：`Φ` 的收缩给出驯符号 -/

theorem tameExpr_of_res (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (π : V) (hπ : val π = 1) (hskew : ∀ x y, cup x y = -cup y x) (hpp : cup π π = 0)
    (res : H2 →ₗ[k] ↥(LinearMap.ker val))
    (huu : ∀ y z : ↥(LinearMap.ker val), res (cup (y : V) (z : V)) = 0)
    (hupi : ∀ y : ↥(LinearMap.ker val), res (cup (y : V) π) = y)
    (a b : V) : res (cup a b) = tameExpr val a b := by
  set ua : ↥(LinearMap.ker val) := ⟨a - val a • π, by simp [map_sub, hπ]⟩ with hua
  set ub : ↥(LinearMap.ker val) := ⟨b - val b • π, by simp [map_sub, hπ]⟩ with hub
  have ha : a = (ua : V) + val a • π := by rw [hua]; simp
  have hb : b = (ub : V) + val b • π := by rw [hub]; simp
  have hpiu : res (cup π (ub : V)) = -ub := by
    rw [hskew π (ub : V), map_neg, hupi]
  have hexp : res (cup a b) = val b • ua - val a • ub := by
    conv_lhs => rw [ha, hb]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_add]
    rw [huu ua ub, hupi ua, hpiu, hpp, map_zero]
    module
  have hua' : (ua : V) = a - val a • π := by rw [hua]
  have hub' : (ub : V) = b - val b • π := by rw [hub]
  have hkey : val b • (a - val a • π) - val a • (b - val b • π)
      = val b • a - val a • b := by
    rw [smul_sub, smul_sub, smul_smul, smul_smul, mul_comm (val b) (val a)]
    module
  rw [hexp]
  apply Subtype.ext
  rw [tameExpr_coe]
  simp only [Submodule.coe_sub, Submodule.coe_smul]
  rw [hua', hub']
  exact hkey

/-! ### 主等价 -/

theorem tameResidueFacts_of_tameSymbolFactors (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (π : V) (hπ : val π = 1) (h : TameSymbolFactors cup val) :
    TameResidueFacts cup val π := by
  obtain ⟨res, hres⟩ := h
  have hker : residueSpan cup val ≤ LinearMap.ker res := by
    rw [residueSpan, Submodule.span_le]
    rintro _ ⟨⟨y, z⟩, rfl⟩
    show res (cup (y : V) (z : V)) = 0
    rw [hres]
    exact tameExpr_uu val y z
  refine ⟨?_, ?_⟩
  · intro y z hyz
    have h1 : res (residuePhi cup val π y) = res (residuePhi cup val π z) := by rw [hyz]
    rw [residuePhi_apply, hres, residuePhi_apply, hres] at h1
    rw [tameExpr_u_pi val π hπ, tameExpr_u_pi val π hπ] at h1
    exact h1
  · rw [disjoint_iff_inf_le]
    intro w hw
    obtain ⟨hwr, hws⟩ := Submodule.mem_inf.mp hw
    obtain ⟨y, rfl⟩ := hwr
    have hzero : res (residuePhi cup val π y) = 0 := hker hws
    rw [residuePhi_apply, hres, tameExpr_u_pi val π hπ] at hzero
    rw [Submodule.mem_bot, show residuePhi cup val π y = 0 by
      rw [show y = 0 from hzero, map_zero]]

theorem tameSymbolFactors_of_tameResidueFacts (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (π : V) (hπ : val π = 1) (hskew : ∀ x y, cup x y = -cup y x)
    (h2 : (2 : k) ≠ 0) (h : TameResidueFacts cup val π) :
    TameSymbolFactors cup val := by
  classical
  have hpp : cup π π = 0 := by
    have hneg : cup π π = -(cup π π) := hskew π π
    have h0 : cup π π + cup π π = 0 := by
      have h1 := congrArg (fun t => cup π π + t) hneg
      simpa using h1
    have h2s : (2 : k) • (cup π π) = 0 := by
      rw [show (2 : k) = 1 + 1 from by norm_num, add_smul]
      simp only [one_smul]
      exact h0
    have hc := congrArg (fun t => (2 : k)⁻¹ • t) h2s
    rwa [smul_smul, inv_mul_cancel₀ h2, one_smul, smul_zero] at hc
  let W : Submodule k H2 := residueSpan cup val
  let Ψ : ↥(LinearMap.ker val) →ₗ[k] H2 ⧸ W :=
    (Submodule.mkQ W).comp (residuePhi cup val π)
  have hker : Ψ.ker = ⊥ := TameResidueFacts.ker_comp_mkQ_eq_bot h
  let g : H2 ⧸ W →ₗ[k] ↥(LinearMap.ker val) :=
    Classical.choose (LinearMap.exists_leftInverse_of_injective Ψ hker)
  have hg := Classical.choose_spec (LinearMap.exists_leftInverse_of_injective Ψ hker)
  have hleft : ∀ y : ↥(LinearMap.ker val), g (Ψ y) = y := by
    intro y
    have hl := congrFun (congrArg DFunLike.coe hg) y
    simpa [LinearMap.comp_apply] using hl
  have huu : ∀ y z : ↥(LinearMap.ker val),
      (g.comp (Submodule.mkQ W)) (cup (y : V) (z : V)) = 0 := by
    intro y z
    have hz : (Submodule.mkQ W) (cup (y : V) (z : V)) = 0 :=
      (Submodule.Quotient.mk_eq_zero W).mpr (cup_mem_residueSpan cup val y z)
    simp [LinearMap.comp_apply, hz]
  have hupi : ∀ y : ↥(LinearMap.ker val),
      (g.comp (Submodule.mkQ W)) (cup (y : V) π) = y := by
    intro y
    have hl := hleft y
    simpa [LinearMap.comp_apply, Ψ, residuePhi_apply] using hl
  exact ⟨g.comp (Submodule.mkQ W), tameExpr_of_res cup val π hπ hskew hpp _ huu hupi⟩

theorem tameSymbolFactors_iff (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (π : V) (hπ : val π = 1) (hskew : ∀ x y, cup x y = -cup y x) (h2 : (2 : k) ≠ 0) :
    TameSymbolFactors cup val ↔ TameResidueFacts cup val π :=
  ⟨tameResidueFacts_of_tameSymbolFactors cup val π hπ,
    tameSymbolFactors_of_tameResidueFacts cup val π hπ hskew h2⟩

theorem nonempty_henselResidueData_iff_tameSymbolFactors (cup : V →ₗ[k] V →ₗ[k] H2)
    (val : V →ₗ[k] k) (π : V) (hπ : val π = 1) (hskew : ∀ x y, cup x y = -cup y x)
    (h2 : (2 : k) ≠ 0) :
    (∃ D : HenselResidueData k V H2 ↥(LinearMap.ker val) cup, D.val = val) ↔
      TameSymbolFactors cup val :=
  (nonempty_henselResidueData_iff cup val π hπ hskew).trans
    (tameSymbolFactors_iff cup val π hπ hskew h2).symm

end TameSymbol

/-! ## 反模型：`(R2)` 严格弱于 `residueSpan = ⊥` -/

section ToyModel

/-- `ℚ³` 上的叉积 `∪`。 -/
noncomputable def toyCross : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun x :=
    { toFun := fun y =>
        ![x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]
      map_add' := by
        intro y z
        ext j
        fin_cases j <;> simp <;> ring
      map_smul' := by
        intro c y
        ext j
        fin_cases j <;> simp <;> ring }
  map_add' := by
    intro x x'
    ext y j
    fin_cases j <;> simp <;> ring
  map_smul' := by
    intro c x
    ext y j
    fin_cases j <;> simp <;> ring

noncomputable def toyPi : Fin 3 → ℚ := ![0, 0, 1]

noncomputable def toyVal : (Fin 3 → ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) 2

theorem toyVal_toyPi : toyVal toyPi = 1 := by
  simp [toyVal, toyPi, LinearMap.proj_apply]

theorem toyCross_skew (x y : Fin 3 → ℚ) : toyCross x y = -toyCross y x := by
  ext j
  fin_cases j <;> simp [toyCross] <;> ring

theorem toyCross_pi (x : Fin 3 → ℚ) : toyCross x toyPi = ![x 1, -x 0, 0] := by
  ext j
  fin_cases j <;> simp [toyCross, toyPi]

/-- 反模型上的 `res`：`w ↦ (−w₁, w₀, 0)`。 -/
noncomputable def toyResFun (w : Fin 3 → ℚ) : ↥(LinearMap.ker toyVal) :=
  ⟨![-w 1, w 0, 0], by simp [toyVal, LinearMap.proj_apply]⟩

noncomputable def toyRes : (Fin 3 → ℚ) →ₗ[ℚ] ↥(LinearMap.ker toyVal) where
  toFun := toyResFun
  map_add' w w' := by
    apply Subtype.ext
    ext j
    fin_cases j <;> simp [toyResFun, Pi.add_apply] <;> ring
  map_smul' c w := by
    apply Subtype.ext
    ext j
    fin_cases j <;> simp [toyResFun, Pi.smul_apply]

theorem toy_tameSymbolFactors : TameSymbolFactors toyCross toyVal := by
  refine ⟨toyRes, ?_⟩
  intro a b
  have key : (toyRes (toyCross a b) : Fin 3 → ℚ)
      = ![- (toyCross a b) 1, (toyCross a b) 0, 0] := by
    simp [toyRes, toyResFun]
  apply Subtype.ext
  rw [key]
  simp only [tameExpr_coe, toyVal, LinearMap.proj_apply, toyCross,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ext j
  fin_cases j <;> simp <;> ring

theorem toy_residueSpan_ne_bot : residueSpan toyCross toyVal ≠ ⊥ := by
  intro hbot
  have hmem : ![(0 : ℚ), 0, 1] ∈ residueSpan toyCross toyVal := by
    have hc := cup_mem_residueSpan toyCross toyVal
      (⟨![1, 0, 0], by simp [toyVal, LinearMap.proj_apply]⟩ : ↥(LinearMap.ker toyVal))
      (⟨![0, 1, 0], by simp [toyVal, LinearMap.proj_apply]⟩ : ↥(LinearMap.ker toyVal))
    simpa [toyCross] using hc
  rw [hbot] at hmem
  have hzero : (![(0 : ℚ), 0, 1] : Fin 3 → ℚ) = 0 := by simpa using hmem
  have := congrFun hzero 2
  simp at this

/-- ★★★ **`(R2)` 的真值严格弱于 `residueSpan = ⊥`（机检反模型）**：
存在杯积载体使 `TameResidueFacts`（＝ (R1)＋(R2)，＝ `∃D`）成立，而 `residueSpan ≠ ⊥`。 -/
theorem exists_tameResidueFacts_of_residueSpan_ne_bot :
    ∃ (cup : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ))
      (val : (Fin 3 → ℚ) →ₗ[ℚ] ℚ) (π : Fin 3 → ℚ),
      TameResidueFacts cup val π ∧ residueSpan cup val ≠ ⊥ :=
  ⟨toyCross, toyVal, toyPi,
    (tameSymbolFactors_iff toyCross toyVal toyPi toyVal_toyPi toyCross_skew
      (by norm_num : (2 : ℚ) ≠ 0)).mp toy_tameSymbolFactors,
    toy_residueSpan_ne_bot⟩

end ToyModel

end L20261018

/-! ## 机检读数（`#print axioms`） -/

#print axioms L20261018.tameExpr
#print axioms L20261018.tameExpr_uu
#print axioms L20261018.tameExpr_u_pi
#print axioms L20261018.tameExpr_pi_u
#print axioms L20261018.tameExpr_pi_pi
#print axioms L20261018.tameExpr_skew
#print axioms L20261018.tameResidueFacts_of_tameSymbolFactors
#print axioms L20261018.tameSymbolFactors_of_tameResidueFacts
#print axioms L20261018.tameSymbolFactors_iff
#print axioms L20261018.nonempty_henselResidueData_iff_tameSymbolFactors
#print axioms L20261018.toy_tameSymbolFactors
#print axioms L20261018.toy_residueSpan_ne_bot
#print axioms L20261018.exists_tameResidueFacts_of_residueSpan_ne_bot
