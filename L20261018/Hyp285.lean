import L20261018.Hyp284

/-!
# R1166（**第 5 项组装第四步：`residueSpan = ⊥` 的逻辑骨架**）

## 本轮做什么

`Hyp284.tameResidueFacts_of_span_eq_bot` 已把 (R2) 归约为 **`residueSpan = ⊥`**。
本轮给出它的**逻辑骨架**，把几何义务压成一条包含关系：

```
residueSpan cup val ≤ range (H²(𝕜) --infl--> H²(F))       （单位×单位杯积是不分歧类）
H²(𝕜) = 0                                                 （cd_p(G_𝕜) ≤ 1，Hyp284）
⟹ residueSpan cup val = ⊥
```

**机检的抽象层**：`residueSpan_eq_bot_of_le_range` —— 只要 `residueSpan` 落在某个
**定义域为 `Subsingleton`** 的线性映射的值域内，它就是 `⊥`。

**剩余的几何义务（唯一）**：`residueSpan ≤ range (infl : H²(𝕜,μ_p) → H²(F,μ_p))`，
即「单位×单位杯积类是不分歧类」。这一步需要库内 `Inflation.Basic` 的 `explicitInfl2`
与系数字典（`muNRep` ↔ `ZMod p`）的拼接。

## 本轮

| 声明 | 内容 |
|---|---|
| **`residueSpan_eq_bot_of_le_range`** | ★★★★ **`residueSpan ≤ range f`（`f` 定义域 subsingleton）⟹ `residueSpan = ⊥`** |
| **`tameResidueFacts_of_le_range`** | ★★★★★ **合成版：`residueSpan ≤ range f` ＋ (R1) ⟹ `TameResidueFacts`** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]
variable {cup : V →ₗ[k] V →ₗ[k] H2} {val : V →ₗ[k] k} {π : V}

/-- ★★★★ **`residueSpan = ⊥` 的逻辑骨架**：

若 `residueSpan` 落在某个线性映射 `f : M →ₗ[k] H2` 的值域内，而 `M` 是 **subsingleton**
（即 `H²(𝕜, μ_p) = 0`），则 `residueSpan = ⊥`。 -/
theorem residueSpan_eq_bot_of_le_range {M : Type*} [AddCommGroup M] [Module k M] [Subsingleton M]
    (f : M →ₗ[k] H2) (h : residueSpan cup val ≤ LinearMap.range f) :
    residueSpan cup val = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨m, hm⟩ := h hx
  have hm0 : m = 0 := Subsingleton.elim m 0
  rw [hm0, map_zero] at hm
  rw [← hm]
  exact Submodule.zero_mem _

/-- ★★★★★ **合成版**：`residueSpan ≤ range f`（`f` 定义域 subsingleton）＋ **(R1)** ⟹ `TameResidueFacts`。

即：一旦几何义务「单位×单位杯积经 `H²(𝕜)` 分解」＋「`H²(𝕜) = 0`」成立，
两条剩余事实**同时**得到（(R2) 由 `residueSpan_eq_bot_of_le_range`，(R1) 由假设）。 -/
theorem tameResidueFacts_of_le_range {M : Type*} [AddCommGroup M] [Module k M] [Subsingleton M]
    (f : M →ₗ[k] H2) (h : residueSpan cup val ≤ LinearMap.range f)
    (hR1 : Function.Injective (residuePhi cup val π)) :
    TameResidueFacts cup val π :=
  tameResidueFacts_of_span_eq_bot (residueSpan_eq_bot_of_le_range f h) hR1

/-! ### 与一般 Hensel 的 `D` 的存在性对接 -/

variable {F : Type} [Field F] {p : ℕ} [NeZero p] [Fact p.Prime]

/-- ★★★★★ **一般 Hensel 的 `D` 存在 —— 归约到「不分歧分解 ＋ (R1)」**。

前提：
* `hπ`：`v(π) = 1`（`val_pi`，初等块）；
* `hskew`：杯积斜对称；
* `hR1`：`Φ = cup(·, (π))` 在 `ker v̄` 上单射（＝ **(R1)**，已有类无关的范数形式路线）；
* `hdecomp`：**单位×单位杯积经 `M` 分解**，且 `M` 是 subsingleton（＝「`H²(𝕜,μ_p) = 0`」）。

结论：**`HenselResidueData`（论文的 `D`）存在**，其 `val` 就是 `v̄ = valH1LinearGen v hp`。
⟹ 第 5 项的全部剩余 = `hR1`（已有路线）＋ `hdecomp`（不发散分解，由 `cd`／inflation 供给）。 -/
theorem exists_henselResidueData_of_le_range
    (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (hskew : ∀ x y, ((TauCeti.ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) x y
      = -(((TauCeti.ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) y x))
    (hR1 : Function.Injective (residuePhi
      ((TauCeti.ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hp)
      (TauCeti.ClassFieldTheory.kummerClass F hp π)))
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M] [Subsingleton M]
    (f : M →ₗ[ZMod p]
      ↑(continuousCohomology (1 + 1) (TauCeti.ClassFieldTheory.muNRep p F)).toModuleCat)
    (hdecomp : residueSpan ((TauCeti.ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hp) ≤ LinearMap.range f) :
    ∃ D : HenselResidueData (ZMod p)
        ↑(continuousCohomology 1 (TauCeti.ClassFieldTheory.muNRep p F)).toModuleCat
        ↑(continuousCohomology (1 + 1) (TauCeti.ClassFieldTheory.muNRep p F)).toModuleCat
        ↥(LinearMap.ker (valH1LinearGen (p := p) v hp))
        ((TauCeti.ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1),
      D.val = valH1LinearGen (p := p) v hp :=
  (generalHensel_reduction (p := p) v hp hζ hπ hskew).mpr
    (tameResidueFacts_of_le_range f hdecomp hR1)

end L20261018

#print axioms L20261018.residueSpan_eq_bot_of_le_range
#print axioms L20261018.tameResidueFacts_of_le_range
#print axioms L20261018.exists_henselResidueData_of_le_range
