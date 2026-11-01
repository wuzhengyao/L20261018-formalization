import L20261018.Hyp326

/-!
# R1233（S34 第 5 轮）：`prop:prelim-residue`(3) 的**正合／满射／分裂**段

论文 (3)：`F = K((π))` 时 `0 → H^q(K) →^{inf} H^q(F) →^{∂_q} H^{q-1}(K) → 0` 分裂正合。
本战役的 `HenselResidueData`（`q=2, j=1`）只把两端写成字段（`inj_infl`／`val_infl`／`split`），
**未单列**正合性与满射性。本轮把它们**从字段导出**（皆零额外假设）：

| 声明 | 内容 |
|---|---|
| `ker_val_eq_range_infl` | ★★★ `ker v̄ = range infl`（`⊆` 由 `split` ＋ `val_pi`） |
| `exact_infl_val` | ★★★ `Function.Exact infl val` |
| `res_surjective` | ★★★★ `∂₂` 满射（由 `tame_u_pi`：`res (cup (inf y) π) = y`） |
| `isCompl_range_infl_span_pi` | ★★★ `V = range infl ⊕ span{π}`（分裂性） |
| `res_comp_infl_cup_pi` | ★★★ `∂₂ ∘ (· ∪ π) ∘ inf = id_{VK}`（分裂的显式截面） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti

namespace L20261018

section Exactness

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  {H2 : Type*} [AddCommGroup H2] [Module k H2]
  {VK : Type*} [AddCommGroup VK] [Module k VK]
  {cup : V →ₗ[k] V →ₗ[k] H2}

/-- ★★★ **`ker v̄ = range inf`**：`⊆` 由 `split`（`x = inf x₀ + m·π` 且 `val x = m`）给出。 -/
theorem ker_val_eq_range_infl (D : HenselResidueData k V H2 VK cup) :
    LinearMap.ker D.val = LinearMap.range D.infl := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨x₀, m, hm⟩ := D.split x
    have hval : D.val x = m := by
      rw [hm, map_add, map_smul, D.val_infl, zero_add, D.val_pi, smul_eq_mul, mul_one]
    rw [LinearMap.mem_ker] at hx
    refine ⟨x₀, ?_⟩
    rw [hm, ← hval, hx, zero_smul, add_zero]
  · rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    exact D.val_infl y

/-- ★★★ **`inf` 与 `v̄` 正合**（`q=2` 档，逐点形式）。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="\partial_q(\mathrm{inf}(\xi))=0."
theorem exact_infl_val (D : HenselResidueData k V H2 VK cup) (x : V) :
    D.val x = 0 ↔ ∃ y : VK, D.infl y = x := by
  constructor
  · intro h
    have hx : x ∈ LinearMap.ker D.val := h
    rw [ker_val_eq_range_infl D] at hx
    exact LinearMap.mem_range.mp hx
  · rintro ⟨y, rfl⟩
    exact D.val_infl y

/-- ★★★★ **`∂₂` 满射**：`tame_u_pi` 直接给截面 `y ↦ cup (inf y) π`。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="H^q(F,\mu_p^{\otimes j})\xrightarrow{\partial_q}"
theorem res_surjective (D : HenselResidueData k V H2 VK cup) :
    Function.Surjective D.res :=
  fun y => ⟨cup (D.infl y) D.pi, D.tame_u_pi y⟩

/-- ★★★ **分裂性**：`V = range inf ⊕ span{π}`（`π` 的系数由 `v̄` 给出）。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="0\longrightarrow H^q(K,\mu_p^{\otimes j})\xrightarrow{\mathrm{inf}}"
theorem isCompl_range_infl_span_pi (D : HenselResidueData k V H2 VK cup) :
    IsCompl (LinearMap.range D.infl) (Submodule.span k {D.pi}) := by
  constructor
  · -- 交为零：`x ∈ range infl` ⟹ `val x = 0`；`x ∈ span{π}` ⟹ `x = c•π` ⟹ `val x = c`
    rw [disjoint_iff_inf_le]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx2
    have hc_eq : c = 0 := by
      have h := congrArg D.val (hy.trans hc.symm)
      simpa [D.val_infl, D.val_pi] using h.symm
    rw [← hc, hc_eq, zero_smul]
    exact Submodule.zero_mem _
  · -- 上确界为 ⊤：由 split
    rw [codisjoint_iff]
    refine eq_top_iff.mpr ?_
    intro x _
    obtain ⟨x₀, m, hm⟩ := D.split x
    have hx0 : D.infl x₀ ∈ LinearMap.range D.infl := ⟨x₀, rfl⟩
    have hpi : m • D.pi ∈ Submodule.span k ({D.pi} : Set V) :=
      Submodule.smul_mem _ m (Submodule.subset_span rfl)
    rw [hm]
    exact Submodule.add_mem_sup hx0 hpi

/-- ★★★ **分裂的显式截面**：`∂₂ ∘ (· ∪ π) ∘ inf = id_{VK}`。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="\partial_q\bigl(\mathrm{inf}(\eta)\cup(\pi)\bigr)=\eta,\partial_q(\mathrm{inf}(\xi))=0."
theorem res_comp_infl_cup_pi (D : HenselResidueData k V H2 VK cup) (y : VK) :
    D.res (cup (D.infl y) D.pi) = y :=
  D.tame_u_pi y

end Exactness

end L20261018

#print axioms L20261018.ker_val_eq_range_infl
#print axioms L20261018.exact_infl_val
#print axioms L20261018.res_surjective
#print axioms L20261018.isCompl_range_infl_span_pi
#print axioms L20261018.res_comp_infl_cup_pi
