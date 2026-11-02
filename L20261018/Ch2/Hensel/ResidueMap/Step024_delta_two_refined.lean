import L20261018.Ch4.Step017_thm_ramified_and_corollary_class_free
import L20261018.Ch4.Step014_ramified_vanishing_hensel_level
import L20261018.Ch2.Hensel.ResidueMap.Step005_residue_cup_data_fields_reduced
import L20261018.Ch2.Hensel.ResidueMap.Step006_tame_pi_u_of
import L20261018.Ch2.Hensel.ResidueMap.Step018_huu_discharged
import L20261018.Ch2.Hensel.ResidueMap.Step020_cup_pi_nonzero_injective
import L20261018.Ch2.Hensel.ResidueMap.Step021_res_and_tame_u_pi_discharged

/-!
# R1013：`∂₂` 的**精确化** —— 11 字段结构 ⟺ **两条剩余事实**

第 (3) 项（自建 `∂₂`）的**账目压缩**：`HenselResidueData`（`Hyp110`，11 个字段，论文 §2.4
两条命题的 `∂₂` 部分）在**规范载体** `VK := ker \bar v`（`infl := 子类型`）上**恰好等价于两条
关于 `∪` 的事实**：

| 事实 | 陈述 | 论文出处 |
|---|---|---|
| **(R1)** `phi_injective` | `Φ := ∪(·, π)` 在 `ker \bar v` 上**单射** | `prop:prelim-residue`(1) 的 `∂₂(inf η ∪ (π)) = η`（存在左逆 ⟺ 单射） |
| **(R2)** `disjoint` | `im Φ` 与「单位类之间杯积的张成」**不相交** | `prop:prelim-residue`(2) 的 `∂₂((u)∪(w)) = 0`（`∂₂` 在 `im Φ` 上是 `Φ⁻¹`，在单位杯积上必须为 `0`） |

**两条都是 GS 6.8.8 的 `H²` 层形态**（`F = K((π))` 的分裂剩余正合列
`0 → H²(K) → H²(F) → H¹(K) → 0` 的**两个半边**），也都**不是**纯线性代数。

## 为什么这是「精确化」而不是「重述」

`HenselResidueData` 有 11 个字段，其中 8 个（`val`／`infl`／`inj_infl`／`val_infl`／`pi`／
`val_pi`／`split`／`tame_pi_u`）在规范载体上是**义务可查**的：`split` 是 `Hyp117.decomp_mem_ker`
（纯线性代数），`tame_pi_u` 是 `Hyp119.tame_pi_u_of`（由 `tame_uu` ＋ `tame_u_pi` ＋ 斜对称
**推出**）。故结构只剩 **`res`** 一个真的自由度，而 `res` 的**全部约束**恰是 (R1) ＋ (R2)：

* **(R1) ⟹ `res` 存在**（本文件 `henselResidueDataOfFacts`）：取 `Ψ := (ker \bar v → H² ⧸ W)`，
  `W := span{∪ y z | y z ∈ ker}`；(R1) ＋ (R2) ⟹ `ker Ψ = ⊥` ⟹ 有左逆 `g`；令
  `res := g ∘ (商映射)`，则 `res (Φ y) = y`（`tame_u_pi`）且 `res (∪ y z) = 0`（`tame_uu`，因
  `∪ y z ∈ W`）。**无需任何基、任何补空间选择**。
* **(R1) ＋ (R2) ⟸ `res`**（本文件 `tameResidueFacts_of_henselResidueData`）：`res ∘ Φ = id` 给
  (R1)；(R2) 由 `tame_uu` ＋ `res ∘ Φ = id` 得。

## 与 R1012 的关系（**更正**）

R1012 记「第 4 条值 `∂₂(inf ξ) = 0` 需要二阶膨胀 `inf₂`，结构里没有」。**在规范载体
`VK := ker \bar v` 上这条不需要 `inf₂`**：`(u)∪(w) = ∪(infl u)(infl w) ∈ W`，故 `∂₂` 在 `im Φ`
之外取 0 时它自动为 0 —— 这正是 (R2)。`inf₂` 只在**取 `VK := H¹(K, μ_p)`** 且把 `inf` 写成
另一个对象时才出现；那是**载体选择**的产物，不是数学缺口。

## 完备情形：两条事实**已机检**（故本归约非空、非空洞）

| 事实 | 完备情形（`IsNonarchimedeanLocalField`）的见证 |
|---|---|
| (R2) | `Hyp135.ker_cup_eq_zero`：`ker` 内任两元的杯积**直接为零** ⟹ `W = ⊥` ⟹ 不相交平凡 |
| (R1) | `Hyp138.kerCupPi_injective`（`ker` 至多 1 维 ＋ `Hyp137` 的 `Φ ≠ 0`） |

⟹ 论文层级的 4.2 在完备情形由**两条事实**重新得到（`orth_eq_bot_paper_route_residue_facts`），
与 `Hyp139` 的路线**独立**（后者不经 `tame_pi_u_of` 的抽象化）。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

/-! ## 1. 抽象层：`Φ`、`W`、两条事实 -/

section Abstract

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- `Φ := ∪(·, π)` 限制在 `ker \bar v` 上（论文 `∂₂` 的「`π` 方向」）。 -/
def residuePhi (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) (π : V) :
    ↥(LinearMap.ker val) →ₗ[k] H2 where
  toFun y := cup (y : V) π
  map_add' y z := by simp
  map_smul' c y := by simp

@[simp]
theorem residuePhi_apply (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) (π : V)
    (y : ↥(LinearMap.ker val)) : residuePhi cup val π y = cup (y : V) π := rfl

/-- `W`：「单位类之间杯积」张成的子空间（不分歧块；GS 6.8.8 里 `im(inf₂)` 的像）。 -/
def residueSpan (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) : Submodule k H2 :=
  Submodule.span k (Set.range fun p : ↥(LinearMap.ker val) × ↥(LinearMap.ker val) =>
    cup (p.1 : V) (p.2 : V))

theorem cup_mem_residueSpan (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (y z : ↥(LinearMap.ker val)) : cup (y : V) (z : V) ∈ residueSpan cup val :=
  Submodule.subset_span ⟨(y, z), rfl⟩

-- @source file=raw/L20261018.tex locator=line:1050 quote="\partial_2((u)\cup(\pi))=(\bar u),\partial_2((\pi)\cup(u))=-(\bar u),\partial_2((u)\cup(w))=0."
/-- **两条剩余事实**（`VK = ker \bar v` 载体上等价于 `HenselResidueData`）。 -/
structure TameResidueFacts (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) (π : V) : Prop where
  /-- **(R1)** `∪(·, π)` 在 `ker \bar v` 上单射（GS 6.8.8：剩余映射在 `inf(η)∪(π)` 上取 `η`）。 -/
  phi_injective : Function.Injective (residuePhi cup val π)
  /-- **(R2)** `im Φ` 与单位杯积张成块不相交（GS 6.8.8：`∂₂((u)∪(w)) = 0`）。 -/
  disjoint : Disjoint (LinearMap.range (residuePhi cup val π)) (residueSpan cup val)

namespace TameResidueFacts

variable {cup : V →ₗ[k] V →ₗ[k] H2} {val : V →ₗ[k] k} {π : V}

/-- 两条事实 ⟹ `Φ` 落在 `H² ⧸ W` 上仍单射（这是造 `res` 的唯一要点）。 -/
theorem ker_comp_mkQ_eq_bot (h : TameResidueFacts cup val π) :
    LinearMap.ker ((Submodule.mkQ (residueSpan cup val)).comp (residuePhi cup val π)) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro y hy
  rw [LinearMap.comp_apply] at hy
  have hmem : residuePhi cup val π y ∈ residueSpan cup val := by
    have hy' := hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy'
    exact hy'
  have hbot : residuePhi cup val π y ∈ (⊥ : Submodule k H2) := by
    have hmem' : residuePhi cup val π y ∈
        LinearMap.range (residuePhi cup val π) ⊓ residueSpan cup val :=
      Submodule.mem_inf.mpr ⟨⟨y, rfl⟩, hmem⟩
    have hd : LinearMap.range (residuePhi cup val π) ⊓ residueSpan cup val = ⊥ := disjoint_iff.mp h.disjoint
    rw [hd] at hmem'
    exact hmem'
  have h0 : residuePhi cup val π y = 0 := by simpa using hbot
  exact h.phi_injective (by rw [h0, map_zero])

end TameResidueFacts

/-! ## 2. 两条事实 ⟹ `HenselResidueData`（构造，无补空间选择） -/

/-- **两条剩余事实 ⟹ 11 字段结构**（`VK := ker \bar v`、`infl := 子类型`）。

`res := g ∘ (H² → H² ⧸ W)`，`g` 是 `Φ` 过商映射后的左逆（(R1) ＋ (R2) 保证其存在）。 -/
noncomputable def henselResidueDataOfFacts (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (π : V) (hπ : val π = 1) (hskew : ∀ x y, cup x y = - cup y x)
    (h : TameResidueFacts cup val π) :
    HenselResidueData k V H2 ↥(LinearMap.ker val) cup := by
  classical
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
  have hres_uu : ∀ y z : ↥(LinearMap.ker val),
      (g.comp (Submodule.mkQ W)) (cup (y : V) (z : V)) = 0 := by
    intro y z
    have hz : (Submodule.mkQ W) (cup (y : V) (z : V)) = 0 :=
      (Submodule.Quotient.mk_eq_zero W).mpr (cup_mem_residueSpan cup val y z)
    simp [LinearMap.comp_apply, hz]
  have hres_u_pi : ∀ y : ↥(LinearMap.ker val),
      (g.comp (Submodule.mkQ W)) (cup (y : V) π) = y := by
    intro y
    have hl := hleft y
    simpa [LinearMap.comp_apply, Ψ, residuePhi_apply] using hl
  refine ⟨g.comp (Submodule.mkQ W), val, (LinearMap.ker val).subtype, Subtype.val_injective,
    (fun y => y.2), π, hπ, (fun x => decomp_mem_ker val π hπ x), hres_uu, hres_u_pi, ?_⟩
  intro κ hκ z
  exact tame_pi_u_of cup hskew val π hπ (g.comp (Submodule.mkQ W)) hres_uu hres_u_pi κ hκ z


/-! ### 构造的 `val` 字段（定义上等于传入的 `val`） -/

theorem henselResidueDataOfFacts_val (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) (π : V)
    (hπ : val π = 1) (hskew : ∀ x y, cup x y = - cup y x) (h : TameResidueFacts cup val π) :
    (henselResidueDataOfFacts cup val π hπ hskew h).val = val := rfl

/-! ## 3. `HenselResidueData` ⟹ 两条事实（必要性：归约是紧的） -/

section Converse

variable {VK : Type*} [AddCommGroup VK] [Module k VK]

/-- **11 字段结构 ⟹ 两条剩余事实**（同一载体：`D.val = val`）。

只有 `split`／`val_infl`／`val_pi`／`tame_uu`／`tame_u_pi` 五条被用到。 -/
theorem tameResidueFacts_of_henselResidueData (cup : V →ₗ[k] V →ₗ[k] H2)
    (val : V →ₗ[k] k) (π : V) (D : HenselResidueData k V H2 VK cup)
    (hval : D.val = val) (hπ : val π = 1) : TameResidueFacts cup val π := by
  classical
  -- `π = D.infl x₁ + D.pi`（`split` ＋ `val π = 1`）
  have hvalπ : D.val π = 1 := by rw [hval]; exact hπ
  obtain ⟨x₁, m, hm⟩ := D.split π
  have hm1 : m = 1 := by
    have h := congrArg D.val hm
    rw [map_add, map_smul, D.val_infl, zero_add, D.val_pi, smul_eq_mul, mul_one, hvalπ] at h
    exact h.symm
  have hπ' : π = D.infl x₁ + D.pi := by
    rw [hm, hm1, one_smul]
  -- `ker val ⊆ range D.infl`
  have hmem_range : ∀ y : ↥(LinearMap.ker val), ∃ x₀ : VK, D.infl x₀ = (y : V) := by
    intro y
    obtain ⟨x₀, m', hy⟩ := D.split (y : V)
    have hyval : D.val (y : V) = 0 := by rw [hval]; exact y.2
    have hm' : m' = 0 := by
      have h := congrArg D.val hy
      rw [map_add, map_smul, D.val_infl, zero_add, D.val_pi, smul_eq_mul, mul_one] at h
      rw [h] at hyval
      exact hyval
    refine ⟨x₀, ?_⟩
    rw [hy, hm', zero_smul, add_zero]
  refine ⟨?_, ?_⟩
  · -- (R1) `Φ` 单射
    intro y z hyz
    have hyz' : residuePhi cup val π (y - z) = 0 := by
      rw [map_sub, hyz, sub_self]
    obtain ⟨a, ha⟩ := hmem_range (y - z)
    have hzero : D.res (cup ((y - z : ↥(LinearMap.ker val)) : V) π) = 0 := by
      simpa using congrArg D.res hyz'
    have hkey : D.res (cup ((y - z : ↥(LinearMap.ker val)) : V) π) = a := by
      rw [← ha, hπ', map_add, map_add, D.tame_uu, D.tame_u_pi, zero_add]
    have ha0 : a = 0 := by rw [← hkey, hzero]
    have hyz0 : (y - z : ↥(LinearMap.ker val)) = 0 := by
      apply Subtype.ext
      rw [← ha, ha0, map_zero]
      rfl
    exact sub_eq_zero.mp hyz0
  · -- (R2) 不相交
    rw [disjoint_iff]
    rw [eq_bot_iff]
    intro z hz
    rw [Submodule.mem_bot]
    obtain ⟨⟨y, hy⟩, hzW⟩ := Submodule.mem_inf.mp hz
    -- `D.res` 在 `W` 上为零
    have hspan : ∀ w ∈ residueSpan cup val, D.res w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨⟨y₁, y₂⟩, rfl⟩ := hx
          obtain ⟨a₁, ha₁⟩ := hmem_range y₁
          obtain ⟨a₂, ha₂⟩ := hmem_range y₂
          change D.res (cup (y₁ : V) (y₂ : V)) = 0
          rw [← ha₁, ← ha₂]
          exact D.tame_uu a₁ a₂
      | zero => rw [map_zero]
      | add x y _ _ ihx ihy => rw [map_add, ihx, ihy, add_zero]
      | smul c x _ ih => rw [map_smul, ih, smul_zero]
    obtain ⟨a, ha⟩ := hmem_range y
    have hresz0 : D.res z = 0 := hspan z hzW
    have hreszy : D.res z = a := by
      rw [← hy, residuePhi_apply, ← ha, hπ', map_add, map_add, D.tame_uu, D.tame_u_pi, zero_add]
    have ha0 : a = 0 := by rw [← hreszy, hresz0]
    have hy0 : y = 0 := by
      apply Subtype.ext
      rw [← ha, ha0, map_zero]
      rfl
    rw [← hy, hy0, residuePhi_apply]
    simp

/-- **归约的紧性**：在规范载体 `ker \bar v` 上，「存在 `D` 且 `D.val = val`」**等价于**两条剩余事实。 -/
theorem nonempty_henselResidueData_iff (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (π : V) (hπ : val π = 1) (hskew : ∀ x y, cup x y = - cup y x) :
    (∃ D : HenselResidueData k V H2 ↥(LinearMap.ker val) cup, D.val = val) ↔
      TameResidueFacts cup val π := by
  constructor
  · rintro ⟨D, hD⟩
    exact tameResidueFacts_of_henselResidueData cup val π D hD hπ
  · intro h
    exact ⟨henselResidueDataOfFacts cup val π hπ hskew h, rfl⟩

end Converse

end Abstract

/-! ## 4. 完备情形：两条事实的见证（本归约**非空**） -/

section Complete

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p]
  [HasEnoughRootsOfUnity F p]

/-- **完备情形的两条剩余事实**（故 `TameResidueFacts` 有非空见证，L1／L10①）。

* (R2)：`Hyp135.ker_cup_eq_zero` 给 `W = ⊥`；
* (R1)：`Hyp138.kerCupPi_injective`（`Hyp137` 给 `Φ ≠ 0`）。 -/
theorem tameResidueFacts_of_complete (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    {π : Fˣ} (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p)) (valLin F p hp)
      (KummerBridge.kummerClass F p hp π) := by
  classical
  have hpi : valLin F p hp (KummerBridge.kummerClass F p hp π) = 1 :=
    valLin_pi (F := F) (p := p) hp hπ
  obtain ⟨γ, hγ⟩ := exists_cup_pi_ne_zero (F := F) (p := p) hp hp2 (hπ := hπ) hpu
    (a1 := a1) (a2 := a2) hne
  have hinj := kerCupPi_injective (F := F) (p := p) hp hp2 (hπ := hπ) hpu (γ := γ) hγ
  refine ⟨?_, ?_⟩
  · -- (R1)：`residuePhi = kerCupPi`
    intro y z hyz
    have hyz' : kerCupPi (F := F) (p := p) hp π y = kerCupPi (F := F) (p := p) hp π z := by
      simpa [kerCupPi_apply, residuePhi_apply] using hyz
    exact hinj hyz'
  · -- (R2)：`W = ⊥`
    rw [disjoint_iff]
    rw [eq_bot_iff]
    intro z hz
    rw [Submodule.mem_bot]
    have hspan : ∀ w ∈ residueSpan (GaloBase.cup (K := F) (p := p)) (valLin F p hp), w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨⟨y₁, y₂⟩, rfl⟩ := hx
          change GaloBase.cup (K := F) (p := p) (y₁ : GaloBase.V F p) (y₂ : GaloBase.V F p) = 0
          exact ker_cup_eq_zero (F := F) (p := p) hp hp2 (hπ := hπ) hpu y₁ y₂
      | zero => rfl
      | add x y _ _ ihx ihy => rw [ihx, ihy, add_zero]
      | smul c x _ ih => rw [ih, smul_zero]
    exact hspan z (Submodule.mem_inf.mp hz).2

end Complete

/-! ## 5. 论文层级 4.2：`D` 换成两条剩余事实 -/

section PaperLevel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime]
  [HasEnoughRootsOfUnity F p]

/-- **`lem:ramified-vanishing`（4.2）以两条剩余事实为唯一缺口**：把 `D` 换成
`TameResidueFacts`（＋ 完备情形的估值层 `valLin`）。

`Hyp153.orth_eq_bot_paper_route_hensel` 的 `D` 由 `henselResidueDataOfFacts` 构造。 -/
-- @source file=raw/L20261018.tex locator=line:1608 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem orth_eq_bot_paper_route_residue_facts (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    {π : Fˣ} (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    {a1 a2 : GaloBase.V F p} (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2, valLin F p hp u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)]
    (hfacts : TameResidueFacts (GaloBase.cup (K := F) (p := p)) (valLin F p hp)
      (KummerBridge.kummerClass F p hp π)) :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ := by
  have hpi : valLin F p hp (KummerBridge.kummerClass F p hp π) = 1 :=
    valLin_pi (F := F) (p := p) hp hπ
  exact orth_eq_bot_paper_route_hensel (F := F) (p := p)
    (D := henselResidueDataOfFacts (GaloBase.cup (K := F) (p := p)) (valLin F p hp)
      (KummerBridge.kummerClass F p hp π) hpi
      (fun x y => GaloBase.cup_skew (K := F) (p := p) x y) hfacts)
    hp2 hne hval

end PaperLevel

end L20261018

#print axioms L20261018.TameResidueFacts.ker_comp_mkQ_eq_bot
#print axioms L20261018.henselResidueDataOfFacts
#print axioms L20261018.tameResidueFacts_of_henselResidueData
#print axioms L20261018.nonempty_henselResidueData_iff
#print axioms L20261018.tameResidueFacts_of_complete
#print axioms L20261018.orth_eq_bot_paper_route_residue_facts
