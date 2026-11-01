import L20261018.Ch4.Step013_basis_selection_u

/-!
# R1001：**4.2 在论文的假设层级（Hensel 层）—— 不假设完备性/局部域**

R1000 的侦察（`RECON-D2.md`）与本轮判别发现：论文 4.2 的原证明路线
（`Hyp151.orth_eq_bot_paper_route`）的**证明体不依赖 `IsNonarchimedeanLocalField`** ——
它只用 `HenselResidueData` 的字段（即论文 §2.4 的两条命题：`prop:prelim-kummer-valuation` ＋
`prop:prelim-residue`）与杯积的双线性/交替性。

⟹ 本文件把整条路线**降到论文的假设层级**：只留 `[Field F] [Fact p.Prime]`，
把 §2.4 的两条命题作为 `D : HenselResidueData` 这个**具名输入**（论文本身也是引用它们），
从而 4.2 不再需要"完备/局部域"（R996 登记的范围收紧**在本条上消除**）。

**论文假设的对应**：

| 论文（`:1603`） | 本文件 |
|---|---|
| `p` 奇素数 | `[Fact p.Prime]` ＋ `NeZero (2 : ZMod p)` |
| `(F,v)` 特征 0 的 **Hensel 离散赋值域**，`char K ≠ p`，`μ_p ⊂ F` | **不出现**——它们的全部用途都在 §2.4 的两条命题里，而后者正是 `D` 的内容 |
| `(a₁)∪(a₂)≠0` | `hne` |
| `\bar v|_U≠0` | `hval : ∃ u ∈ U, D.val u ≠ 0` |
| `U^⊥=0` | `ResidueCupData.orth (GaloBase.cup) a1 a2 = ⊥` |

**⟹ 这是"逐字"意义上更强的对齐**：条件与论文同层（论文用 §2.4 的两条命题，我们也用）。
其**完备情形实例**已由 `Hyp139.henselResidueDataOfCup` 供给（⟹ `D` 这个具名输入在完备情形
是可证的、非空的）。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

attribute [local instance] TopRep.distribMulAction

/-! ## 1. 类无关的交替性（`x∪x=0`，只需 `2≠0`） -/

theorem cup_self_free (hp2 : NeZero (2 : ZMod p)) (x : GaloBase.V F p) :
    GaloBase.cup (K := F) (p := p) x x = 0 := by
  have h : GaloBase.cup (K := F) (p := p) x x = -GaloBase.cup (K := F) (p := p) x x :=
    GaloBase.cup_skew (K := F) (p := p) x x
  have h2 : (2 : ZMod p) • GaloBase.cup (K := F) (p := p) x x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    abel
  exact (smul_eq_zero.mp h2).resolve_left (NeZero.ne (2 : ZMod p))

/-- `Set.range ![a,b] = {a,b}`（类无关版）。 -/
theorem range_pair_eq_free (a b : GaloBase.V F p) :
    (Set.range ![a, b] : Set (GaloBase.V F p)) = {a, b} := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-! ## 2. 线性代数（`U` 二维、独立、核一维、正交性） -/

theorem pair_linearIndependent_free (hp2 : NeZero (2 : ZMod p)) {x y : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) x y ≠ 0) :
    LinearIndependent (ZMod p) ![x, y] := by
  have hx : x ≠ 0 := by
    intro h0
    exact hne (by rw [h0, LinearMap.map_zero, LinearMap.zero_apply])
  have hy : y ≠ 0 := by
    intro h0
    exact hne (by rw [h0, LinearMap.map_zero])
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hcup : s • (GaloBase.cup (K := F) (p := p) x y) = 0 := by
    have h := congrArg (fun w => GaloBase.cup (K := F) (p := p) w y) hst
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      cup_self_free (F := F) (p := p) hp2, smul_zero, add_zero] at h
    simpa using h
  have hs : s = 0 := by
    rcases smul_eq_zero.mp hcup with h | h
    · exact h
    · exact absurd h hne
  refine ⟨hs, ?_⟩
  have ht : t • y = 0 := by
    have := hst
    rw [hs, zero_smul, zero_add] at this
    exact this
  rcases smul_eq_zero.mp ht with h | h
  · exact h
  · exact absurd h hy

theorem finrank_plane_eq_two_free (hp2 : NeZero (2 : ZMod p)) {x y : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) x y ≠ 0) :
    Module.finrank (ZMod p) ↥(ResidueCupData.plane (k := ZMod p) x y) = 2 := by
  have hli := pair_linearIndependent_free (F := F) (p := p) hp2 hne
  have hspan : ResidueCupData.plane (k := ZMod p) x y
      = Submodule.span (ZMod p) (Set.range ![x, y]) := by
    rw [ResidueCupData.plane, range_pair_eq_free (F := F) (p := p)]
  rw [hspan, finrank_span_eq_card hli]
  simp

/-- 正交于平面 ⟹ 与平面内任一元作杯积为零（类无关版）。 -/
theorem cup_eq_zero_of_mem_orth_free {x a1 a2 : GaloBase.V F p}
    (hx : x ∈ ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2)
    {γ : GaloBase.V F p} (hγ : γ ∈ ResidueCupData.plane (k := ZMod p) a1 a2) :
    GaloBase.cup (K := F) (p := p) x γ = 0 := by
  rw [ResidueCupData.orth, LinearMap.mem_ker, ResidueCupData.commonCupMap_apply,
    Prod.mk_eq_zero] at hx
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨c1, c2, rfl⟩ := (ResidueCupData.mem_plane_iff (k := ZMod p) a1 a2 γ).mp hγ
  simp only [map_add, map_smul, h1, h2, smul_zero, add_zero]

/-- 任意线性泛函：`val|_U ≠ 0` ⟹ `\ker(val|_U)` 一维（类无关版）。 -/
theorem finrank_ker_restrict_plane_eq_one_free (hp2 : NeZero (2 : ZMod p))
    {x y : GaloBase.V F p} (hne : GaloBase.cup (K := F) (p := p) x y ≠ 0)
    (val : GaloBase.V F p →ₗ[ZMod p] ZMod p)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) x y, val u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    Module.finrank (ZMod p) ↥(LinearMap.ker
      (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype)) = 1 := by
  have hφne : (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype) ≠ 0 := by
    obtain ⟨u, hu, hvu⟩ := hval
    intro h
    apply hvu
    have hz : (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype) ⟨u, hu⟩ = 0 := by
      rw [h, LinearMap.zero_apply]
    simpa using hz
  have hsurj : Function.Surjective
      (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype) := by
    intro c
    have hx : ∃ z : ↥(ResidueCupData.plane (k := ZMod p) x y),
        (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype) z ≠ 0 := by
      by_contra h
      push_neg at h
      exact hφne (LinearMap.ext h)
    obtain ⟨z, hz⟩ := hx
    refine ⟨(c / ((val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype) z)) • z, ?_⟩
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ c hz
  have hrange1 : Module.finrank (ZMod p) ↥(LinearMap.range
      (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj,
      (Submodule.topEquiv (R := ZMod p) (M := ZMod p)).finrank_eq, Module.finrank_self]
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (val.comp (ResidueCupData.plane (k := ZMod p) x y).subtype) (V₂ := ZMod p)
  have hplane : Module.finrank (ZMod p) ↥(ResidueCupData.plane (k := ZMod p) x y) = 2 :=
    finrank_plane_eq_two_free (F := F) (p := p) hp2 hne
  rw [hrange1, hplane] at hrn
  omega

/-- `\ker\bar v = \mathrm{im}\,\mathrm{infl}`（类无关版，只用 `D` 的字段）。 -/
theorem HenselResidueData.ker_val_eq_range_infl_free {VK : Type} [AddCommGroup VK]
    [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) VK
      (GaloBase.cup (K := F) (p := p))) :
    LinearMap.ker D.val = LinearMap.range D.infl := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨x₀, m, hxm⟩ := D.split x
    have hm : m = 0 := by
      have h : D.val x = m := by
        rw [hxm, map_add, map_smul, D.val_infl, zero_add, D.val_pi, smul_eq_mul, mul_one]
      rw [hx] at h
      exact h.symm
    rw [LinearMap.mem_range]
    exact ⟨x₀, by rw [hxm, hm, zero_smul, add_zero]⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    rw [LinearMap.mem_ker, D.val_infl]

/-! ## 3. **4.2 在论文假设层级**（Hensel 层；§2.4 两条命题作 `D`） -/

-- @source file=raw/L20261018.tex locator=line:1608 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
/-- **`lem:ramified-vanishing`（论文 4.2）在论文的假设层级**：按论文原证明路线
（`Hyp151` 的逐步转写），只用 §2.4（作 `D`）与线性代数，**不假设完备性/局部域**。 -/
theorem orth_eq_bot_paper_route_hensel {VK : Type} [AddCommGroup VK] [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) VK
      (GaloBase.cup (K := F) (p := p)))
    (hp2 : NeZero (2 : ZMod p))
    {a1 a2 : GaloBase.V F p} (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2, D.val u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ := by
  classical
  have hval' := hval
  obtain ⟨u, hu, hvu⟩ := hval
  set κ : GaloBase.V F p := (D.val u)⁻¹ • u with hκdef
  have hκU : κ ∈ ResidueCupData.plane (k := ZMod p) a1 a2 := Submodule.smul_mem _ _ hu
  have hκval : D.val κ = 1 := by
    rw [hκdef, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hvu
  have hfin := finrank_ker_restrict_plane_eq_one_free (F := F) (p := p) (x := a1) (y := a2)
    (val := D.val) (hval := hval') hp2 hne
  have hpos : 0 < Module.finrank (ZMod p) ↥(LinearMap.ker
      (D.val.comp (ResidueCupData.plane (k := ZMod p) a1 a2).subtype)) := by omega
  haveI : Nontrivial ↥(LinearMap.ker
      (D.val.comp (ResidueCupData.plane (k := ZMod p) a1 a2).subtype)) :=
    Module.nontrivial_of_finrank_pos hpos
  obtain ⟨γc, hγc⟩ := exists_ne (0 : ↥(LinearMap.ker
    (D.val.comp (ResidueCupData.plane (k := ZMod p) a1 a2).subtype)))
  have hγU : ((γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)) : GaloBase.V F p)
      ∈ ResidueCupData.plane (k := ZMod p) a1 a2 :=
    (γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)).2
  have hγker : D.val ((γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)) : GaloBase.V F p) = 0 :=
    LinearMap.mem_ker.mp γc.2
  have hγne : ((γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)) : GaloBase.V F p) ≠ 0 := by
    intro h0
    apply hγc
    exact Subtype.ext (Subtype.ext h0)
  obtain ⟨γ₀, hγ₀⟩ := LinearMap.mem_range.mp (by
    rw [← HenselResidueData.ker_val_eq_range_infl_free (F := F) (p := p) D]
    exact hγker)
  refine eq_bot_iff.mpr ?_
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨x₀, m, hx₀⟩ := D.split x
  have hxγ : GaloBase.cup (K := F) (p := p) x
      ((γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)) : GaloBase.V F p) = 0 :=
    cup_eq_zero_of_mem_orth_free (F := F) (p := p) hx hγU
  have htm : m = 0 := by
    rw [hx₀, ← hγ₀] at hxγ
    have h := congrArg D.res hxγ
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      D.tame_uu x₀ γ₀, zero_add, map_zero] at h
    have hneg : D.res (GaloBase.cup (K := F) (p := p) D.pi (D.infl γ₀)) = -γ₀ :=
      D.tame_pi_u D.pi D.val_pi γ₀
    rw [hneg, smul_neg] at h
    have hγ₀ne : γ₀ ≠ 0 := by
      intro h0
      apply hγne
      rw [← hγ₀, h0, map_zero]
    have : m • γ₀ = 0 := neg_eq_zero.mp h
    rcases smul_eq_zero.mp this with h1 | h1
    · exact h1
    · exact absurd h1 hγ₀ne
  have hx1 : x = D.infl x₀ := by rw [hx₀, htm, zero_smul, add_zero]
  have hxκ : GaloBase.cup (K := F) (p := p) x κ = 0 :=
    cup_eq_zero_of_mem_orth_free (F := F) (p := p) hx hκU
  rw [hx1] at hxκ
  have h := congrArg D.res hxκ
  simp only [map_zero] at h
  have hneg2 : D.res (GaloBase.cup (K := F) (p := p) (D.infl x₀) κ) = x₀ := by
    have hskew : GaloBase.cup (K := F) (p := p) (D.infl x₀) κ
        = - GaloBase.cup (K := F) (p := p) κ (D.infl x₀) :=
      GaloBase.cup_skew (K := F) (p := p) _ _
    rw [hskew, map_neg, D.tame_pi_u κ hκval x₀, neg_neg]
  rw [hneg2] at h
  rw [hx1, h, map_zero]

end L20261018
#print axioms L20261018.cup_self_free
#print axioms L20261018.pair_linearIndependent_free
#print axioms L20261018.finrank_plane_eq_two_free
#print axioms L20261018.cup_eq_zero_of_mem_orth_free
#print axioms L20261018.finrank_ker_restrict_plane_eq_one_free
#print axioms L20261018.HenselResidueData.ker_val_eq_range_infl_free
#print axioms L20261018.orth_eq_bot_paper_route_hensel
