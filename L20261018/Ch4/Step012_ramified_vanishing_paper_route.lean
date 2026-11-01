import L20261018.Ch4.Step011_transition_paragraph_4_1_4_2

/-!
# R999：**按论文原路线重证 4.2**（`lem:ramified-vanishing`，`raw/L20261018.tex:1613–1626`）

论文 4.2 的证明是两行 `\partial_2` 计算：

> 选择 `U` 的基并调整其代表元，可取 `(\pi u),(c)` 为基，其中 `u,c\in\mathcal O_F^\times`，且 `(\bar c)\ne0`。
> 对任意 `x\in U^\perp`，…写成 `x=(w)+k(\pi)`… 正交条件及命题~\ref{prop:prelim-residue} 给出
> `0=\partial_2((c)\cup x)=k(\bar c)`。由于 `(\bar c)\ne0`，有 `k=0`，故 `x=(w)`。再由另一个正交条件，
> `0=\partial_2((\pi u)\cup(w))=-(\bar w)`。因此 `\bar w\in K^{\times p}` …于是 `w=(yz)^p`，从而 `x=(w)=0`。

**本文件的对应（逐步）**：

| 论文步 | Lean 步 |
|---|---|
| 取 `U` 的基，`\bar v` 在基上取 `(1,0)` | `κ∈U` 且 `\bar v(κ)=1`；`γ∈U∩\ker\bar v`，`γ≠0`（由 `Hyp150` 的核 1 维性） |
| `(\bar c)\ne0` | `γ≠0`（`γ` 是核的非零元，即 `(c)` 的角色） |
| `x=(w)+k(\pi)` | `D.split x = x₀ + m•π`（`prop:prelim-kummer-valuation`(2)） |
| `0=\partial_2((c)\cup x)=k(\bar c)\Rightarrow k=0` | `0=D.res(cup x γ)=m•(-γ) ⇒ m=0`（`tame_uu` ＋ `tame_pi_u` ＋ 斜对称） |
| `0=\partial_2((\pi u)\cup(w))=-(\bar w)` | `0=D.res(cup x κ)=x₀`（`tame_pi_u` ＋ 斜对称） |
| `\bar w\in K^{\times p}\Rightarrow w=(yz)^p\Rightarrow x=0` | `x₀=0 ⇒ x=0`（`x₀=0` 即 `(w)=0`，即 `w\in F^{\times p}`） |

**⟹ 与 `Hyp139`（本战役此前的"绕开路线"）相比，本文件是论文证明的**逐步转写**；
两者的差别只是 `D`（`\partial_2` 的三条驯符号）从哪来：这里对**任意** `HenselResidueData` 成立，
实例化用 `Hyp139.henselResidueDataOfCup`（`def`，体可见）。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-- 正交于平面 ⟹ 与平面内任一元作杯积为零。 -/
theorem cup_eq_zero_of_mem_orth {x a1 a2 : GaloBase.V F p}
    (hx : x ∈ ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2)
    {γ : GaloBase.V F p} (hγ : γ ∈ ResidueCupData.plane (k := ZMod p) a1 a2) :
    GaloBase.cup (K := F) (p := p) x γ = 0 := by
  rw [ResidueCupData.orth, LinearMap.mem_ker, ResidueCupData.commonCupMap_apply,
    Prod.mk_eq_zero] at hx
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨c1, c2, rfl⟩ := (ResidueCupData.mem_plane_iff (k := ZMod p) a1 a2 γ).mp hγ
  simp only [map_add, map_smul, h1, h2, smul_zero, add_zero]

/-- `\ker\bar v = \mathrm{im}\,\mathrm{infl}`（`HenselResidueData` 版）。 -/
theorem HenselResidueData.ker_val_eq_range_infl {VK : Type} [AddCommGroup VK]
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

/-- 任意线性泛函版：`val|_U ≠ 0` ⟹ `\ker(val|_U)` 一维。 -/
theorem finrank_ker_restrict_plane_eq_one_general (hp2 : NeZero (2 : ZMod p))
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
    finrank_plane_eq_two (F := F) (p := p) hp2 hne
  rw [hrange1, hplane] at hrn
  omega

/-- **论文 4.2 原证明路线**（对任意 `HenselResidueData`，即 `\partial_2` 的三条驯符号 ＋ 分解）。 -/
-- @source file=raw/L20261018.tex locator=line:1608 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem orth_eq_bot_paper_route {VK : Type} [AddCommGroup VK] [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) VK
      (GaloBase.cup (K := F) (p := p)))
    (hp2 : NeZero (2 : ZMod p))
    {a1 a2 : GaloBase.V F p} (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2, D.val u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ := by
  classical
  -- ① `κ ∈ U`，`\bar v(κ) = 1`
  have hval' := hval
  obtain ⟨u, hu, hvu⟩ := hval
  set κ : GaloBase.V F p := (D.val u)⁻¹ • u with hκdef
  have hκU : κ ∈ ResidueCupData.plane (k := ZMod p) a1 a2 := Submodule.smul_mem _ _ hu
  have hκval : D.val κ = 1 := by
    simp only [hκdef, map_smul, smul_eq_mul, hvu]
    field_simp
  -- ② `γ ∈ U ∩ \ker\bar v`，`γ ≠ 0`
  have hfin := finrank_ker_restrict_plane_eq_one_general (F := F) (p := p) (x := a1) (y := a2)
    (val := D.val) (hval := hval') hp2 hne
  have hpos : 0 < Module.finrank (ZMod p) ↥(LinearMap.ker
      (D.val.comp (ResidueCupData.plane (k := ZMod p) a1 a2).subtype)) := by omega
  haveI : Nontrivial ↥(LinearMap.ker
      (D.val.comp (ResidueCupData.plane (k := ZMod p) a1 a2).subtype)) :=
    Module.nontrivial_of_finrank_pos hpos
  obtain ⟨γc, hγc⟩ := exists_ne (0 : ↥(LinearMap.ker
    (D.val.comp (ResidueCupData.plane (k := ZMod p) a1 a2).subtype)))
  -- `γ : V`，`γ ∈ U`，`D.val γ = 0`，`γ ≠ 0`
  have hγU : ((γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)) : GaloBase.V F p)
      ∈ ResidueCupData.plane (k := ZMod p) a1 a2 :=
    (γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)).2
  have hγker : D.val ((γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)) : GaloBase.V F p) = 0 :=
    LinearMap.mem_ker.mp γc.2
  have hγne : ((γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)) : GaloBase.V F p) ≠ 0 := by
    intro h0
    apply hγc
    exact Subtype.ext (Subtype.ext h0)
  -- `γ = infl γ₀`
  obtain ⟨γ₀, hγ₀⟩ := LinearMap.mem_range.mp (by
    rw [← HenselResidueData.ker_val_eq_range_infl (F := F) (p := p) D]
    exact hγker)
  -- ③ 对 `x ∈ U^⊥`
  refine eq_bot_iff.mpr ?_
  intro x hx
  rw [Submodule.mem_bot]
  -- 分解 `x = infl x₀ + m·π`
  obtain ⟨x₀, m, hx₀⟩ := D.split x
  -- ④ 与 `γ` 正交 ⟹ `m = 0`
  have hxγ : GaloBase.cup (K := F) (p := p) x
      ((γc : ↥(ResidueCupData.plane (k := ZMod p) a1 a2)) : GaloBase.V F p) = 0 :=
    cup_eq_zero_of_mem_orth (F := F) (p := p) hx hγU
  have htm : m = 0 := by
    rw [hx₀, ← hγ₀] at hxγ
    have h := congrArg D.res hxγ
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      D.tame_uu x₀ γ₀, zero_add, map_zero] at h
    -- `h : m • D.res (cup π (infl γ₀)) = 0`
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
  -- ⑤ `x = infl x₀`，再与 `κ` 正交 ⟹ `x₀ = 0`
  have hx1 : x = D.infl x₀ := by rw [hx₀, htm, zero_smul, add_zero]
  have hxκ : GaloBase.cup (K := F) (p := p) x κ = 0 :=
    cup_eq_zero_of_mem_orth (F := F) (p := p) hx hκU
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

/-! ## 论文真实对象上的实例化（`D` 由 `Hyp139.henselResidueDataOfCup` 构造） -/

/-- **`lem:ramified-vanishing`（论文 4.2）—— 按论文原证明路线**，真实对象版：
`(a_1)\cup(a_2)\ne0` ＋ `\bar v|_U\ne0` ⟹ `U^\perp=0`。 -/
-- @source file=raw/L20261018.tex locator=line:1608 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem ramified_vanishing_paper_route (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : Fˣ}
    (hne : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2),
      valLin F p hp u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p))
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) = ⊥ := by
  have hp2' : NeZero (2 : ZMod p) := Assemble36.neZero_two_zmod (p := p) hp2
  exact orth_eq_bot_paper_route (F := F) (p := p)
    (henselResidueDataOfCup (F := F) (p := p) hp hp2' (hπ := hπ) hpu hne)
    hp2' hne hval

end L20261018
#print axioms L20261018.cup_eq_zero_of_mem_orth
#print axioms L20261018.HenselResidueData.ker_val_eq_range_infl
#print axioms L20261018.finrank_ker_restrict_plane_eq_one_general
#print axioms L20261018.orth_eq_bot_paper_route
#print axioms L20261018.ramified_vanishing_paper_route
