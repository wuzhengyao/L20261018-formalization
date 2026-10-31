import Hyp148

/-!
# R998：**逐字 100% 第 1 步 —— 4.1/4.2 之间过渡段的两句 ＋ 一句前提**（论文 `:1600–1601`）

论文在 `lem:basis-change` 与 `lem:ramified-vanishing` 之间有一段**无编号但承重**的归约：

> 若模 `p` 赋值映射 `\bar v:U\to\Fp` 非零，则 `\ker\bar v` 为一维。可选取 `U` 的基 `\gamma_1,\gamma_2`，
> 使 `\bar v(\gamma_1)=1`、`\bar v(\gamma_2)=0`。… 由命题~\ref{prop:prelim-kummer-valuation}，
> 非零类 `\gamma_2=(c)` 的剩余类 `(\bar c)\in H^1(K,\mu_p)` 也非零。

本文件机检其中三件（"基的选取"= 纯线性代数，见 §4 说明）：

| 论文断言 | 本文件 |
|---|---|
| （隐含）`U` 的生成元线性无关 ⟹ `\dim U=2` | **`pair_linearIndependent`**、**`finrank_plane_eq_two`** |
| `\bar v\|_U` 非零 ⟹ `\ker(\bar v\|_U)` 一维 | **`finrank_ker_restrict_plane_eq_one`** |
| 单位类 `(c)\ne0` ⟹ 其剩余类 `(\bar c)\ne0` | **`residue_not_pow_of_kummerClass_ne_zero`** ＋ `kummerClass_pair_linearIndependent` 等实例化 |

**为什么承重**：论文 4.2 证明的第一行就用 `(\bar c)\ne0` 把 `k(\bar c)=0` 化成 `k=0`；
若它不成立，4.2 的证明断在第一步。（本战役此前以 `\ker\bar v` ≤ 1 维 ＋ 交错性绕开该路线，
故这三句一直未形式化 —— 本文件正是"逐字"所缺的那块。）
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-! ## 1. 抽象层：`x, y` 的独立性与 `span{x,y}` 的维数 -/

/-- **`x, y` 线性无关**（由 `x∪y ≠ 0` ＋ 交替性 `x∪x = 0`）。

若 `s•x + t•y = 0`，两边与 `y` 作杯积得 `s•(x∪y) = 0`（`y∪y=0`）⟹ `s=0`；代回得 `t•y = 0`，
再由 `y ≠ 0` 得 `t = 0`。 -/
theorem pair_linearIndependent (hp2 : NeZero (2 : ZMod p)) {x y : GaloBase.V F p}
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
      cup_self (F := F) (p := p) hp2, smul_zero, add_zero] at h
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

/-- **`span{x,y}` 二维**（`x∪y ≠ 0` 时）。 -/
theorem finrank_plane_eq_two (hp2 : NeZero (2 : ZMod p)) {x y : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) x y ≠ 0) :
    Module.finrank (ZMod p) ↥(ResidueCupData.plane (k := ZMod p) x y) = 2 := by
  have hli := pair_linearIndependent (F := F) (p := p) hp2 hne
  have hrange : (Set.range ![x, y] : Set (GaloBase.V F p)) = {x, y} := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hspan : ResidueCupData.plane (k := ZMod p) x y
      = Submodule.span (ZMod p) (Set.range ![x, y]) := by
    rw [ResidueCupData.plane, hrange]
  rw [hspan, finrank_span_eq_card hli]
  simp

/-! ## 2. `\ker(\bar v|_U)` 一维（论文 `:1600` 第一句） -/

/-- **`\ker(\bar v|_U)` 一维**：`\bar v|_U \ne 0` ＋ `\dim U = 2` ⟹ 核一维（秩–零化度）。

非零线性泛函 `U \to \F_p` 满射（`\F_p` 一维：`f x ≠ 0` 时 `c = (c/(f x)) • f x`），
故 `\dim\ker = \dim U - 1 = 1`。 -/
-- @source file=raw/L20261018.tex locator=line:1596 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $\ker\bar v$ 为一维。"
theorem finrank_ker_restrict_plane_eq_one (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    {x y : GaloBase.V F p} (hne : GaloBase.cup (K := F) (p := p) x y ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) x y, valLin F p hp u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    Module.finrank (ZMod p) ↥(LinearMap.ker
      ((valLin F p hp).comp (ResidueCupData.plane (k := ZMod p) x y).subtype)) = 1 := by
  have hφne : ((valLin F p hp).comp (ResidueCupData.plane (k := ZMod p) x y).subtype) ≠ 0 := by
    obtain ⟨u, hu, hvu⟩ := hval
    intro h
    apply hvu
    have hz : ((valLin F p hp).comp (ResidueCupData.plane (k := ZMod p) x y).subtype)
        ⟨u, hu⟩ = 0 := by
      rw [h, LinearMap.zero_apply]
    simpa using hz
  have hsurj : Function.Surjective
      ((valLin F p hp).comp (ResidueCupData.plane (k := ZMod p) x y).subtype) := by
    intro c
    have hx : ∃ z : ↥(ResidueCupData.plane (k := ZMod p) x y),
        ((valLin F p hp).comp (ResidueCupData.plane (k := ZMod p) x y).subtype) z ≠ 0 := by
      by_contra h
      push_neg at h
      exact hφne (LinearMap.ext h)
    obtain ⟨z, hz⟩ := hx
    refine ⟨(c / ((valLin F p hp).comp (ResidueCupData.plane (k := ZMod p) x y).subtype z)) • z, ?_⟩
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ c hz
  have hrange1 : Module.finrank (ZMod p) ↥(LinearMap.range
      ((valLin F p hp).comp (ResidueCupData.plane (k := ZMod p) x y).subtype)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj,
      (Submodule.topEquiv (R := ZMod p) (M := ZMod p)).finrank_eq, Module.finrank_self]
  have hrn := LinearMap.finrank_range_add_finrank_ker
    ((valLin F p hp).comp (ResidueCupData.plane (k := ZMod p) x y).subtype) (V₂ := ZMod p)
  have hplane : Module.finrank (ZMod p) ↥(ResidueCupData.plane (k := ZMod p) x y) = 2 :=
    finrank_plane_eq_two (F := F) (p := p) hp2 hne
  rw [hrange1, hplane] at hrn
  omega

/-! ## 3. `(\bar c) \ne 0`：单位类的剩余类非零（论文 `:1601` 第三句） -/

/-- **论文 `:1601` 第三句**：单位 `c` 的 Kummer 类非零 ⟹ 其余 `\bar c` 不是 `K` 中的 `p` 次幂
（即 `(\bar c)\ne 0`，`H^1(K,\mu_p)` 的 Kummer 单射性）。

用 `prop:prelim-kummer-valuation`(1) 的**逐点判据**（`Hyp114.unitPow_iff_residuePow`）。 -/
-- @source file=raw/L20261018.tex locator=line:1599 quote="由命题~\ref{prop:prelim-kummer-valuation}，非零类 $\gamma_2=(c)$ 的剩余类 $(\bar c)\in H^1(K,\mu_p)$ 也非零。"
theorem residue_not_pow_of_kummerClass_ne_zero (hp : IsUnit (p : F)) (hpu : IsUnit (p : 𝒪[F]))
    {u : Fˣ} (hu : u ∈ unitFiltration F 0)
    (hne : KummerBridge.kummerClass F p hp u ≠ 0) :
    Units.map (IsLocalRing.residue 𝒪[F]) (unitFiltrationZeroEquivIntegerUnits ⟨u, hu⟩)
      ∉ (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range := by
  have hnotF : u ∉ (powMonoidHom p : Fˣ →* Fˣ).range := by
    intro hmem
    exact hne ((KummerBridge.kummerClass_eq_zero_iff (F := F) (p := p) hp u).mpr hmem)
  have hcoe : Units.map (Subring.subtype 𝒪[F]) (unitFiltrationZeroEquivIntegerUnits ⟨u, hu⟩) = u := by
    ext
    rfl
  intro hres
  apply hnotF
  rw [← hcoe]
  exact (unitPow_iff_residuePow (F := F) hpu
    (unitFiltrationZeroEquivIntegerUnits ⟨u, hu⟩)).mpr hres

/-! ## 4. 论文真实对象的实例化（`(a_1),(a_2)` 与其平面 `U`） -/

/-- **`(a₁),(a₂)` 线性无关**（论文过渡段隐含的"`U` 二维"）。 -/
theorem kummerClass_pair_linearIndependent (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    {a1 a2 : Fˣ}
    (hne : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0) :
    LinearIndependent (ZMod p)
      ![KummerBridge.kummerClass F p hp a1, KummerBridge.kummerClass F p hp a2] :=
  pair_linearIndependent (F := F) (p := p) hp2 hne

/-- **`U = span{(a₁),(a₂)}` 二维**（论文过渡段）。 -/
theorem finrank_plane_kummerClass_eq_two (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    {a1 a2 : Fˣ}
    (hne : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0) :
    Module.finrank (ZMod p) ↥(ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2)) = 2 :=
  finrank_plane_eq_two (F := F) (p := p) hp2 hne

/-- **`\ker(\bar v|_U)` 一维**（论文 `:1600` 第一句，真实对象）。 -/
theorem finrank_ker_restrict_plane_kummerClass_eq_one (hp : IsUnit (p : F))
    (hp2 : NeZero (2 : ZMod p)) {a1 a2 : Fˣ}
    (hne : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2),
      valLin F p hp u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    Module.finrank (ZMod p) ↥(LinearMap.ker
      ((valLin F p hp).comp (ResidueCupData.plane (k := ZMod p)
        (KummerBridge.kummerClass F p hp a1)
        (KummerBridge.kummerClass F p hp a2)).subtype)) = 1 :=
  finrank_ker_restrict_plane_eq_one (F := F) (p := p) hp hp2 hne hval

end L20261018
#print axioms L20261018.pair_linearIndependent
#print axioms L20261018.finrank_plane_eq_two
#print axioms L20261018.finrank_ker_restrict_plane_eq_one
#print axioms L20261018.residue_not_pow_of_kummerClass_ne_zero
#print axioms L20261018.finrank_ker_restrict_plane_kummerClass_eq_one
