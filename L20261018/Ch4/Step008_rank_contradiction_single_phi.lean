import L20261018.Ch4.Step007_corollary_four_four_no_d

/-!
# R991：**`∅-carrier-bridge` 消除 —— 论文「`rankΦ=2` 与 `rankΦ≥3` 矛盾」在同一 `Φ` 上合成**

收口报告 `S25-CLOSURE.md` ② 第 2 条曾登记一个**非数学**的残留：T4(2)（`thm:ramified`(2)）落在
`GaloBase` 载体，T5（`:1646` 推论）落在显式载体 `H1`，故论文末句的**矛盾**不能直接合成。
本文件把两个 `Φ` 的**值域**沿 `Θ₁`／`Θ₂` 搬运，弥合该残留。

## 机制（一处等式，其余是 `Submodule` 簿记）

`Hyp145.cup_compat_theta` ＋ `theta1_kummerClass` 给出**交换方块**

    (Θ₂ × Θ₂) ∘ Φ_Galo = Φ_exp ∘ Θ₁

其中
`Φ_Galo w = (w ∪ kc₁, w ∪ kc₂)`（`GaloBase` 载体，`kc_i = kummerClass a_i`），
`Φ_exp v = (v ∪ k₁', v ∪ k₂')`（显式载体，`k_i' = kummerExplicit a_i`）。
`Θ₁ = h1ToVEquiv.symm` 满射 ⟹ `(Θ₂×Θ₂)(range Φ_Galo) = range Φ_exp` ⟹
`finrank`／`Module.rank` 相等（`LinearEquiv.finrank_map_eq`／`submoduleMap`）。

## 结论（论文 `raw/L20261018.tex:1646` 末句）

`d_K = 1`（＋ `v|_U ≠ 0`）⟹ `rank Φ = 2`；而 `ind(D) = p²` ⟹ `rank Φ ≥ 3`。**矛盾。**
本文件给出 `False`，且**不含 `D`**（两端分别由 `Hyp145`／`Hyp146` 供 `D` 的实例）。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

section Bridge

variable (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
  (hne : Theo352.cupLin (F := F)
    (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
    (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)

/-- **交换方块（点态）**：`(Θ₂×Θ₂) (Φ_Galo w) = Φ_exp (Θ₁ w)`。

两侧都用 `cup_compat_theta` ＋ `theta1_kummerClass` 展开；
`Θ₁(kummerClass a_i) = kummerExplicit a_i` 是本式的关键（Kummer 类的桥，`Hyp140`／`Hyp145`）。 -/
theorem Bex_Phi_theta (w : GaloBase.V F p) :
    ((theta2 (F := F) p).prodCongr (theta2 (F := F) p))
        ((biKummerDataKummer F p hp a1 a2
          (cup_kummerClass_ne_zero (F := F) (p := p) hp hne)).Phi w)
      = (Theo352.Bex (F := F) (p := p) hp hne).Phi (theta1 (F := F) p w) := by
  refine Prod.ext ?_ ?_
  · show theta2 (F := F) p
        (GaloBase.cup (K := F) (p := p) w (KummerBridge.kummerClass F p hp a1))
      = Theo352.cupLin (F := F) (p := p) (theta1 (F := F) p w)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
    rw [cup_compat_theta, theta1_kummerClass]
  · show theta2 (F := F) p
        (GaloBase.cup (K := F) (p := p) w (KummerBridge.kummerClass F p hp a2))
      = Theo352.cupLin (F := F) (p := p) (theta1 (F := F) p w)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a2)
    rw [cup_compat_theta, theta1_kummerClass]

/-- 交换方块（线性映射等式）。 -/
theorem phi_comp :
    (((theta2 (F := F) p).prodCongr (theta2 (F := F) p)).toLinearMap).comp
        (biKummerDataKummer F p hp a1 a2
          (cup_kummerClass_ne_zero (F := F) (p := p) hp hne)).Phi
      = (Theo352.Bex (F := F) (p := p) hp hne).Phi.comp
          (theta1 (F := F) p).toLinearMap := by
  refine LinearMap.ext fun w => ?_
  exact Bex_Phi_theta (F := F) (p := p) hp hne w

/-- **值域搬运**：`(Θ₂×Θ₂) (range Φ_Galo) = range Φ_exp`（`Θ₁` 满射）。 -/
theorem phi_range_map :
    Submodule.map ((theta2 (F := F) p).prodCongr (theta2 (F := F) p)).toLinearMap
        (biKummerDataKummer F p hp a1 a2
          (cup_kummerClass_ne_zero (F := F) (p := p) hp hne)).Phi.range
      = (Theo352.Bex (F := F) (p := p) hp hne).Phi.range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨y, hy⟩ := (LinearMap.mem_range
      (f := (biKummerDataKummer F p hp a1 a2
        (cup_kummerClass_ne_zero (F := F) (p := p) hp hne)).Phi)).mp hw
    refine LinearMap.mem_range.mpr ⟨theta1 (F := F) p y, ?_⟩
    rw [← hy]
    exact (Bex_Phi_theta (F := F) (p := p) hp hne y).symm
  · rintro _ ⟨v, rfl⟩
    refine Submodule.mem_map.mpr ⟨(biKummerDataKummer F p hp a1 a2
      (cup_kummerClass_ne_zero (F := F) (p := p) hp hne)).Phi ((theta1 (F := F) p).symm v),
      LinearMap.mem_range_self _ _, ?_⟩
    exact (Bex_Phi_theta (F := F) (p := p) hp hne ((theta1 (F := F) p).symm v)).trans
      (by rw [LinearEquiv.apply_symm_apply])

/-- **`finrank` 搬运**：两载体的 `Φ` 值域同维。 -/
theorem finrank_range_eq :
    Module.finrank (ZMod p)
        ↥(biKummerDataKummer F p hp a1 a2
          (cup_kummerClass_ne_zero (F := F) (p := p) hp hne)).Phi.range
      = Module.finrank (ZMod p) ↥(Theo352.Bex (F := F) (p := p) hp hne).Phi.range := by
  rw [← phi_range_map (F := F) (p := p) hp hne]
  exact (LinearEquiv.finrank_map_eq ((theta2 (F := F) p).prodCongr (theta2 (F := F) p)) _).symm

/-- **`Module.rank` 搬运**：两载体的 `Φ` 值域同秩。 -/
theorem rank_range_eq :
    Module.rank (ZMod p)
        ↥(biKummerDataKummer F p hp a1 a2
          (cup_kummerClass_ne_zero (F := F) (p := p) hp hne)).Phi.range
      = Module.rank (ZMod p) ↥(Theo352.Bex (F := F) (p := p) hp hne).Phi.range := by
  rw [← phi_range_map (F := F) (p := p) hp hne]
  exact LinearEquiv.rank_eq (((theta2 (F := F) p).prodCongr (theta2 (F := F) p)).submoduleMap _)

end Bridge

/-! ## 论文末句的矛盾（`D` 已消失） -/

/-- **`raw/L20261018.tex:1646` 末句的矛盾形态**：`d_K = 1`（`hK1`）＋ `ind(D) = p²`（`hD`）
⟹ `rankΦ = 2`（T5，`corollary_4_4_uncond`）与 `rankΦ ≥ 3`（T4(2)，`thm_ramified_2`）
在同一 `Φ` 上冲突 ⟹ `False`。**`D` 已消失**（两端各自由 `Hyp145`／`Hyp146` 构造）。 -/
-- @source file=raw/L20261018.tex locator=line:1646 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
theorem corollary_4_4_contradiction_uncond (hp : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2),
      valLin F p hp (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    (hK1 : Module.finrank (ZMod p) ↥(LinearMap.ker (valLin F p hp)) = 1)
    [FiniteDimensional (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))]
    (b1 b2 : GaloBase.V F p)
    (hD : H2Bridge.indOfH2 (p := p) (K := F) (KummerBridge.primitiveRoot_spec F p)
      (GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1) b1
        + GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a2) b2) = p ^ 2) :
    False := by
  -- T4(2)：`rank Φ_Galo ≥ 3`
  have h3 : (3 : Cardinal) ≤ Module.rank (ZMod p)
      ↥(biKummerDataKummer F p hp a1 a2
        (cup_kummerClass_ne_zero (F := F) (p := p) hp hne)).Phi.range :=
    thm_ramified_2 (F := F) (p := p) hp hp2
      (cup_kummerClass_ne_zero (F := F) (p := p) hp hne) b1 b2 hD
  -- T5：`finrank Φ_exp = 2`（`corollary_4_4_uncond` 的 `Φ` 是 `commonCupMap`，先用 `rfl` 级等式换口径）
  obtain ⟨h2, _⟩ := corollary_4_4_uncond (F := F) (p := p) hp hp2 hpu hne hval hK1
  have h2B : Module.finrank (ZMod p) ↥(Theo352.Bex (F := F) (p := p) hp hne).Phi.range = 2 := by
    rw [Bex_Phi_eq_commonCupMap (F := F) (p := p) hp hne]
    exact h2
  have h2' : Module.rank (ZMod p) ↥(Theo352.Bex (F := F) (p := p) hp hne).Phi.range
      = (2 : Cardinal) := by
    rw [← Module.finrank_eq_rank' (K := ZMod p)
      (V := ↥(Theo352.Bex (F := F) (p := p) hp hne).Phi.range), h2B]
    norm_num
  rw [rank_range_eq (F := F) (p := p) hp hne, h2'] at h3
  exact absurd h3 (by norm_num)

end L20261018
#print axioms L20261018.Bex_Phi_theta
#print axioms L20261018.phi_comp
#print axioms L20261018.phi_range_map
#print axioms L20261018.finrank_range_eq
#print axioms L20261018.rank_range_eq
#print axioms L20261018.corollary_4_4_contradiction_uncond
