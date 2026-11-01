import L20261018.Hyp132
import L20261018.Hyp123

/-!
# R976：`hdep` 的最后一段（域论抬回）—— 单位类的幂依赖性

R975 在剩余域单位群里得到「任两元成幂关系（模 `p` 次幂）」（`Hyp132`）。
本文件把它**抬回 `Fˣ`**：

**`unit_pow_dependence`**：`u, w ∈ U(F,0) = unitFiltration F 0`（即单位）⟹
**或** `w` 本身是 `p` 次幂，**或** 存在 `n` 使 `u · w⁻ⁿ` 是 `p` 次幂。

桥接三件（皆已定位）：
- `unitFiltrationZeroEquivIntegerUnits : unitFiltration F 0 ≃* 𝒪[F]ˣ`
  （`UnitFiltration/Basic.lean:346`，底层元素不动：`coe_unitFiltrationZeroEquivIntegerUnits`）；
- `Hyp114.unitPow_iff_residuePow`：`𝒪[F]ˣ` 中 `p` 次幂 ⟺ 剩余中 `p` 次幂；
- `Hyp132.residue_exists_mul_pow_inv_mem_range`：剩余侧任两元成幂关系。

下一步（R977）：用 `KummerV.kummerClass_mul` ＋ `kummerClass_pow` 把它翻成 `kc u = n • kc w`，
即 `hdep`；再由 `Hyp130.hUU_of_ker_le_one` 得 `hUU`。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime]

/-- **单位类的幂依赖性（模 `p` 次幂）**：`u, w` 是同余 `1` 的单位 ⟹
`w` 是 `p` 次幂，或 `∃ n, u · w⁻ⁿ` 是 `p` 次幂。 -/
theorem unit_pow_dependence (hpu : IsUnit (p : 𝒪[F])) {u w : Fˣ}
    (hu : u ∈ unitFiltration F 0) (hw : w ∈ unitFiltration F 0) :
    w ∈ (powMonoidHom p : Fˣ →* Fˣ).range ∨
      ∃ n : ℕ, u * (w ^ n)⁻¹ ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
  classical
  -- 把 `u, w` 看作 `𝒪[F]ˣ` 的元素
  set u₀ : 𝒪[F]ˣ := unitFiltrationZeroEquivIntegerUnits ⟨u, hu⟩ with hu₀
  set w₀ : 𝒪[F]ˣ := unitFiltrationZeroEquivIntegerUnits ⟨w, hw⟩ with hw₀
  have hu₀coe : Units.map (Subring.subtype 𝒪[F]) u₀ = u := by
    ext
    rfl
  have hw₀coe : Units.map (Subring.subtype 𝒪[F]) w₀ = w := by
    ext
    rfl
  by_cases hwr : Units.map (IsLocalRing.residue 𝒪[F]) w₀ ∈
      (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range
  · -- `w` 本身是 `p` 次幂
    left
    rw [← hw₀coe]
    exact (unitPow_iff_residuePow (F := F) hpu w₀).mpr hwr
  · -- 否则用剩余侧的幂关系
    right
    obtain ⟨n, hn⟩ := residue_exists_mul_pow_inv_mem_range (F := F) p
      (Units.map (IsLocalRing.residue 𝒪[F]) u₀)
      (Units.map (IsLocalRing.residue 𝒪[F]) w₀) hwr
    refine ⟨n, ?_⟩
    have hres : Units.map (IsLocalRing.residue 𝒪[F]) (u₀ * (w₀ ^ n)⁻¹) ∈
        (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range := by
      rw [map_mul, map_inv, map_pow]
      exact hn
    have hlift := (unitPow_iff_residuePow (F := F) hpu (u₀ * (w₀ ^ n)⁻¹)).mpr hres
    rwa [map_mul, map_inv, map_pow, hu₀coe, hw₀coe] at hlift

end L20261018
#print axioms L20261018.unit_pow_dependence
