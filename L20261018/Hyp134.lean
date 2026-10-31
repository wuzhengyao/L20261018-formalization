import Hyp133
import Hyp130

/-!
# R976（续）：**`hdep` 与 `hUU` 均为定理**

把 R975–R976 的三段拼起来：

- `Hyp122.exists_unit_rep`：`\ker\bar v` 的元素都是单位类；
- **`Hyp133.unit_pow_dependence`**：两个单位类成幂关系（模 `p` 次幂）——`w` 本身是 `p` 次幂，
  或 `∃ n, u·w⁻ⁿ` 是 `p` 次幂；
- Kummer 算术（`KummerV.kummerClass_mul`／`Hyp120.kummerClass_pow`／`kc x = 0 ↔ x ∈ (·)^p`）
  ⟹ `kc u = n • kc w` ⟹ **`hdep`**（`\ker\bar v` 内任两元线性相关）；
- **`Hyp130.hUU_of_ker_le_one`** ⟹ **`hUU`**。

⟹ `Hyp119` 的第 2 条具名假设（`hUU`）**解除**（以 `IsUnit (p : 𝒪[F])` 与 `p ≠ 2` 为条件）。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- **`hdep`**：`\ker\bar v` 内任两元线性相关。

证明：由 `exists_unit_rep` 取单位 `u, w`；`unit_pow_dependence` 给 `w ∈ (Fˣ)^p`
（则 `z = 0`，零在任何 `span` 里）或 `∃ n, u·w⁻ⁿ ∈ (Fˣ)^p`
（则 `kc u = n • kc w`，即 `y = n • z`）。 -/
theorem ker_dependent (hp : IsUnit (p : F)) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F])) :
    ∀ y z : GaloBase.V F p, valLin F p hp y = 0 → valLin F p hp z = 0 →
      y ∈ Submodule.span (ZMod p) ({z} : Set (GaloBase.V F p)) ∨
        z ∈ Submodule.span (ZMod p) ({y} : Set (GaloBase.V F p)) := by
  intro y z hy hz
  obtain ⟨u, hu, huy⟩ := exists_unit_rep (F := F) (p := p) hp (hπ := hπ) (y := y) hy
  obtain ⟨w, hw, hwz⟩ := exists_unit_rep (F := F) (p := p) hp (hπ := hπ) (y := z) hz
  have hu' : u ∈ unitFiltration F 0 :=
    (mem_unitFiltration_zero u).2 ((normalizedValuation_eq_one_iff u).1 hu)
  have hw' : w ∈ unitFiltration F 0 :=
    (mem_unitFiltration_zero w).2 ((normalizedValuation_eq_one_iff w).1 hw)
  rcases unit_pow_dependence (F := F) p hpu hu' hw' with hwpow | ⟨n, hn⟩
  · -- `w` 是 `p` 次幂 ⟹ `z = kc w = 0`，而 `0 ∈ span{y}`
    right
    have hw0 : KummerBridge.kummerClass F p hp w = 0 :=
      (KummerBridge.kummerClass_eq_zero_iff F p hp w).mpr hwpow
    have hz0 : z = 0 := by rw [← hwz, hw0]
    rw [hz0]
    exact Submodule.zero_mem _
  · -- `u·w⁻ⁿ` 是 `p` 次幂 ⟹ `kc u = n • kc w`，即 `y = n • z`
    left
    have h0 : KummerBridge.kummerClass F p hp (u * (w ^ n)⁻¹) = 0 :=
      (KummerBridge.kummerClass_eq_zero_iff F p hp (u * (w ^ n)⁻¹)).mpr hn
    -- `kc x⁻¹ = -kc x`（由 `kc` 加性 ＋ `kc 1 = 0`）
    have hinv : KummerBridge.kummerClass F p hp ((w ^ n)⁻¹)
        = -KummerBridge.kummerClass F p hp (w ^ n) := by
      have h1 : KummerBridge.kummerClass F p hp (1 : Fˣ) = 0 :=
        (KummerBridge.kummerClass_eq_zero_iff F p hp 1).mpr (one_mem _)
      have h := KummerV.kummerClass_mul (F := F) (p := p) hp (w ^ n) ((w ^ n)⁻¹)
      rw [mul_inv_cancel, h1] at h
      exact eq_neg_of_add_eq_zero_right h.symm
    rw [KummerV.kummerClass_mul, hinv, kummerClass_pow] at h0
    -- `h0 : kc u + -(n • kc w) = 0`
    have heq : KummerBridge.kummerClass F p hp u = n • KummerBridge.kummerClass F p hp w := by
      have h' : KummerBridge.kummerClass F p hp u - n • KummerBridge.kummerClass F p hp w = 0 := by
        simpa [sub_eq_add_neg] using h0
      exact sub_eq_zero.mp h'
    rw [Submodule.mem_span_singleton]
    refine ⟨(n : ZMod p), ?_⟩
    rw [Nat.cast_smul_eq_nsmul, ← huy, ← hwz]
    exact heq.symm

/-- **`hUU` 是定理**（以 `IsUnit (p : 𝒪[F])` 与 `p ≠ 2` 为条件）：
两**单位**类的杯积为零。由 `ker_dependent` ＋ `hUU_of_ker_le_one` 直接得。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="\partial_2((u)\cup(w))=0."
theorem hUU (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p)) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F])) :
    ∀ u w : Fˣ, normalizedValuation F u = 1 → normalizedValuation F w = 1 →
      GaloBase.cup (K := F) (p := p)
        (KummerBridge.kummerClass F p hp u) (KummerBridge.kummerClass F p hp w) = 0 :=
  hUU_of_ker_le_one (F := F) p hp hp2 (ker_dependent (F := F) p hp hπ hpu)

end L20261018
#print axioms L20261018.ker_dependent
#print axioms L20261018.hUU
