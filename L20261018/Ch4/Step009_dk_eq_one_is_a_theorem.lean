import L20261018.Ch4.Step008_rank_contradiction_single_phi

/-!
# R992：**`d_K = 1` 是定理** —— T5 的最后一条假设 `hK1` 解除

收口报告 `S25-CLOSURE.md` ③ 曾把 `hK1`（论文的「若 `d_K = 1`」）登记为**保留的论文假设**，
并把消去它的代价记为「需 `finrank H¹ = 2` ⟹ Kummer 同构 `H¹(F,μ_p) ≅ Fˣ/Fˣ^p` 的 `p²` 阶」
（当时的 `∅-formalization-gap`）。**本文件表明那条估计错了 —— 走的是两个便宜的方向：**

* **上界 `finrank (ker \bar v) ≤ 1`**：`Hyp134.ker_dependent`（`ker` 内任两元线性相关）＋ `finrank_le_one_iff`。
* **下界 `≥ 1`**：`Hyp137.exists_cup_pi_ne_zero` 直接给一个 `γ ∈ ker` 且 `cup γ π ≠ 0`，
  故 `γ ≠ 0` ⟹ `ker ≠ ⊥`。（**这就是全部**：不需要 Kummer 同构、不需要剩余域、不需要 `μ_{q-1}`。）

**⟹ `finrank (ker \bar v) = 1` 无条件成立**（在 `hne`／`hpu`／`hp2` ＋ 有限维下），
故 T5 与论文末句矛盾的**全部**假设只剩论文自带的 `hne`／`hval`／`hpu` 与本战役的 `hp2`。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-! ## 1. `ker \bar v` 非零（由 `Φ := cup (·) π` 非零） -/

/-- **`ker \bar v` 含非零元**：`Hyp137` 给出 `γ ∈ ker` 使 `cup γ π ≠ 0`，
故 `γ ≠ 0`（`cup 0 π = 0`）。 -/
theorem exists_ne_zero_mem_ker (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0) :
    ∃ γ : ↥(LinearMap.ker (valLin F p hp)), (γ : GaloBase.V F p) ≠ 0 := by
  obtain ⟨π, hπ⟩ := TauCeti.exists_isUniformizer F
  rw [TauCeti.isUniformizer_def] at hπ
  obtain ⟨γ, hγ⟩ := exists_cup_pi_ne_zero (F := F) (p := p) hp hp2 (hπ := hπ) hpu hne
  refine ⟨γ, ?_⟩
  intro h0
  apply hγ
  rw [h0, LinearMap.map_zero, LinearMap.zero_apply]

/-! ## 2. `finrank (ker \bar v) = 1`（论文的 `d_K = 1`） -/

/-- **上界**：`ker \bar v` 至多 1 维。

由 `Hyp134.ker_dependent`（任两元相关）＋ `finrank_le_one_iff`：
取非零的 `γ ∈ ker`，任一 `w ∈ ker` 与 `γ` 相关 ⟹ `w` 是 `γ` 的倍数
（若 `γ = c·w` 则 `c ≠ 0`，故 `w = c⁻¹·γ`）。 -/
theorem finrank_ker_valLin_le_one (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    Module.finrank (ZMod p) ↥(LinearMap.ker (valLin F p hp)) ≤ 1 := by
  obtain ⟨π, hπ⟩ := TauCeti.exists_isUniformizer F
  rw [TauCeti.isUniformizer_def] at hπ
  obtain ⟨γ, hγne⟩ := exists_ne_zero_mem_ker (F := F) (p := p) hp hp2 hpu hne
  rw [finrank_le_one_iff]
  refine ⟨γ, ?_⟩
  intro w
  rcases ker_dependent (F := F) (p := p) hp (hπ := hπ) hpu
    (w : GaloBase.V F p) (γ : GaloBase.V F p) w.2 γ.2 with h | h
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    exact ⟨c, Subtype.ext (by rw [Submodule.coe_smul]; exact hc)⟩
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hc
      exact hγne hc.symm
    refine ⟨c⁻¹, Subtype.ext ?_⟩
    rw [Submodule.coe_smul, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- **`finrank (ker \bar v) = 1`** —— 论文的 `d_K = 1`，在 `VK := ↥(ker \bar v)` 下**无条件成立**。

（上界 `≤ 1` 由 `ker_dependent`；下界 `≥ 1` 由非零元，经 `Module.finrank_pos_iff`。） -/
theorem finrank_ker_valLin_eq_one (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    Module.finrank (ZMod p) ↥(LinearMap.ker (valLin F p hp)) = 1 := by
  have hle := finrank_ker_valLin_le_one (F := F) (p := p) hp hp2 hpu hne
  have hpos : 0 < Module.finrank (ZMod p) ↥(LinearMap.ker (valLin F p hp)) := by
    rw [Module.finrank_pos_iff]
    obtain ⟨γ, hγne⟩ := exists_ne_zero_mem_ker (F := F) (p := p) hp hp2 hpu hne
    exact ⟨γ, 0, fun h => hγne (by simpa using congrArg Subtype.val h)⟩
  omega

/-! ## 3. **T5 最后一条假设解除**（`hK1` 不再出现） -/

/-- **T5 的最终形态**：`rank(Φ) = 2 ∧ d_F = 2`，**`hK1` 已解除**。

剩余假设：论文自带的 `hne`（`(a₁)∪(a₂)≠0`）、`hval`（`v|_U≠0`）、`hpu`（`char K ≠ p`），
本战役的 `hp2`（`p ≠ 2`），以及 `[FiniteDimensional (ZMod p) H¹]`（论文 4.4 开头明写 `d_F < ∞`）。 -/
theorem corollary_4_4_uncond' (hp : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2),
      valLin F p hp (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    [FiniteDimensional (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))] :
    Module.finrank (ZMod p)
        ↥(ResidueCupData.commonCupMap (Theo352.cupLin (F := F) (p := p))
          (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a2)).range = 2
      ∧ Module.finrank (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) = 2 := by
  haveI := Assemble36.neZero_two_zmod (p := p) hp2
  haveI : FiniteDimensional (ZMod p) (GaloBase.V F p) :=
    FiniteDimensional.of_surjective (theta1 (F := F) p).symm.toLinearMap
      (theta1 (F := F) p).symm.surjective
  exact corollary_4_4_uncond (F := F) (p := p) hp hp2 hpu hne hval
    (finrank_ker_valLin_eq_one (F := F) (p := p) hp
      (Assemble36.neZero_two_zmod (p := p) hp2) hpu
      (cup_kummerClass_ne_zero (F := F) (p := p) hp hne))

/-- **`d_F = 2`**（T5 的第二个分量，`hK1` 已解除）：`finrank (H¹_abs) = 2`。 -/
theorem finrank_H1_eq_two (hp : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2),
      valLin F p hp (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    [FiniteDimensional (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))] :
    Module.finrank (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) = 2 :=
  (corollary_4_4_uncond' (F := F) (p := p) hp hp2 hpu hne hval).2

/-- **`finrank (GaloBase.V) = 2`**（同一事实的另一载体）：由 `Θ₁` 搬运。 -/
theorem finrank_V_eq_two (hp : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2),
      valLin F p hp (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    [FiniteDimensional (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))] :
    Module.finrank (ZMod p) (GaloBase.V F p) = 2 := by
  rw [(theta1 (F := F) p).finrank_eq]
  exact finrank_H1_eq_two (F := F) (p := p) hp hp2 hpu hne hval

/-! ## 4. 论文末句矛盾的**最终形态**（`hK1` 已解除） -/

/-- **`raw/L20261018.tex:1646` 末句的矛盾（最终形态）**：
`v|_U ≠ 0` ＋ `ind(D) = p²` ⟹ `False`。**`D` 与 `hK1`（`d_K = 1`）都不再是假设。** -/
-- @source file=raw/L20261018.tex locator=line:1646 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
theorem corollary_4_4_contradiction_uncond' (hp : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2),
      valLin F p hp (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    [FiniteDimensional (ZMod p) (H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))]
    (b1 b2 : GaloBase.V F p)
    (hD : H2Bridge.indOfH2 (p := p) (K := F) (KummerBridge.primitiveRoot_spec F p)
      (GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1) b1
        + GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a2) b2) = p ^ 2) :
    False := by
  haveI := Assemble36.neZero_two_zmod (p := p) hp2
  haveI : FiniteDimensional (ZMod p) (GaloBase.V F p) :=
    FiniteDimensional.of_surjective (theta1 (F := F) p).symm.toLinearMap
      (theta1 (F := F) p).symm.surjective
  exact corollary_4_4_contradiction_uncond (F := F) (p := p) hp hp2 hpu hne hval
    (finrank_ker_valLin_eq_one (F := F) (p := p) hp
      (Assemble36.neZero_two_zmod (p := p) hp2) hpu
      (cup_kummerClass_ne_zero (F := F) (p := p) hp hne))
    b1 b2 hD

end L20261018
#print axioms L20261018.exists_ne_zero_mem_ker
#print axioms L20261018.finrank_ker_valLin_le_one
#print axioms L20261018.finrank_ker_valLin_eq_one
#print axioms L20261018.corollary_4_4_uncond'
#print axioms L20261018.finrank_H1_eq_two
#print axioms L20261018.finrank_V_eq_two
#print axioms L20261018.corollary_4_4_contradiction_uncond'
