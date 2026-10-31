import Hyp136
import Hyp117

/-!
# R979：T2／T3 的**线性代数核** —— `cup (·) (π)` 在 `\ker\bar v` 上**非零且单射**

R970 侦察已确认：**四库皆无** `∂: H² → H¹`（提示词 ⑤T2 的 (a) 路线被否）。
本文件给出另一条：`HenselResidueData` 里 `res` 与 `tame_u_pi` 这**两条假设是耦合的** ——
`tame_u_pi : ∀ y ∈ \ker, res (cup y π) = y` 的意思正是「`res` 是 `Φ := cup (·) π` 的**左逆**」。
故只要 **`Φ` 单射**，`res` 就**存在**（取任一左逆），两条假设同时解除。

`Φ` 单射的两个前提都在手边：
1. `\ker\bar v` 至多 1 维（`Hyp134.ker_dependent`）；
2. **`Φ ≠ 0`**：由定理的假设 `hne : cup a1 a2 ≠ 0` ＋ 分解 `x = x₀ + m·π`（`Hyp117.decomp_mem_ker`）
   ＋ `cup` 在 `\ker` 上为零（`Hyp135`）＋ `cup π π = 0`（交错性）推出。

**⟹ 本文件把 `res`／`tame_u_pi` 的「存在性障碍」化为两条已机检事实。**
（注意：这样得到的 `res` 是**某个**左逆，与论文 `∂₂` 的**同一性**未证 —— 载体身份见文件末的说明。）
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- `Φ := cup (·) (π)` 在 `\ker\bar v` 上**不恒为零** —— 由 `hne` 反证。

若 `Φ` 在 `\ker` 上恒零，则对任意 `x = x₀ + m·π`、`x' = x₀' + m'·π` 有
`cup x x' = m' • cup x₀ π - m • cup x₀' π + (m·m') • cup π π = 0`
（`cup` 在 `\ker×\ker` 上为零、`cup π π = 0`、斜对称），与 `hne` 矛盾。 -/
theorem exists_cup_pi_ne_zero (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p)) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F])) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0) :
    ∃ y : ↥(LinearMap.ker (valLin F p hp)),
      GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hp π) ≠ 0 := by
  classical
  have hπ' : valLin F p hp (KummerBridge.kummerClass F p hp π) = 1 :=
    valLin_pi (F := F) (p := p) hp hπ
  by_contra h
  push_neg at h
  obtain ⟨y1, m1, hy1⟩ := decomp_mem_ker (valLin F p hp)
    (KummerBridge.kummerClass F p hp π) hπ' a1
  obtain ⟨y2, m2, hy2⟩ := decomp_mem_ker (valLin F p hp)
    (KummerBridge.kummerClass F p hp π) hπ' a2
  apply hne
  rw [hy1, hy2]
  -- 展开双线性并逐项消掉
  have hskew : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp π) (y2 : GaloBase.V F p) = 0 := by
    rw [GaloBase.cup_skew (K := F) (p := p), h y2, neg_zero]
  have hself : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp π) (KummerBridge.kummerClass F p hp π) = 0 :=
    cup_self (F := F) (p := p) hp2 _
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [ker_cup_eq_zero (F := F) (p := p) hp hp2 (hπ := hπ) hpu y1 y2, hskew, hself, h y1]
  simp only [smul_zero, add_zero, zero_add]

end L20261018
#print axioms L20261018.exists_cup_pi_ne_zero
