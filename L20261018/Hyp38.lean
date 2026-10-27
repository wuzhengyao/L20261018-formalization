import L20261018.Hyp36
/-!
# 非空实例义务（C2）：`BiKummerData` 不空洞，且第三章各条在有模型上成立

KB 规则「非空实例义务」（L1 ＋ L10①）要求：条件定理的假设类须**自带机检的非空见证**。
第三章各条在 `A.lean` 里都是 `BiKummerData k V H2` 上的条件定理，假设类还有
`[NeZero (2 : k)]`（论文的 `p` 为奇素数）。本文件给出一个**具体模型**：

* `k = ZMod 3`（故 `2 ≠ 0`：论文的「`p` 奇」），
* `V = k × k`，`H2 = k`，
* `cup` ＝ 辛形式 `x₁y₂ − x₂y₁`（双线性、斜对称），
* `a₁ = (1,0)`，`a₂ = (0,1)`，故 `cup a₁ a₂ = 1 ≠ 0`（论文的非零杯积假设）。

于是 `BiKummerData` **非空**，且 `A.lean` 的每条定理在该模型上**都有实例**——
这些 `example` 即是「不空洞」的机检证据（若某条定理的假设在生产不出，编译会失败）。

## 覆盖范围（诚实声明）

本文件见证的是 **`A.lean` 抽象层**的非空性。**`_kummer` 真实对象层**（`Hyp22`/`Hyp20` 等）
的 `hne : cup (a₁) (a₂) ≠ 0` 需要真实域上 `H²(G_F, Z/p)` 中某个杯积非零的**具体计算**，
那是数论（`Br(F)[p] ≠ 0`）；库内只有 `p = 2` 的实例（`TauCeti.card_brauerGroup_eq_two`：
`Nat.card (Br ℝ) = 2`）。该层仍记 `∅-open`，见 `STATUS.md`。
-/

open LinearMap
open scoped Cardinal

namespace L20261018

/-- 玩具杯积：二维辛形式 `x₁y₂ − x₂y₁`，双线性且斜对称。 -/
noncomputable def toyCup : (ZMod 3 × ZMod 3) →ₗ[ZMod 3] (ZMod 3 × ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
  LinearMap.mk₂ (ZMod 3) (fun x y => x.1 * y.2 - x.2 * y.1)
    (by intro x y z; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intro c x y; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (by intro x y z; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intro c x y; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

/-- `2 ≠ 0` 在 `ZMod 3` 中：论文的「`p` 为奇素数」。 -/
instance : NeZero (2 : ZMod 3) := ⟨by decide⟩

/-- **论文第三章的抽象数据有一个具体模型。** -/
noncomputable def toyBiKummer : BiKummerData (ZMod 3) (ZMod 3 × ZMod 3) (ZMod 3) where
  cup := toyCup
  a1 := (1, 0)
  a2 := (0, 1)
  hne := by
    simp [toyCup, LinearMap.mk₂_apply]
  skew := by
    intro x y
    simp only [toyCup, LinearMap.mk₂_apply]
    ring

/-- **非空见证**：`BiKummerData` 的假设类不空。 -/
theorem biKummerData_nonempty :
    Nonempty (BiKummerData (ZMod 3) (ZMod 3 × ZMod 3) (ZMod 3)) :=
  ⟨toyBiKummer⟩

/-! ### 各条定理在该模型上的实例（「不空洞」的机检证据） -/

/-- 3.1(1) 在玩具模型上有实例。 -/
example : toyBiKummer.U ⊓ toyBiKummer.Uperp = ⊥ := toyBiKummer.lemma_3_1_1

/-- 3.1(3) 在玩具模型上有实例：`rank Φ ≥ 2`。 -/
example : (2 : Cardinal) ≤ Module.rank (ZMod 3) ↥toyBiKummer.Phi.range :=
  toyBiKummer.lemma_3_1_3

/-- 3.3(1) 在玩具模型上有实例（`hNrd` 取该模型上的平凡情况）。 -/
example : LinearMap.range (0 : (ZMod 3 × ZMod 3) →ₗ[ZMod 3] (ZMod 3 × ZMod 3))
    ≤ (⊤ : Submodule (ZMod 3) (ZMod 3 × ZMod 3)) :=
  BiKummerData.lemma_3_3_1 (k := ZMod 3)
    (0 : (ZMod 3 × ZMod 3) →ₗ[ZMod 3] (ZMod 3 × ZMod 3))
    (⊤ : Submodule (ZMod 3) (ZMod 3 × ZMod 3)) (fun _ => Submodule.mem_top)

/-- `U` 在其模型上确实**非零**（`⟨(1,0),(0,1)⟩` 是二维的）：`a₁ ≠ 0`。 -/
example : toyBiKummer.a1 ≠ 0 := by
  simp [toyBiKummer]

/-- `U^⊥` 在该模型上**不是全空间**：`a₁ ∉ U^⊥`（因 `cup a₁ a₂ = 1 ≠ 0`）。 -/
example : toyBiKummer.a1 ∉ toyBiKummer.Uperp := by
  rw [BiKummerData.mem_Uperp_iff]
  simp [toyBiKummer, toyCup]

/-! ### C2 的真实域层：形式化为明确的命题 -/

/-- **C2 的真实域层残余**（形式化，可判）：存在 `a₁, a₂ ∈ F^×` 使 Kummer 杯积非零。
这是 `_kummer` 版各条（`Hyp20`/`Hyp22`）的假设 `hne` 的**非空见证**。

库内**只有 `p = 2`** 的实例（`TauCeti.card_brauerGroup_eq_two : Nat.card (Br ℝ) = 2`，
配合 `TauCeti.BrauerGroup.brauer2EquivH2_quaternionClass`）；论文要求 `p` **奇**，
故这一层仍记 `∅-open`——它不是本题的数学障碍，而是需要一次 `Br(F)[p] ≠ 0` 的具体计算
（例如 `F = ℚ(ζ_p)` 上的 `(ζ_p, p)` 类），属**基建/数论**。 -/
def HasNonzeroKummerCup (F : Type) [Field F] (p : ℕ) [Fact p.Prime]
    [HasEnoughRootsOfUnity F p] (hp : IsUnit (p : F)) : Prop :=
  ∃ a1 a2 : Fˣ, GaloBase.cup (K := F) (p := p)
    (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0

/-- 「C2 真实层成立」的**精确陈述**：存在奇素数 `p` 与含 `μ_p` 的域 `F`，使 Kummer 杯积非零。 -/
def HasNonzeroKummerCupSomewhere : Prop :=
  ∃ (F : Type) (_ : Field F) (p : ℕ) (_ : Fact p.Prime) (_ : HasEnoughRootsOfUnity F p)
    (hp : IsUnit (p : F)) (_ : p ≠ 2), HasNonzeroKummerCup F p hp

end L20261018
