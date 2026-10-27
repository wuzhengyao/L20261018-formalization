import L20261018.Hyp35
import L20261018.Hyp26
/-!
# `(a)` 收口：`ker res = U` 在论文的载体上

`Hyp35.res_kummerClass_eq_zero_iff` 给出的是**逐 Kummer 类**的判据：
`res (a) = 0 ↔ a ∈ (Fˣ)^p ⊔ Δ`。`A.lemma_3_1_2` 要的是**子模等式**
`LinearMap.ker res = U`，其中 `U = span{(a₁), (a₂)}`。本文件把前者组装成后者。

为此需要两块：

1. **`kummerClass` 满射**（`kummerClass_surjective`）：`V = H¹(F, ZMod p)` 的每个类都是某个
   `a ∈ Fˣ` 的 Kummer 类。由 `TauCeti.kummerMap_surjective`（Kummer 理论/Hilbert 90）经两个加法等价搬过来。
   没有它，逐类判据管不到任意 `x : V`。

2. **`Δ = closure{a₁, a₂}` 的像落在 `span{(a₁), (a₂)}` 里**
   （`kummerClass_mem_span_of_mem_closure`）：`kummerClass` 是群同态
   （`Hyp26.kummerClassHom`），故对 `closure` 归纳即得——乘性走加法、取逆走负元。
   注意这里**不需要 `p`-挠**：`Subgroup.closure` 的归纳只给乘积与逆，不给整数倍。

组装：`x ∈ ker res` ⟹ `x = (a)`（满射）⟹ `a ∈ (Fˣ)^p ⊔ Δ`（`Hyp35`）⟹ 写成 `u·d`
（`u` 是 `p` 次幂、`d ∈ Δ`）⟹ `(a) = (u) + (d) = 0 + (d) ∈ span`。反向由
`span_le`：`(aᵢ)` 本身在 `ker res` 里（`aᵢ ∈ Δ`）。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace KummerV

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **每个上同调类都是某个 `a ∈ Fˣ` 的 Kummer 类。** 由 Kummer 理论（`TauCeti.kummerMap_surjective`）
经系数比较与模型比较两个加法等价搬过来。 -/
theorem kummerClass_surjective (hp : IsUnit (p : F)) :
    Function.Surjective (KummerBridge.kummerClass F p hp) := by
  intro v
  obtain ⟨y, hy⟩ := (KummerBridge.h1ToVEquiv (F := F) (p := p)).surjective v
  obtain ⟨z, hz⟩ := (KummerBridge.kummerH1Equiv F p hp).surjective y
  obtain ⟨a, ha⟩ := kummerMap_surjective (K := F) (n := p) hp (Multiplicative.ofAdd z)
  refine ⟨a, ?_⟩
  show KummerBridge.h1ToVEquiv F p
    ((KummerBridge.kummerH1Equiv F p hp) ((kummerMap F p hp a).toAdd)) = v
  have hzeq : Multiplicative.toAdd (Multiplicative.ofAdd z) = z := rfl
  rw [ha, hzeq, hz, hy]

/-- `kummerClass` 作为加法同态：`(ab) = (a) + (b)`。 -/
theorem kummerClass_mul (hp : IsUnit (p : F)) (x y : Fˣ) :
    KummerBridge.kummerClass F p hp (x * y)
      = KummerBridge.kummerClass F p hp x + KummerBridge.kummerClass F p hp y := by
  have h := map_mul (KummerBridge.kummerClassHom (F := F) (p := p) hp) x y
  simp only [KummerBridge.kummerClassHom_apply] at h
  exact Multiplicative.ofAdd.injective h

/-- `kummerClass` 取逆：`(a⁻¹) = -(a)`。 -/
theorem kummerClass_inv (hp : IsUnit (p : F)) (x : Fˣ) :
    KummerBridge.kummerClass F p hp x⁻¹ = - KummerBridge.kummerClass F p hp x := by
  have h : KummerBridge.kummerClass F p hp x + KummerBridge.kummerClass F p hp x⁻¹ = 0 := by
    rw [← kummerClass_mul (F := F) (p := p) hp, mul_inv_cancel]
    exact (KummerBridge.kummerClass_eq_zero_iff (F := F) (p := p) hp 1).mpr (one_mem _)
  exact eq_neg_of_add_eq_zero_right h

/-- **`Δ = closure{a₁, a₂}` 的 Kummer 像落在 `span{(a₁), (a₂)}` 里。**
对 `Subgroup.closure` 归纳：生成元由 `subset_span` 直接给出，乘积走 `kummerClass_mul`，
取逆走 `kummerClass_inv`。 -/
theorem kummerClass_mem_span_of_mem_closure (hp : IsUnit (p : F)) (a1 a2 : Fˣ) {d : Fˣ}
    (hd : d ∈ Subgroup.closure ({a1, a2} : Set Fˣ)) :
    KummerBridge.kummerClass F p hp d
      ∈ Submodule.span (ZMod p)
          ({KummerBridge.kummerClass F p hp a1, KummerBridge.kummerClass F p hp a2} :
            Set (GaloBase.V F p)) := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hd
  · intro y hy
    rcases (by simpa using hy : y = a1 ∨ y = a2) with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · show KummerBridge.kummerClass F p hp 1 ∈ _
    rw [(KummerBridge.kummerClass_eq_zero_iff (F := F) (p := p) hp 1).mpr (one_mem _)]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [kummerClass_mul (F := F) (p := p) hp]
    exact Submodule.add_mem _ hx hy
  · intro x _ hx
    rw [kummerClass_inv (F := F) (p := p) hp]
    exact Submodule.neg_mem _ hx

/-- **`(a)` 收口：`ker res = U`。** 在论文自己的载体 `GaloBase.V F p = H¹(G_F, ZMod p)` 上，
限制到 `E = F(Δ^{1/p})`（`Δ = closure{a₁, a₂}`）的核**恰好**是由 `(a₁)`, `(a₂)` 张成的二维子空间
`U`。这正是 `A.lemma_3_1_2` 的假设 `hker`，也是论文条目 3.1(2)。

`⊆`：任意 `x` 由 `kummerClass_surjective` 写成 `(a)`；`Hyp35` 的判据给出 `a ∈ (Fˣ)^p ⊔ Δ`；
写成 `a = u·d`（`u` 是 `p` 次幂、`d ∈ Δ`）后 `(a) = (u) + (d) = 0 + (d) ∈ U`
（`kummerClass_eq_zero_iff` 与 `kummerClass_mem_span_of_mem_closure`）。
`⊇`：`aᵢ ∈ Δ`，故 `(aᵢ) ∈ ker res`（`Hyp35` 判据），而 `ker res` 是子模。 -/
theorem ker_res_eq_span (hp : IsUnit (p : F)) (a1 a2 : Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex
      (Subgroup.closure ({a1, a2} : Set Fˣ))]
    (hroots : ∀ b ∈ Subgroup.closure ({a1, a2} : Set Fˣ),
      ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F)) :
    (ContinuousCohomology.res
        (IntermediateField.val (kummerField (SeparableClosure F) p
          (Subgroup.closure ({a1, a2} : Set Fˣ)))).fieldRange.fixingSubgroup
        (GaloBase.muP F p) 1).hom.ker
      = Submodule.span (ZMod p)
          ({KummerBridge.kummerClass F p hp a1, KummerBridge.kummerClass F p hp a2} :
            Set (GaloBase.V F p)) := by
  set S : Subgroup (AbsoluteGaloisGroup F) :=
    (IntermediateField.val (kummerField (SeparableClosure F) p
      (Subgroup.closure ({a1, a2} : Set Fˣ)))).fieldRange.fixingSubgroup with hS
  apply le_antisymm
  · intro x hx
    change (ContinuousCohomology.res S (GaloBase.muP F p) 1).hom x = 0 at hx
    obtain ⟨a, rfl⟩ := kummerClass_surjective (F := F) (p := p) hp x
    have ha := (res_kummerClass_eq_zero_iff (F := F) (p := p) hp
      (Subgroup.closure ({a1, a2} : Set Fˣ)) hroots a).mp (hS ▸ hx)
    rw [Subgroup.mem_sup] at ha
    obtain ⟨u, hu, d, hd, hud⟩ := ha
    have hkm : KummerBridge.kummerClass F p hp a
        = KummerBridge.kummerClass F p hp u + KummerBridge.kummerClass F p hp d := by
      rw [← hud, kummerClass_mul (F := F) (p := p) hp]
    rw [hkm, (KummerBridge.kummerClass_eq_zero_iff (F := F) (p := p) hp u).mpr hu, zero_add]
    exact kummerClass_mem_span_of_mem_closure (F := F) (p := p) hp a1 a2 hd
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    change (ContinuousCohomology.res S (GaloBase.muP F p) 1).hom x = 0
    rcases hx with rfl | rfl
    · exact (res_kummerClass_eq_zero_iff (F := F) (p := p) hp
        (Subgroup.closure ({a1, a2} : Set Fˣ)) hroots a1).mpr
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
    · exact (res_kummerClass_eq_zero_iff (F := F) (p := p) hp
        (Subgroup.closure ({a1, a2} : Set Fˣ)) hroots a2).mpr
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))

/-! ### 接 `A.lemma_3_1_2`：`hker` 参数被消掉 -/

/-- **奇素数下 `2 ≠ 0` 在 `ZMod p` 中**（`A.lemma_3_1_2` 的 `[NeZero (2 : k)]` 前提）。
论文固定 `p` 为**奇**素数，故这个前提在目标域类上非空。 -/
theorem neZero_two_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : NeZero (2 : ZMod p) where
  out := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by simpa using h)
    have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    exact hp2 (le_antisymm hple hpge)

/-- **`A.lemma_3_1_2` 在真实对象上、`hker` 被消掉。** 论文 3.1(2) 的结论（`res|_{U^⊥}` 单射）
现在**不再需要 `hker` 参数**：它由 `ker_res_eq_span` 提供。`B` 取 `A.galoBiKummer`，`aᵢ` 取
Kummer 类 `(aᵢ)`，`res` 取真实限制映射的 `ZMod p`-线性部分。

剩下的前提只有三条**非空且真实**的输入：`p` 为奇素数（`hp2`），`(Fˣ)^p` 在 `closure{a₁,a₂}`
中有限指数（`IsFiniteRelIndex`），以及 `Δ` 的元素在可分闭包中可开 `p` 次方（`hroots`；
`char F ∤ p` 时恒真）。 -/
theorem lemma_3_1_2_galo (hp : IsUnit (p : F)) (a1 a2 : Fˣ) (hp2 : p ≠ 2)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex
      (Subgroup.closure ({a1, a2} : Set Fˣ))]
    (hroots : ∀ b ∈ Subgroup.closure ({a1, a2} : Set Fˣ),
      ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (hne : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0) :
    Function.Injective (fun x : (L20261018.galoBiKummer (K := F) (p := p)
        (KummerBridge.kummerClass F p hp a1)
        (KummerBridge.kummerClass F p hp a2) hne).Uperp =>
      (ContinuousCohomology.res
        (IntermediateField.val (kummerField (SeparableClosure F) p
          (Subgroup.closure ({a1, a2} : Set Fˣ)))).fieldRange.fixingSubgroup
        (GaloBase.muP F p) 1).hom x.val) := by
  have hN2 : NeZero (2 : ZMod p) := neZero_two_zmod hp2
  let B : L20261018.BiKummerData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) :=
    L20261018.galoBiKummer (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1)
      (KummerBridge.kummerClass F p hp a2) hne
  let resL : GaloBase.V F p →ₗ[ZMod p]
      ↑(continuousCohomology 1 (TopRep.res
        (IntermediateField.val (kummerField (SeparableClosure F) p
          (Subgroup.closure ({a1, a2} : Set Fˣ)))).fieldRange.fixingSubgroup.subtype
        (GaloBase.muP F p))).toModuleCat :=
    (ContinuousCohomology.res
      (IntermediateField.val (kummerField (SeparableClosure F) p
        (Subgroup.closure ({a1, a2} : Set Fˣ)))).fieldRange.fixingSubgroup
      (GaloBase.muP F p) 1).hom
  have hker : LinearMap.ker resL = B.U :=
    ker_res_eq_span (F := F) (p := p) hp a1 a2 (hroots := hroots)
  exact B.lemma_3_1_2 resL hker

end KummerV
