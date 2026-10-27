import L20261018.Hyp5
import L20261018.Hyp36
import L20261018.Hyp40
import TauCeti.RepresentationTheory.Homological.ContCohomology.H2ZMod

/-!
# 3.5(2) 的真实对象版：`U^⊥/N ↪ V/(U+N) ↠ V/(U+U^⊥)`（R912）

`A.theorem_3_5_2` 是**抽象** `BiKummerData` 版（B 档）。本文件把它实例化到论文的真实对象上，
全部在**显式上同调模型**（`ContCohomology.H1`/`H2`，与 `Hyp5` 的 `Ncor`、`Hyp40` 的
`lemma_3_3_2_explicit` 同一个模型）：

* `V = H¹(G_F, μ_p)` = `H1 (AbsoluteGaloisGroup F) (ZMod p)`；
* `U = span{(a₁), (a₂)}`，`(a) = kummerExplicit a`（`Hyp40`）；
* `U^⊥ = {x : x ∪ (a₁) = x ∪ (a₂) = 0}`（`BiKummerData.Uperp`，`cup = explicitCup11`）；
* `N = cor_{E/F} H¹(E, μ_p)`（`GaloFive.Ncor`，`E = kummerField(Δ).fieldRange`）。

## 两块新基建（都是库内缺口）

1. **`H¹` 的 `ZMod n`-模结构**（`instModuleZModH1`）：TauCeti 只有 `H²` 版的
   `instModuleZModH2`。做法同源：`ZMod n`-模上 `n • x = 0`，故 `H¹` 也是（`nsmul_H1_eq_zero`）。
2. **显式杯积的斜对称**（`cupLin_skew`）：`explicitCup11_eq_neg_flip` 给
   `x ⌣ y = - (y ⌣_{μᵒᵖ} x)`，还差一步「交换配对下 `μ` 与 `μᵒᵖ` 给出同一杯积」
   （`explicitCup11_flip_eq`，逐余环链算 `mul_comm`）。没有这一步，`BiKummerData.skew` 填不上。

## 主结果

* **`theorem_3_5_2_explicit`**：`N ⊆ U^⊥` 由 `Hyp40`（投影公式 ＋ `res(a_i) = 0`）给出，
  再交给 `A.theorem_3_5_2` —— 于是该条目**只带论文自身的假设**（`p` 奇素、`μ_p ⊂ F`、
  `E = F(a₁^{1/p}, a₂^{1/p})`、`(a₁)∪(a₂) ≠ 0`）。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Theo352

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-! ### 基建 1：`H¹` 的 `ZMod n`-模结构 -/

/-- `n • x = 0` 在 `H¹(G, M)` 上（系数上成立时）。 -/
theorem nsmul_H1_eq_zero {n : ℕ} {G : Type} [Monoid G] [TopologicalSpace G] {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [DistribMulAction G M]
    [ContinuousSMul G M] (h : ∀ m : M, n • m = 0) (x : H1 G M) : n • x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    have hz : (n • z : ↥(Z1 G M)) = 0 := by
      refine Subtype.ext ?_
      funext g
      exact h (z.1 g)
    have h1 : (H1pi G M) (n • z) = 0 := by rw [hz, map_zero]
    rw [AddMonoidHom.map_nsmul] at h1
    exact h1

/-- **`H¹(G, M)` 是 `ZMod n`-模**（当系数是时）——`instModuleZModH2` 的 `H¹` 版。 -/
instance instModuleZModH1 {n : ℕ} {G : Type} [Monoid G] [TopologicalSpace G] {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [DistribMulAction G M]
    [ContinuousSMul G M] [Module (ZMod n) M] : Module (ZMod n) (H1 G M) :=
  AddCommGroup.zmodModule (nsmul_H1_eq_zero (ZModModule.char_nsmul_eq_zero n))

/-! ### 基建 2：显式杯积的 `ZMod p`-线性与斜对称 -/

/-- `ZMod n`-模之间的加性同态尊重纯量。 -/
theorem addMonoidHom_map_zmod_smul {n : ℕ} [NeZero n] {M N : Type*} [AddCommGroup M]
    [Module (ZMod n) M] [AddCommGroup N] [Module (ZMod n) N] (f : M →+ N) (c : ZMod n) (y : M) :
    f (c • y) = c • f y := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul]
  have h := AddMonoidHom.map_nsmul f c.val y
  rw [h]
  conv_rhs => rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]

/-- 显式杯积对第一槽 `ZMod p`-线性。 -/
theorem cup_smul_left (c : ZMod p) (x y : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
        (GaloCup.zmodMulPairing p) (continuous_of_discreteTopology) (fun _ _ _ => rfl) (c • x) y
      = c • (explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
        (GaloCup.zmodMulPairing p) (continuous_of_discreteTopology) (fun _ _ _ => rfl) x y) := by
  have h := addMonoidHom_map_zmod_smul (n := p)
    (f := explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
      (GaloCup.zmodMulPairing p) (continuous_of_discreteTopology) (fun _ _ _ => rfl)) c x
  rw [h]
  exact AddMonoidHom.smul_apply c _ y

/-- 显式杯积对第二槽 `ZMod p`-线性。 -/
theorem cup_smul_right (c : ZMod p) (x y : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
        (GaloCup.zmodMulPairing p) (continuous_of_discreteTopology) (fun _ _ _ => rfl) x (c • y)
      = c • (explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
        (GaloCup.zmodMulPairing p) (continuous_of_discreteTopology) (fun _ _ _ => rfl) x y) := by
  have h := addMonoidHom_map_zmod_smul (n := p)
    (f := (explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
      (GaloCup.zmodMulPairing p) (continuous_of_discreteTopology) (fun _ _ _ => rfl)) x) c y
  rw [h]

/-- **显式 `(1,1)` 杯积，`ZMod p`-双线性版**。 -/
noncomputable def cupLin :
    H1 (AbsoluteGaloisGroup F) (ZMod p) →ₗ[ZMod p]
      H1 (AbsoluteGaloisGroup F) (ZMod p) →ₗ[ZMod p] H2 (AbsoluteGaloisGroup F) (ZMod p) :=
  LinearMap.mk₂ (ZMod p)
    (fun x y => explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
      (GaloCup.zmodMulPairing p) (continuous_of_discreteTopology) (fun _ _ _ => rfl) x y)
    (fun x₁ x₂ y => by simp)
    (fun c x y => cup_smul_left (p := p) c x y)
    (fun x y₁ y₂ => by simp)
    (fun c x y => cup_smul_right (p := p) c x y)

theorem cupLin_apply (x y : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    cupLin (p := p) x y = explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
      (GaloCup.zmodMulPairing p) (continuous_of_discreteTopology) (fun _ _ _ => rfl) x y := by
  simp only [cupLin, LinearMap.mk₂_apply]

/-- `ZMod p` 的乘法配对交换：`μᵒᵖ = μ`。 -/
theorem zmodMulPairing_flip :
    (GaloCup.zmodMulPairing p).flip = GaloCup.zmodMulPairing p := by
  refine AddMonoidHom.ext fun x => ?_
  refine AddMonoidHom.ext fun y => ?_
  exact mul_comm y x

/-- **交换配对下 `μᵒᵖ` 与 `μ` 给出同一个显式杯积**（逐余环链 `mul_comm`）。 -/
theorem explicitCup11_flip_eq
    (hμ : Continuous (fun q : (ZMod p) × (ZMod p) => (GaloCup.zmodMulPairing p) q.1 q.2))
    (hequiv : ∀ (g : AbsoluteGaloisGroup F) (m n : ZMod p),
      (GaloCup.zmodMulPairing p) (g • m) (g • n) = g • (GaloCup.zmodMulPairing p) m n)
    (x y : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
        ((GaloCup.zmodMulPairing p).flip)
        ((GaloCup.zmodMulPairing p).continuous_flip hμ)
        ((GaloCup.zmodMulPairing p).flip_map_smul hequiv) x y
      = explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p)
        (GaloCup.zmodMulPairing p) hμ hequiv x y := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    induction y using QuotientAddGroup.induction_on with
    | H b =>
      rw [explicitCup11_mk, explicitCup11_mk]
      congr 1
      refine Subtype.ext ?_
      funext q
      exact mul_comm ((b : AbsoluteGaloisGroup F → ZMod p) q.2)
        (q.1 • (a : AbsoluteGaloisGroup F → ZMod p) q.1)

/-- **显式杯积斜对称**：`x ∪ y = - (y ∪ x)`（`explicitCup11_eq_neg_flip` ＋ 交换配对）。 -/
theorem cupLin_skew (x y : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    cupLin x y = - cupLin y x := by
  have key := explicitCup11_eq_neg_flip (G := AbsoluteGaloisGroup F) (M := ZMod p) (N := ZMod p)
    (P := ZMod p) (μ := GaloCup.zmodMulPairing p) (hμ := continuous_of_discreteTopology)
    (hequiv := fun _ _ _ => rfl) x y
  rw [explicitCup11_flip_eq (hμ := continuous_of_discreteTopology) (hequiv := fun _ _ _ => rfl)]
    at key
  rw [cupLin_apply, cupLin_apply]
  exact key

/-! ### 真实对象 -/

/-- 论文的 `E = F(a₁^{1/p}, a₂^{1/p})`（以 Kummer 子群 `Δ` 编码）。 -/
noncomputable def Efield (Δ : Subgroup Fˣ) : IntermediateField F (SeparableClosure F) :=
  (IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange

/-- 显式模型上的 `BiKummerData`：`cup = explicitCup11`、`a_i = (a_i)`。 -/
noncomputable def Bex (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (hne : cupLin (F := F) (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    L20261018.BiKummerData (ZMod p) (H1 (AbsoluteGaloisGroup F) (ZMod p))
      (H2 (AbsoluteGaloisGroup F) (ZMod p)) where
  cup := cupLin
  a1 := GaloCup.kummerExplicit (F := F) (p := p) hp a1
  a2 := GaloCup.kummerExplicit (F := F) (p := p) hp a2
  hne := hne
  skew := cupLin_skew

/-- 真实 `N = cor_{E/F}H¹(E, μ_p)`，看作 `ZMod p`-子模。 -/
noncomputable def Nsub (Δ : Subgroup Fˣ) [FiniteDimensional F (Efield (F := F) (p := p) Δ)]
    [IsGalois F (Efield (F := F) (p := p) Δ)] :
    Submodule (ZMod p) (H1 (AbsoluteGaloisGroup F) (ZMod p)) :=
  Submodule.span (ZMod p)
    ((GaloFive.Ncor F p (Efield (F := F) (p := p) Δ) : Set (H1 (AbsoluteGaloisGroup F) (ZMod p))))

/-! ### 主定理 -/

/-- **3.5(2) 的真实对象版**：`0 → U^⊥/N → V/(U+N) → V/(U+U^⊥) → 0`。

`N ⊆ U^⊥` 由 `Hyp40.lemma_3_3_2_explicit`（投影公式 ＋ `res(a_i) = 0`）给出；
其余是 `A.theorem_3_5_2` 的线性代数内容。 -/
-- @source file=raw/L20261018.tex locator=label:thm:hs-tate-exact-sequences quote="0\longrightarrow U^\perp/N \xrightarrow{\ j\ }V/(U+N) \xrightarrow{\ q\ }V/(U+U^\perp)\longrightarrow0."
theorem theorem_3_5_2_explicit (hp : IsUnit (p : F)) (hp2 : p ≠ 2) (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (hU : IsOpen ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
      : Set (AbsoluteGaloisGroup F)))
    [((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup).FiniteIndex]
    [FiniteDimensional F (Efield (F := F) (p := p) Δ)]
    [IsGalois F (Efield (F := F) (p := p) Δ)]
    {a1 a2 : Fˣ} (ha1 : a1 ∈ Δ) (ha2 : a2 ∈ Δ)
    (hne : cupLin (F := F) (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    ∃ (j : ((Bex (F := F) (p := p) hp hne).Uperp ⧸
          (Nsub (F := F) (p := p) Δ).comap (Bex (F := F) (p := p) hp hne).Uperp.subtype) →ₗ[ZMod p]
          (H1 (AbsoluteGaloisGroup F) (ZMod p) ⧸
            ((Bex (F := F) (p := p) hp hne).U ⊔ Nsub (F := F) (p := p) Δ)))
      (q : (H1 (AbsoluteGaloisGroup F) (ZMod p) ⧸
            ((Bex (F := F) (p := p) hp hne).U ⊔ Nsub (F := F) (p := p) Δ)) →ₗ[ZMod p]
          (H1 (AbsoluteGaloisGroup F) (ZMod p) ⧸
            ((Bex (F := F) (p := p) hp hne).U ⊔ (Bex (F := F) (p := p) hp hne).Uperp))),
      Function.Injective j ∧ Function.Surjective q ∧ LinearMap.range j = LinearMap.ker q := by
  haveI h2 : NeZero (2 : ZMod p) := ⟨by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by simpa using h)
    have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    exact hp2 (le_antisymm hple hpge)⟩
  have hNU : Nsub (F := F) (p := p) Δ ≤ (Bex (F := F) (p := p) hp hne).Uperp := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    rw [SetLike.mem_coe] at hx
    obtain ⟨w, rfl⟩ := hx
    have hmain : cupLin (F := F) (p := p) ((GaloFive.corN F p (Efield Δ)) w)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a1) = 0 ∧
        cupLin (F := F) (p := p) ((GaloFive.corN F p (Efield Δ)) w)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a2) = 0 :=
      GaloCup.lemma_3_3_2_explicit (F := F) (p := p) hp Δ hroots ha1 ha2 hU w
    exact (Bex (F := F) (p := p) hp hne).mem_Uperp_iff _ |>.mpr hmain
  exact L20261018.BiKummerData.theorem_3_5_2 (Bex (F := F) (p := p) hp hne)
    (Nsub (F := F) (p := p) Δ) hNU

/-- `Nsub` 就是 `Ncor` 本身（加法子群在 `ZMod p`-模下自动是子模，故张成不放大）。 -/
theorem Nsub_coe (Δ : Subgroup Fˣ) [FiniteDimensional F (Efield (F := F) (p := p) Δ)]
    [IsGalois F (Efield (F := F) (p := p) Δ)] :
    ((Nsub (F := F) (p := p) Δ : Submodule (ZMod p) (H1 (AbsoluteGaloisGroup F) (ZMod p))) :
        Set (H1 (AbsoluteGaloisGroup F) (ZMod p)))
      = (GaloFive.Ncor F p (Efield (F := F) (p := p) Δ) :
        Set (H1 (AbsoluteGaloisGroup F) (ZMod p))) := by
  let S : Submodule (ZMod p) (H1 (AbsoluteGaloisGroup F) (ZMod p)) :=
    { __ := GaloFive.Ncor F p (Efield (F := F) (p := p) Δ)
      smul_mem' := fun c x hx => by
        rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
        exact (GaloFive.Ncor F p (Efield (F := F) (p := p) Δ)).nsmul_mem hx c.val }
  have h : Submodule.span (ZMod p)
      ((GaloFive.Ncor F p (Efield (F := F) (p := p) Δ) :
        Set (H1 (AbsoluteGaloisGroup F) (ZMod p)))) = S :=
    Submodule.span_eq S
  rw [Nsub, h]
  rfl

end Theo352

#print axioms Theo352.nsmul_H1_eq_zero
#print axioms Theo352.cupLin_skew
#print axioms Theo352.theorem_3_5_2_explicit
