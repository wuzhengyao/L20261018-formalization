import L20261018.Hyp13
import L20261018.Hyp40
import L20261018.Hyp92
/-!
# `U` 接线的代数基石：显式模型里 Kummer 类的乘法/取逆/闭包像（R913 第一块）

`Hyp13.theorem_3_5_1_galo` 取 `U = (resMG).ker`（论文取 `U = span{(a₁),(a₂)}`）——这是 3.5(1)
唯一的技术性偏离，也是 **3.6 的前置**（`A.theorem_3_6` 的两条 SES 必须用同一个 `U`）。
`Hyp36.ker_res_eq_span` 已在 `GaloBase.V` 模型上证明了这条等式；本文件开始把它搬到
**显式模型**（`Hyp5` 的 `resMG`、`Hyp40` 的 `lemma_3_3_2_explicit` 所在的模型）。

本文件给出四个纯代数基石（`Hyp36` 同名引理在显式模型的对应物）：

* `kummerExplicit_mul`／`kummerExplicit_one`／`kummerExplicit_inv`：
  `(a·b) = (a) + (b)`、`(1) = 0`、`(a⁻¹) = -(a)`；
* `kummerExplicit_mem_span_of_mem_closure`：`d ∈ closure{a₁,a₂} ⟹ (d) ∈ span{(a₁),(a₂)}`
  （对 `Subgroup.closure` 归纳）。

**剩下的两块**（下一轮）：`kummerExplicit_surjective`（`KummerBridge.kummerH1Equiv` 满 ＋
`kummerMap` 满）与核判据（`resMG (kc a) = 0 ↔ a ∈ (Fˣ)^p ⊔ Δ`，经 `Hyp9.res_explicitH1`
＋ `Hyp29`）；再与 `⊇` 方向（`Hyp40`）合成 `(resMG).ker = span{(a₁),(a₂)}`。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Theo351

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

theorem kummerExplicit_mul (hp : IsUnit (p : F)) (a b : Fˣ) :
    GaloCup.kummerExplicit (F := F) (p := p) hp (a * b)
      = GaloCup.kummerExplicit (F := F) (p := p) hp a
        + GaloCup.kummerExplicit (F := F) (p := p) hp b := by
  simp [GaloCup.kummerExplicit, map_mul, map_add]

theorem kummerExplicit_one (hp : IsUnit (p : F)) :
    GaloCup.kummerExplicit (F := F) (p := p) hp 1 = 0 := by
  have h := kummerExplicit_mul (F := F) (p := p) hp 1 1
  rw [mul_one] at h
  have h2 : (0 : H1 (AbsoluteGaloisGroup F) (ZMod p))
        + GaloCup.kummerExplicit (F := F) (p := p) hp 1
      = GaloCup.kummerExplicit (F := F) (p := p) hp 1
        + GaloCup.kummerExplicit (F := F) (p := p) hp 1 := by
    rw [zero_add]
    exact h
  exact (add_right_cancel h2).symm

theorem kummerExplicit_inv (hp : IsUnit (p : F)) (a : Fˣ) :
    GaloCup.kummerExplicit (F := F) (p := p) hp a⁻¹
      = - GaloCup.kummerExplicit (F := F) (p := p) hp a := by
  have h : GaloCup.kummerExplicit (F := F) (p := p) hp a
      + GaloCup.kummerExplicit (F := F) (p := p) hp a⁻¹ = 0 := by
    rw [← kummerExplicit_mul (F := F) (p := p) hp, mul_inv_cancel]
    exact kummerExplicit_one (F := F) (p := p) hp
  exact eq_neg_of_add_eq_zero_right h

/-- **`Δ = closure{a₁, a₂}` 的 Kummer 像落在 `span{(a₁), (a₂)}` 里**。 -/
theorem kummerExplicit_mem_span_of_mem_closure (hp : IsUnit (p : F)) (a1 a2 : Fˣ) {d : Fˣ}
    (hd : d ∈ Subgroup.closure ({a1, a2} : Set Fˣ)) :
    GaloCup.kummerExplicit (F := F) (p := p) hp d
      ∈ Submodule.span (ZMod p)
          ({GaloCup.kummerExplicit (F := F) (p := p) hp a1,
            GaloCup.kummerExplicit (F := F) (p := p) hp a2} :
            Set (H1 (AbsoluteGaloisGroup F) (ZMod p))) := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hd
  · intro y hy
    rcases (by simpa using hy : y = a1 ∨ y = a2) with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · show GaloCup.kummerExplicit (F := F) (p := p) hp 1 ∈ _
    rw [kummerExplicit_one (F := F) (p := p) hp]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [kummerExplicit_mul (F := F) (p := p) hp]
    exact Submodule.add_mem _ hx hy
  · intro x _ hx
    rw [kummerExplicit_inv (F := F) (p := p) hp]
    exact Submodule.neg_mem _ hx

/-! ### 满射性 -/

/-- **`H¹(G_F, μ_p)` 的每个类都是 Kummer 类**（显式模型）。 -/
theorem kummerExplicit_surjective (hp : IsUnit (p : F)) :
    Function.Surjective (GaloCup.kummerExplicit (F := F) (p := p) hp) := by
  intro x
  obtain ⟨y, hy⟩ := (KummerBridge.kummerH1Equiv F p hp).surjective x
  obtain ⟨a, ha⟩ := kummerMap_surjective (K := F) (n := p) hp (Multiplicative.ofAdd y)
  refine ⟨a, ?_⟩
  show (KummerBridge.kummerH1Equiv F p hp)
    (Multiplicative.toAdd ((kummerMap F p hp) a)) = x
  have hzeq : Multiplicative.toAdd (Multiplicative.ofAdd y) = y := rfl
  rw [ha, hzeq, hy]

/-! ### `resMG` 与 `explicitRes1` 的核同一 -/

theorem resMG_eq_zero_iff_explicitRes1 (Δ : Subgroup Fˣ)
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p) Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p) Δ)]
    (x : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    GaloFive.resMG F p (Theo352.Efield (F := F) (p := p) Δ) x = 0
      ↔ explicitRes1 (AbsoluteGaloisGroup F) (ZMod p)
          (Theo352.Efield (F := F) (p := p) Δ).fixingSubgroup x = 0 := by
  constructor
  · intro h
    have hcoe := congrArg
      (fun y : GaloFive.MG F p (Theo352.Efield (F := F) (p := p) Δ) =>
        (y : H1 (Theo352.Efield (F := F) (p := p) Δ).fixingSubgroup (ZMod p))) h
    have hc := coe_explicitResConj1 (G := AbsoluteGaloisGroup F) (M := ZMod p)
      (N := (Theo352.Efield (F := F) (p := p) Δ).fixingSubgroup) x
    simp only [GaloFive.resMG, AddSubgroup.coe_zero] at hcoe
    exact hc.symm.trans hcoe
  · intro h
    refine Subtype.ext ?_
    have hc := coe_explicitResConj1 (G := AbsoluteGaloisGroup F) (M := ZMod p)
      (N := (Theo352.Efield (F := F) (p := p) Δ).fixingSubgroup) x
    simp only [GaloFive.resMG, AddSubgroup.coe_zero]
    exact hc.trans h

/-! ### 核判据 -/

/-- **`resMG (kc a) = 0 ↔ a ∈ (Fˣ)^p ⊔ Δ`**（显式模型里的限制核判据）。 -/
theorem resMG_kummerExplicit_eq_zero_iff (hp : IsUnit (p : F)) (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p) Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p) Δ)]
    (a : Fˣ) :
    GaloFive.resMG F p (Theo352.Efield (F := F) (p := p) Δ)
        (GaloCup.kummerExplicit (F := F) (p := p) hp a) = 0
      ↔ a ∈ (powMonoidHom p : Fˣ →* Fˣ).range ⊔ Δ := by
  have hiff := BKummer.res_explicitH1_kummerMap_eq_zero_iff (F := F) (p := p) hp Δ hroots a
  rw [resMG_eq_zero_iff_explicitRes1 (F := F) (p := p) Δ]
  constructor
  · intro h
    have h' : explicitRes1 (AbsoluteGaloisGroup F) (ZMod p)
        (Theo352.Efield (F := F) (p := p) Δ).fixingSubgroup
        ((KummerBridge.kummerH1Equiv F p hp)
          (Multiplicative.toAdd ((kummerMap F p hp) a))) = 0 := h
    refine hiff.mp ?_
    rw [res_explicitH1]
    exact (AddEquiv.map_eq_zero_iff _).mpr h'
  · intro h
    refine (explicitH1AddEquivContinuousCohomology
      (G := ↥(Theo352.Efield (F := F) (p := p) Δ).fixingSubgroup) (M := ZMod p)).injective ?_
    rw [map_zero, ← res_explicitH1]
    exact hiff.mpr h

/-! ### 核判据的推论：`p` 次幂的 Kummer 类为零 -/

/-- **`p` 次幂的 Kummer 类是零**：`u ∈ (Fˣ)^p ⟹ (u) = 0`。 -/
theorem kummerExplicit_eq_zero_of_mem_pow (hp : IsUnit (p : F)) {u : Fˣ}
    (hu : u ∈ (powMonoidHom p : Fˣ →* Fˣ).range) :
    GaloCup.kummerExplicit (F := F) (p := p) hp u = 0 := by
  obtain ⟨v, hv⟩ := hu
  have hpow : ∀ k : ℕ, GaloCup.kummerExplicit (F := F) (p := p) hp (v ^ k)
      = k • GaloCup.kummerExplicit (F := F) (p := p) hp v := by
    intro k
    induction k with
    | zero => rw [pow_zero, zero_smul]; exact kummerExplicit_one (F := F) (p := p) hp
    | succ n ih => rw [pow_succ, kummerExplicit_mul (F := F) (p := p) hp, ih, succ_nsmul]
  rw [← hv]
  have hpv : (powMonoidHom p : Fˣ →* Fˣ) v = v ^ p := rfl
  rw [hpv, hpow p, ← Nat.cast_smul_eq_nsmul (R := ZMod p) p,
    CharP.cast_eq_zero (ZMod p) p, zero_smul]

/-! ### 主结果：`(resMG).ker = span{(a₁),(a₂)}` -/

/-- **`U` 接线本体**：`x ∈ ker(res_{E/F}) ↔ x ∈ span{(a₁),(a₂)}`（`E = F(Δ^{1/p})`，
`Δ = closure{a₁,a₂}`）——`Hyp36.ker_res_eq_span` 的显式模型版。 -/
theorem mem_ker_resMG_iff (hp : IsUnit (p : F)) (a1 a2 : Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex
      (Subgroup.closure ({a1, a2} : Set Fˣ))]
    (hroots : ∀ b ∈ Subgroup.closure ({a1, a2} : Set Fˣ),
      ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p)
      (Subgroup.closure ({a1, a2} : Set Fˣ)))]
    [IsGalois F (Theo352.Efield (F := F) (p := p)
      (Subgroup.closure ({a1, a2} : Set Fˣ)))]
    (x : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    x ∈ (GaloFive.resMG F p (Theo352.Efield (F := F) (p := p)
        (Subgroup.closure ({a1, a2} : Set Fˣ)))).ker
      ↔ x ∈ Submodule.span (ZMod p)
          ({GaloCup.kummerExplicit (F := F) (p := p) hp a1,
            GaloCup.kummerExplicit (F := F) (p := p) hp a2} :
            Set (H1 (AbsoluteGaloisGroup F) (ZMod p))) := by
  classical
  haveI : Fact p.Prime := inferInstance
  constructor
  · intro hx
    have hx0 := AddMonoidHom.mem_ker.mp hx
    obtain ⟨a, rfl⟩ := kummerExplicit_surjective (F := F) (p := p) hp x
    have ha := (resMG_kummerExplicit_eq_zero_iff (F := F) (p := p) hp
      (Subgroup.closure ({a1, a2} : Set Fˣ)) hroots a).mp hx0
    rw [Subgroup.mem_sup] at ha
    obtain ⟨u, hu, d, hd, hud⟩ := ha
    have hkm : GaloCup.kummerExplicit (F := F) (p := p) hp a
        = GaloCup.kummerExplicit (F := F) (p := p) hp u
          + GaloCup.kummerExplicit (F := F) (p := p) hp d := by
      rw [← kummerExplicit_mul (F := F) (p := p) hp, hud]
    rw [hkm, kummerExplicit_eq_zero_of_mem_pow (F := F) (p := p) hp hu, zero_add]
    exact kummerExplicit_mem_span_of_mem_closure (F := F) (p := p) hp a1 a2 hd
  · intro hx
    have hK : GaloCup.kummerExplicit (F := F) (p := p) hp a1
        ∈ (GaloFive.resMG F p (Theo352.Efield (F := F) (p := p)
            (Subgroup.closure ({a1, a2} : Set Fˣ)))).ker
      ∧ GaloCup.kummerExplicit (F := F) (p := p) hp a2
        ∈ (GaloFive.resMG F p (Theo352.Efield (F := F) (p := p)
            (Subgroup.closure ({a1, a2} : Set Fˣ)))).ker := by
      constructor
      · rw [AddMonoidHom.mem_ker]
        exact (resMG_kummerExplicit_eq_zero_iff (F := F) (p := p) hp
          (Subgroup.closure ({a1, a2} : Set Fˣ)) hroots a1).mpr
          (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
      · rw [AddMonoidHom.mem_ker]
        exact (resMG_kummerExplicit_eq_zero_iff (F := F) (p := p) hp
          (Subgroup.closure ({a1, a2} : Set Fˣ)) hroots a2).mpr
          (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
    -- `ker` 在 `ZMod p`-纯量下封闭，故含两生成元的 span
    let K : Submodule (ZMod p) (H1 (AbsoluteGaloisGroup F) (ZMod p)) :=
      { __ := (GaloFive.resMG F p (Theo352.Efield (F := F) (p := p)
            (Subgroup.closure ({a1, a2} : Set Fˣ)))).ker
        smul_mem' := fun c y hy => by
          rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
          exact (GaloFive.resMG F p (Theo352.Efield (F := F) (p := p)
            (Subgroup.closure ({a1, a2} : Set Fˣ)))).ker.nsmul_mem hy c.val }
    have hle : Submodule.span (ZMod p)
        ({GaloCup.kummerExplicit (F := F) (p := p) hp a1,
          GaloCup.kummerExplicit (F := F) (p := p) hp a2} :
          Set (H1 (AbsoluteGaloisGroup F) (ZMod p))) ≤ K := by
      refine Submodule.span_le.mpr ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hK.1
      · exact hK.2
    exact hle hx

/-! ### 3.5(1) 以论文的 `U` 陈述 -/

/-- **3.5(1)（论文形式）**：`0 → V/(U+N) → M^G/N_G(M) → K₂ → 0`，其中
`U = span{(a₁),(a₂)}`（论文的 U，**不是** `ker res`）。

证明 = `Hyp13.theorem_3_5_1_galo`（`U = ker res` 版）＋ `mem_ker_resMG_iff`（把 `ker res` 换成 span）。 -/
-- @source file=raw/L20261018.tex locator=label:thm:hs-tate-exact-sequences quote="0\longrightarrow V/(U+N) \xrightarrow{\ \overline{\res}_{E/F}\ }\widehat H^0(G,M) \xrightarrow{\ \bar d_2\ }K_2\longrightarrow0"
theorem theorem_3_5_1_explicit (hp : IsUnit (p : F)) (a1 a2 : Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex
      (Subgroup.closure ({a1, a2} : Set Fˣ))]
    (hroots : ∀ b ∈ Subgroup.closure ({a1, a2} : Set Fˣ),
      ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p)
      (Subgroup.closure ({a1, a2} : Set Fˣ)))]
    [IsGalois F (Theo352.Efield (F := F) (p := p)
      (Subgroup.closure ({a1, a2} : Set Fˣ)))] :
    ∃ (φ : (H1 (AbsoluteGaloisGroup F) (ZMod p) ⧸
          ((Submodule.span (ZMod p)
              ({GaloCup.kummerExplicit (F := F) (p := p) hp a1,
                GaloCup.kummerExplicit (F := F) (p := p) hp a2} :
                Set (H1 (AbsoluteGaloisGroup F) (ZMod p)))).toAddSubgroup
            ⊔ GaloFive.Ncor F p (Theo352.Efield (F := F) (p := p)
              (Subgroup.closure ({a1, a2} : Set Fˣ)))))
        →+ (↥(GaloFive.MG F p (Theo352.Efield (F := F) (p := p)
              (Subgroup.closure ({a1, a2} : Set Fˣ)))) ⧸
            GaloFive.NG F p (Theo352.Efield (F := F) (p := p)
              (Subgroup.closure ({a1, a2} : Set Fˣ)))))
      (ψ : (↥(GaloFive.MG F p (Theo352.Efield (F := F) (p := p)
              (Subgroup.closure ({a1, a2} : Set Fˣ)))) ⧸
            GaloFive.NG F p (Theo352.Efield (F := F) (p := p)
              (Subgroup.closure ({a1, a2} : Set Fˣ)))) →+
          ↥(GaloFive.K2 F p (Theo352.Efield (F := F) (p := p)
              (Subgroup.closure ({a1, a2} : Set Fˣ))))),
      Function.Injective φ ∧ Function.Surjective ψ ∧ φ.range = ψ.ker := by
  have hU : (GaloFive.resMG F p (Theo352.Efield (F := F) (p := p)
        (Subgroup.closure ({a1, a2} : Set Fˣ)))).ker
      = (Submodule.span (ZMod p)
          ({GaloCup.kummerExplicit (F := F) (p := p) hp a1,
            GaloCup.kummerExplicit (F := F) (p := p) hp a2} :
            Set (H1 (AbsoluteGaloisGroup F) (ZMod p)))).toAddSubgroup := by
    ext x
    rw [Submodule.mem_toAddSubgroup]
    exact mem_ker_resMG_iff (F := F) (p := p) hp a1 a2 hroots x
  rw [← hU]
  exact GaloFive.theorem_3_5_1_galo (K := F) (p := p)
    (E := Theo352.Efield (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ)))

end Theo351

#print axioms Theo351.kummerExplicit_mul
#print axioms Theo351.kummerExplicit_inv
#print axioms Theo351.kummerExplicit_surjective
#print axioms Theo351.resMG_eq_zero_iff_explicitRes1
#print axioms Theo351.resMG_kummerExplicit_eq_zero_iff
#print axioms Theo351.kummerExplicit_mem_span_of_mem_closure
#print axioms Theo351.kummerExplicit_eq_zero_of_mem_pow
#print axioms Theo351.mem_ker_resMG_iff
#print axioms Theo351.theorem_3_5_1_explicit
