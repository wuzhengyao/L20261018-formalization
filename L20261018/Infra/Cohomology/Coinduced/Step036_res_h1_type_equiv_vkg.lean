import L20261018.Ch4.Step042_hd_infl_final_form

/-!
# S70 R1：`F5` 第二半 —— `ResH1Type ≅ VKG`（膨胀把剩余 `H¹` 送到 `ker v̄`）

`F5` 的两半（`PROMPT-S70` §①／§②）：
* **本件＝第二半**：`H¹(Γ⧸I, ℤ/p) = ResH1Type ≅ VKG`，即 `infl1Res` 的**核零、值域恰是 `ker v̄`**。
* 第一半（`H¹(Γ⧸I,H¹(I,μ_p)) ≅ H¹(Γ⧸I,ℤ/p)`）**不在本件**（墙 1，`LESSONS` D73）。

## 机制（三块，全部现成）

```
infl1Res (eQ x) = h1ToVEquiv (explicitMap1 (Γ⧸I) (ZMod p) Γ (ZMod p) φ id x)      Hyp748.infl1Res_eQ
explicitMap1 … φ id = explicitInfl1 ∘ explicitMap1 … id e                          Hyp748.explicitInfl1_eq_comp_coeff
explicitMap1 … id subtype ∘ explicitMap1 … id e = id                              ★本件（explicitMap1_comp ＋ Hyp752）
explicitRes1 ∘ explicitInfl1 = 0                                                  库内
VKG ≤ range infl1Res                                                              Hyp749.unramifiedKummer
```

## 交付

| 声明 | 内容 |
|---|---|
| `explicitMap1_subtype_comp_coeff` | ★★★★ `em_{sub} ∘ em_e = id`（一级） |
| `res1V_h1ToVEquiv` | `res1V (h1ToVEquiv y) = explicitRes1 y` |
| **`res1V_infl1Res_eq_zero`** | ★★★★ 膨胀的像落在 `ker(res₁)` |
| `infl1Res_mem_VKG` | `infl1Res a ∈ VKG` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-- ★★★★ **一级方阵的右逆**：`em_{Γ⧸I,sub} ∘ em_{Γ⧸I,e} = id`。

`explicitMap1_comp`（`φ = ψ = id`、`q = subtype`、`f = e`）＋ `subtype ∘ e = id`
（`Hyp752.subtype_comp_coeffSubAddHom`）＋ `explicitMap1_id`。 -/
theorem explicitMap1_subtype_comp_coeff :
    (explicitMap1 (AbsoluteGaloisGroup F ⧸ I)
        ↥(FixedPoints.addSubgroup (↥I) (ZMod p))
        (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
        (ContinuousMonoidHom.id _)
        (FixedPoints.addSubgroup (↥I) (ZMod p)).subtype
        continuous_of_discreteTopology
        (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) I k n)).comp
      (explicitMap1 (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
        (AbsoluteGaloisGroup F ⧸ I) ↥(FixedPoints.addSubgroup (↥I) (ZMod p))
        (ContinuousMonoidHom.id _) (coeffSubAddHom (p := p) (I := I))
        continuous_of_discreteTopology
        (coeffSubAddHom_smul (F := F) (p := p) I))
    = AddMonoidHom.id (H1 (AbsoluteGaloisGroup F ⧸ I) (ZMod p)) := by
  rw [← explicitMap1_comp (G := AbsoluteGaloisGroup F ⧸ I) (M := ZMod p)
    (H := AbsoluteGaloisGroup F ⧸ I)
    (N := ↥(FixedPoints.addSubgroup (↥I) (ZMod p)))
    (K := AbsoluteGaloisGroup F ⧸ I) (P := ZMod p)
    (φ := ContinuousMonoidHom.id _) (f := coeffSubAddHom (p := p) (I := I))
    (hf := continuous_of_discreteTopology)
    (hequiv := coeffSubAddHom_smul (F := F) (p := p) I)
    (ψ := ContinuousMonoidHom.id _)
    (q := (FixedPoints.addSubgroup (↥I) (ZMod p)).subtype)
    (hq := continuous_of_discreteTopology)
    (hequivq := fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) I k n)]
  have hcomp_ids : (ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ I)).comp
      (ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ I))
      = ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ I) := rfl
  rw [hcomp_ids]
  -- ⚠ `rw` 直接换 `subtype ∘ e → id` 会撞「连续性证明依赖被换项」（D56 同型）⟹ 用 `explicitMap1_congr_of_eq`
  have hcongr := explicitMap1_congr_of_eq (G := AbsoluteGaloisGroup F ⧸ I) (M := ZMod p)
    (H := AbsoluteGaloisGroup F ⧸ I) (N := ZMod p)
    (φ := ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ I))
    (ψ := ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ I))
    (f := (FixedPoints.addSubgroup (↥I) (ZMod p)).subtype.comp
      (coeffSubAddHom (p := p) (I := I)))
    (q := AddMonoidHom.id (ZMod p))
    (hf := continuous_of_discreteTopology) (hq := continuous_of_discreteTopology)
    (hφ := fun _ _ => rfl) (hψ := fun _ _ => rfl)
    (rfl : ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ I)
      = ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ I))
    (subtype_comp_coeffSubAddHom (F := F) (p := p) (I := I))
  rw [hcongr]
  exact explicitMap1_id _ _

section Inertia

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- `res1V (h1ToVEquiv y) = explicitRes1 y`（`res1V` 的定义 ＋ `symm_apply_apply`）。 -/
theorem res1V_h1ToVEquiv (y : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    res1V (F := F) (p := p) (KummerBridge.h1ToVEquiv (F := F) (p := p) y)
      = explicitRes1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) y := by
  rw [res1V_apply, AddEquiv.symm_apply_apply]

/-- ★★★★ **`em_{Γ⧸I,φ,id}` ＝ `explicitInfl1 ∘ em_e`**（`Hyp748` ＋ 本件的一级右逆）。 -/
theorem explicitMap1_quot_id_eq_infl_comp_coeff (z : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)) :
    explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
        (AbsoluteGaloisGroup F) (ZMod p)
        (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F)) (AddMonoidHom.id (ZMod p))
        continuous_of_discreteTopology (fun _ _ => rfl) z
      = explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F)
          (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
            (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
            ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
            (ContinuousMonoidHom.id _) (coeffSubAddHom (p := p) (I := inertiaLoc F))
            continuous_of_discreteTopology
            (coeffSubAddHom_smul (F := F) (p := p) (inertiaLoc F)) z) := by
  rw [explicitInfl1_eq_comp_coeff (F := F) (p := p) (inertiaLoc F)]
  have hright := congrArg (fun f => f z)
    (explicitMap1_subtype_comp_coeff (F := F) (p := p) (inertiaLoc F))
  rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hright
  rw [hright]

/-- ★★★★ **`em_{Γ⧸I,φ,id}` 单射**（`explicitInfl1` 单 ＋ 一级右逆）。 -/
theorem explicitMap1_quot_id_injective :
    Function.Injective (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
      (AbsoluteGaloisGroup F) (ZMod p)
      (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F)) (AddMonoidHom.id (ZMod p))
      continuous_of_discreteTopology (fun _ _ => rfl)) := by
  intro a b hab
  have hright : ∀ z : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p),
      explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
          (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
          (ContinuousMonoidHom.id _)
          (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype
          continuous_of_discreteTopology
          (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) (inertiaLoc F) k n)
          (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
            (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
            ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
            (ContinuousMonoidHom.id _) (coeffSubAddHom (p := p) (I := inertiaLoc F))
            continuous_of_discreteTopology
            (coeffSubAddHom_smul (F := F) (p := p) (inertiaLoc F)) z) = z := by
    intro z
    have h := congrArg (fun f => f z)
      (explicitMap1_subtype_comp_coeff (F := F) (p := p) (inertiaLoc F))
    rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at h
    exact h
  have h1 : explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F)
        (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
          (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
          (ContinuousMonoidHom.id _) (coeffSubAddHom (p := p) (I := inertiaLoc F))
          continuous_of_discreteTopology
          (coeffSubAddHom_smul (F := F) (p := p) (inertiaLoc F)) a)
      = explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F)
        (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
          (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
          (ContinuousMonoidHom.id _) (coeffSubAddHom (p := p) (I := inertiaLoc F))
          continuous_of_discreteTopology
          (coeffSubAddHom_smul (F := F) (p := p) (inertiaLoc F)) b) := by
    rw [← explicitMap1_quot_id_eq_infl_comp_coeff (F := F) (p := p) a,
      ← explicitMap1_quot_id_eq_infl_comp_coeff (F := F) (p := p) b]
    exact hab
  have h2 := explicitInfl1_injective (G := AbsoluteGaloisGroup F) (M := ZMod p)
    (N := inertiaLoc F) h1
  rw [← hright a, ← hright b, h2]

/-- ★★★★ **`infl1Res` 单射**（`infl1Res_eQ` ＋ `em_{φ,id}` 单 ＋ `h1ToVEquiv` 单）。 -/
theorem infl1Res_injective :
    Function.Injective (infl1Res (F := F) (p := p) (inertiaLoc F)) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (eQ (F := F) (p := p) (inertiaLoc F)).surjective a
  obtain ⟨y, rfl⟩ := (eQ (F := F) (p := p) (inertiaLoc F)).surjective b
  rw [infl1Res_eQ, infl1Res_eQ] at hab
  have hx : x = y := explicitMap1_quot_id_injective (F := F) (p := p)
    ((KummerBridge.h1ToVEquiv (F := F) (p := p)).injective hab)
  rw [hx]

/-- ★★★★ **膨胀的像落在 `ker(res₁)`**：`res₁ (infl₁ a) = 0`（`inertiaLoc` 载体）。 -/
theorem res1V_infl1Res_eq_zero (a : ResH1Type (F := F) p (inertiaLoc F)) :
    res1V (F := F) (p := p) (infl1Res (F := F) (p := p) (inertiaLoc F) a) = 0 := by
  obtain ⟨x, rfl⟩ := (eQ (F := F) (p := p) (inertiaLoc F)).surjective a
  rw [infl1Res_eQ, res1V_h1ToVEquiv, explicitMap1_quot_id_eq_infl_comp_coeff]
  have h0 := congrArg (fun f => f (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
      (AbsoluteGaloisGroup F ⧸ inertiaLoc F) ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
      (ContinuousMonoidHom.id _) (coeffSubAddHom (p := p) (I := inertiaLoc F))
      continuous_of_discreteTopology
      (coeffSubAddHom_smul (F := F) (p := p) (inertiaLoc F)) x))
    (explicitRes1_comp_explicitInfl1 (G := AbsoluteGaloisGroup F) (M := ZMod p)
      (N := inertiaLoc F))
  simpa using h0

/-- `v̄ (infl₁ a) = 0`（`Hyp747` 的 `v̄ = 0 ⟺ res₁ = 0`）。 -/
theorem infl1Res_valLinOf_eq_zero (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p)
    {v : Fˣ →* Multiplicative ℤ} (hv : ValCompat (F := F) v)
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (a : ResH1Type (F := F) p (inertiaLoc F)) :
    valLinOf (F := F) (p := p) v hp (infl1Res (F := F) (p := p) (inertiaLoc F) a) = 0 :=
  (valLinOf_eq_zero_iff_res1V_eq_zero_of_valCompat (F := F) (p := p) hp hpq v hv hπ
    (infl1Res (F := F) (p := p) (inertiaLoc F) a)).mpr
    (res1V_infl1Res_eq_zero (F := F) (p := p) a)

/-- ★★★★★ **`infl₁ : ResH1Type →ₗ VKG`**（核心striction 到 `ker v̄`）。 -/
noncomputable def infl1ResToVKG (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p)
    {v : Fˣ →* Multiplicative ℤ} (hv : ValCompat (F := F) v)
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) :
    ResH1Type (F := F) p (inertiaLoc F) →ₗ[ZMod p] VKG F p v hp where
  toFun a := ⟨infl1Res (F := F) (p := p) (inertiaLoc F) a,
    infl1Res_valLinOf_eq_zero (F := F) (p := p) hp hpq hv hπ a⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- ★★★★★ **`F5` 第二半**：`ResH1Type ≃ₗ VKG`
（满＝`Hyp749.unramifiedKummer`；单＝`infl1Res_injective`）。 -/
noncomputable def infl1EquivVKG (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p)
    {v : Fˣ →* Multiplicative ℤ} (hv : ValCompat (F := F) v)
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) :
    ResH1Type (F := F) p (inertiaLoc F) ≃ₗ[ZMod p] VKG F p v hp :=
  LinearEquiv.ofBijective
    (infl1ResToVKG (F := F) (p := p) hp hpq hv hπ)
    ⟨fun a b hab => infl1Res_injective (F := F) (p := p) (by
        have h := congrArg (Subtype.val) hab
        simpa [infl1ResToVKG] using h),
      fun y => by
        obtain ⟨a, ha⟩ := unramifiedKummer (F := F) (p := p) hp hpq v hv hπ y
        refine ⟨a, Subtype.ext ?_⟩
        simpa [infl1ResToVKG] using ha⟩

end Inertia

end L20261018

#print axioms L20261018.explicitMap1_quot_id_eq_infl_comp_coeff
#print axioms L20261018.explicitMap1_quot_id_injective
#print axioms L20261018.infl1Res_injective
#print axioms L20261018.res1V_infl1Res_eq_zero
#print axioms L20261018.infl1EquivVKG
