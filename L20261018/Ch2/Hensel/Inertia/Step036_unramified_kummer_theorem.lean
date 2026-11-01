import L20261018.Ch2.Hensel.Inertia.Step035_ker_v_eq_ker_res1
import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Comparison

/-!
# S68 R3：★★★ **`Hyp744.UnramifiedKummer` 由假设变定理**（膨胀-限制正合列的载体搬运）

## 结果

`unramifiedKummer_of_inertia`：
对 `I = inertiaLoc F`（惯性子群）、`v = normalizedValuation F`、`char κ ∤ p`，
**`Hyp744.UnramifiedKummer` 成立**（`ker v̄ ⊆ range infl₁`）。⟹ 该具名假设**已消灭**。

## 数学链条（全部为库内已机检件 ＋ 本件三块搬运）

```
v̄ y = 0
  --  Hyp747.valLinOf_eq_zero_iff_res1V_eq_zero
⟹ res₁ y = 0
  --  explicitInfRes_exact（TauCeti：range explicitInfl1 = ker explicitRes1）
⟹ h1ToVEquiv⁻¹ y = explicitInfl1 w       (w : H¹(Γ⧸I, μ_p))
  --  infl1Res_eQ ＋ explicitInfl1_eq_comp_coeff
⟹ y = infl1Res (eQ (… w))
```

## 三块搬运（本件的净增量）

| 缺口 | 内容 | 本件声明 |
|---|---|---|
| **G3a** | `Γ⧸I` 在 `ZMod p` 上的平凡作用实例（`Hyp610` 走 `muPQuot` 正是为避开它） | `instSMulQuotZMod`／`instMulActionQuotZMod`／`instDistribMulActionQuotZMod`／`instSMulCommClassQuotZModInt`／`instContinuousSMulQuotZMod` |
| **G3a'** | 两套载体定义相等 | `restrictScalars_muPQuot_eq`／`restrictScalars_muP_eq`（`rfl`） |
| **G3b-ii** | `restrictScalarsIntEquiv` 与 `map` 交换（库内只有 `≫` 形态） | `restrictScalarsIntEquiv_map` |
| **G3c** | `coeffIdHom` ＝ 恒等系数对（底层函数决定 `TopRep` 态射） | `resRestrictScalarsIntMap_coeffIdHom_eq_pair` |
| **方阵** | `infl1Res ∘ eQ = h1ToVEquiv ∘ explicitMap1` | **`infl1Res_eQ`** |
| 系数分解 | `explicitInfl1` ＝ `ZMod p` 侧 `explicitMap1` ∘ 系数比较 | `explicitInfl1_eq_comp_coeff` |

## 诚实边界

* **`I` 必须是惯性**：原 `def` 对任意正规子群 `I` **是假的**（`I = ⊤` 时 `H¹(1,μ_p) = 0`
  而 `ker v̄ ≠ 0`）。本件的定理形态因此固定 `I = inertiaLoc F`。
* **`v` 取成 `normalizedValuation F`**：`Hyp187.ValCompat v` ＋ `v π = 1` ⟹ `v = normalizedValuation F`
  是**下一件**（`Hyp749`）的内容；本件不含。
* 全部落在 `[IsNonarchimedeanLocalField F]`（完备），与 `Hyp743`／`Hyp511` 同一层级。
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

/-! ## G3a：`Γ⧸I` 在 `ZMod p` 上的平凡作用 -/

section QuotientInstances

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

instance instSMulQuotZMod : SMul (AbsoluteGaloisGroup F ⧸ I) (ZMod p) :=
  ⟨fun _ x => x⟩

instance instMulActionQuotZMod : MulAction (AbsoluteGaloisGroup F ⧸ I) (ZMod p) where
  one_smul := by intro x; rfl
  mul_smul := by intro g h x; rfl

instance instDistribMulActionQuotZMod :
    DistribMulAction (AbsoluteGaloisGroup F ⧸ I) (ZMod p) where
  smul_zero := by intro g; rfl
  smul_add := by intro g x y; rfl

instance instSMulCommClassQuotZModInt :
    SMulCommClass (AbsoluteGaloisGroup F ⧸ I) ℤ (ZMod p) where
  smul_comm := by intro g m x; rfl

instance instContinuousSMulQuotZMod :
    ContinuousSMul (AbsoluteGaloisGroup F ⧸ I) (ZMod p) := ⟨continuous_snd⟩

end QuotientInstances

/-! ## G3b-ii：标量限制与 `map` 交换 -/

section Naturality

variable (p : ℕ) [Fact p.Prime]
variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {X : TopRep (ZMod p) G} {Y : TopRep (ZMod p) H}

/-- ★★★★ **标量限制与 `map` 交换**（元素形态）：
`TauCeti.ContCohomology.map_comp_restrictScalarsIntIso_hom_of_hom`（`RestrictScalars.lean:558`）
的逐点读数。 -/
theorem restrictScalarsIntEquiv_map (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ)
    (z : ↥(continuousCohomology n (TopRep.restrictScalarsInt.obj X)).toModuleCat) :
    restrictScalarsIntEquiv Y n
        (ContinuousCohomology.map φ (TopRep.resRestrictScalarsIntMap (φ : H →* G) f) n z)
      = ContinuousCohomology.map φ f n (restrictScalarsIntEquiv X n z) := by
  have h := congrArg (fun u => (CategoryTheory.ConcreteCategory.hom u) z)
    (TauCeti.ContCohomology.map_comp_restrictScalarsIntIso_hom_of_hom (X := X) (Y := Y) φ f n)
  simp only [CategoryTheory.ConcreteCategory.comp_apply] at h
  rw [restrictScalarsIntEquiv_apply, restrictScalarsIntEquiv_apply]
  exact h

end Naturality

namespace L20261018

section Carrier

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-! ## G3a'：两套载体定义相等（`rfl`，靠上面的实例） -/

/-- `muPQuot` 的标量限制**就是** `ofDiscreteModule ℤ`（否则 `restrictScalarsIntEquiv` 接不上）。 -/
theorem restrictScalars_muPQuot_eq :
    TopRep.restrictScalarsInt.obj (muPQuot (AbsoluteGaloisGroup F ⧸ I) p)
      = TauCeti.ofDiscreteModule ℤ (AbsoluteGaloisGroup F ⧸ I) (ZMod p) := rfl

/-- `GaloBase.muP` 的标量限制**就是** `ofDiscreteModule ℤ`。 -/
theorem restrictScalars_muP_eq :
    TopRep.restrictScalarsInt.obj (GaloBase.muP F p)
      = TauCeti.ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p) := rfl

/-! ## `eQ`：`H¹(Γ⧸I, μ_p)` 的显式模型 ↔ 战役载体 -/

/-- ★★★★ **`H¹(Γ⧸I, μ_p)` 的显式模型 ≃ 战役载体 `ResH1Type`**
（`explicitH1AddEquivContinuousCohomology` ＋ `restrictScalarsIntEquiv`）。 -/
noncomputable def eQ :
    H1 (AbsoluteGaloisGroup F ⧸ I) (ZMod p) ≃+ ResH1Type (F := F) p I :=
  (explicitH1AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F ⧸ I) (M := ZMod p)).trans
    (restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F ⧸ I) (muPQuot (AbsoluteGaloisGroup F ⧸ I) p) 1)

/-- `eQ` 的定义式。 -/
theorem eQ_apply (x : H1 (AbsoluteGaloisGroup F ⧸ I) (ZMod p)) :
    eQ (F := F) (p := p) I x
      = restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F ⧸ I)
          (muPQuot (AbsoluteGaloisGroup F ⧸ I) p) 1
          (explicitH1AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F ⧸ I) (M := ZMod p) x) :=
  rfl

/-- ★★★★ **`coeffIdHom` 的标量限制就是恒等系数对**：两者底层函数都是 `id`
（`ofDiscreteModulePair_eq_of_hom_apply`：`TopRep` 态射由底层函数决定）。 -/
theorem resRestrictScalarsIntMap_coeffIdHom_eq_pair :
    TopRep.resRestrictScalarsIntMap
        (Subgroup.quotientMkContinuousMonoidHom I : AbsoluteGaloisGroup F →* _)
        (coeffIdHom (F := F) p I)
      = ofDiscreteModulePair
          (Subgroup.quotientMkContinuousMonoidHom I : AbsoluteGaloisGroup F →* _)
          (AddMonoidHom.id (ZMod p)).toIntLinearMap (fun _ _ => rfl) := by
  have hψ : ∀ m : ZMod p,
      (TopRep.resRestrictScalarsIntMap
        (Subgroup.quotientMkContinuousMonoidHom I : AbsoluteGaloisGroup F →* _)
        (coeffIdHom (F := F) p I)).hom m
      = (AddMonoidHom.id (ZMod p)).toIntLinearMap m := by
    intro m
    rw [TopRep.resRestrictScalarsIntMap_hom_apply]
    rfl
  exact ofDiscreteModulePair_eq_of_hom_apply
    (R := ℤ) (M := ZMod p) (N := ZMod p)
    (Subgroup.quotientMkContinuousMonoidHom I : AbsoluteGaloisGroup F →* _)
    ((AddMonoidHom.id (ZMod p)).toIntLinearMap) (fun _ _ => rfl) _ hψ


/-! ## G3：平方 `infl1Res ∘ eQ = h1ToVEquiv ∘ explicitMap1` -/

/-- ★★★★★ **膨胀-限制的载体方阵**：`infl1Res (eQ x) = h1ToVEquiv (explicitMap1 … x)`。

链条（全部为库内已机检件 ＋ 本件 G3b-ii／G3c）：
`infl1Res = map φ coeffIdHom 1`（`Hyp610` 定义）
⟶ 标量限制交换（`restrictScalarsIntEquiv_map`）
⟶ `coeffIdHom` 的标量限制 ＝ 恒等系数对（`resRestrictScalarsIntMap_coeffIdHom_eq_pair`）
⟶ 显式↔规范模型方阵（`explicitH1AddEquivContinuousCohomology_map`）。 -/
theorem infl1Res_eQ (x : H1 (AbsoluteGaloisGroup F ⧸ I) (ZMod p)) :
    infl1Res (F := F) (p := p) I (eQ (F := F) (p := p) I x)
      = KummerBridge.h1ToVEquiv (F := F) (p := p)
          (explicitMap1 (AbsoluteGaloisGroup F ⧸ I) (ZMod p) (AbsoluteGaloisGroup F) (ZMod p)
            (Subgroup.quotientMkContinuousMonoidHom I) (AddMonoidHom.id (ZMod p))
            continuous_of_discreteTopology (fun _ _ => rfl) x) := by
  rw [eQ_apply]
  -- ① 标量限制交换（反向用）
  have hnat := restrictScalarsIntEquiv_map (p := p) (G := AbsoluteGaloisGroup F ⧸ I)
    (H := AbsoluteGaloisGroup F) (X := muPQuot (AbsoluteGaloisGroup F ⧸ I) p)
    (Y := GaloBase.muP F p)
    (φ := (Subgroup.quotientMkContinuousMonoidHom I))
    (f := coeffIdHom (F := F) p I) 1
    (explicitH1AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F ⧸ I) (M := ZMod p) x)
  -- ② `infl1Res` 的定义式
  have hdef : infl1Res (F := F) (p := p) I
      (restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F ⧸ I)
        (muPQuot (AbsoluteGaloisGroup F ⧸ I) p) 1
        (explicitH1AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F ⧸ I) (M := ZMod p) x))
      = ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
          (coeffIdHom (F := F) p I) 1
          (restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F ⧸ I)
            (muPQuot (AbsoluteGaloisGroup F ⧸ I) p) 1
            (explicitH1AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F ⧸ I)
              (M := ZMod p) x)) := rfl
  rw [hdef, ← hnat]
  -- ③ `coeffIdHom` 的标量限制就是恒等系数对
  rw [resRestrictScalarsIntMap_coeffIdHom_eq_pair (F := F) (p := p) I]
  -- ④ 显式↔规范模型方阵
  have hsq : (CategoryTheory.ConcreteCategory.hom
        (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
          (ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I :
              AbsoluteGaloisGroup F →* _)
            ((AddMonoidHom.id (ZMod p)).toIntLinearMap) (fun _ _ => rfl)) 1))
        ((explicitH1AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F ⧸ I)
          (M := ZMod p)) x)
      = explicitH1AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F) (M := ZMod p)
          (explicitMap1 (AbsoluteGaloisGroup F ⧸ I) (ZMod p) (AbsoluteGaloisGroup F) (ZMod p)
            (Subgroup.quotientMkContinuousMonoidHom I) (AddMonoidHom.id (ZMod p))
            continuous_of_discreteTopology (fun _ _ => rfl) x) :=
    explicitH1AddEquivContinuousCohomology_map (G := AbsoluteGaloisGroup F ⧸ I)
      (M := ZMod p) (H := AbsoluteGaloisGroup F) (N := ZMod p)
      (Subgroup.quotientMkContinuousMonoidHom I) (AddMonoidHom.id (ZMod p))
      (fun _ _ => rfl) x
  simp only [KummerBridge.h1ToVEquiv]
  exact congrArg (restrictScalarsIntEquiv (GaloBase.muP F p) 1) hsq

/-- `M^I ↪ ZMod p` 与 `Γ⧸I`-作用相容（两侧作用都平凡；`M^I` 一侧走商的普通作用）。 -/
theorem coe_quotient_smul_subtype_fixedPoints (h : AbsoluteGaloisGroup F ⧸ I)
    (m : FixedPoints.addSubgroup (↥I) (ZMod p)) :
    ((FixedPoints.addSubgroup (↥I) (ZMod p)).subtype (h • m) : ZMod p)
      = h • ((FixedPoints.addSubgroup (↥I) (ZMod p)).subtype m) := by
  induction h using QuotientGroup.induction_on with
  | H g =>
    rw [TauCeti.coe_quotient_smul_fixedPoints_addSubgroup]
    show ((g • m : FixedPoints.addSubgroup (↥I) (ZMod p)) : ZMod p) = _
    rw [TauCeti.coe_smul_fixedPoints_addSubgroup]
    rfl


/-- 上一条的 `Γ`-形态（沿商映射）：`subtype (quotientMk k • n) = k • subtype n`。 -/
theorem coe_quotientMk_smul_subtype_fixedPoints (k : AbsoluteGaloisGroup F)
    (n : FixedPoints.addSubgroup (↥I) (ZMod p)) :
    ((FixedPoints.addSubgroup (↥I) (ZMod p)).subtype
        (Subgroup.quotientMkContinuousMonoidHom I k • n) : ZMod p)
      = k • ((FixedPoints.addSubgroup (↥I) (ZMod p)).subtype n) := by
  rw [coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) I]
  rfl

/-! ## 把 `explicitInfl1` 写成 `explicitMap1 … id ∘ 系数比较` -/

/-- ★★★★ **`explicitInfl1` 的系数分解**：
`explicitInfl1`（源系数 `M^I`、目标系数 `ZMod p`）＝ `ZMod p` 系数上的 `explicitMap1`
复合上「`M^I ↪ ZMod p`」这一系数比较（`explicitMap1_comp` 的直接后果）。 -/
theorem explicitInfl1_eq_comp_coeff
    (w : H1 (AbsoluteGaloisGroup F ⧸ I) (FixedPoints.addSubgroup (↥I) (ZMod p))) :
    explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) I w
      = explicitMap1 (AbsoluteGaloisGroup F ⧸ I) (ZMod p) (AbsoluteGaloisGroup F) (ZMod p)
          (Subgroup.quotientMkContinuousMonoidHom I) (AddMonoidHom.id (ZMod p))
          continuous_of_discreteTopology (fun _ _ => rfl)
          (explicitMap1 (AbsoluteGaloisGroup F ⧸ I) (FixedPoints.addSubgroup (↥I) (ZMod p))
            (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
            (ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ I))
            (FixedPoints.addSubgroup (↥I) (ZMod p)).subtype
            continuous_of_discreteTopology
            (coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) I) w) := by
  rw [explicitInfl1_eq_explicitMap1]
  simpa only [explicitMap1_id, AddMonoidHom.id_apply] using
   (explicitMap1_explicitMap1_of_comp_eq
    (AbsoluteGaloisGroup F ⧸ I) ↥(FixedPoints.addSubgroup (↥I) (ZMod p))
    (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
    (ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ I))
    (FixedPoints.addSubgroup (↥I) (ZMod p)).subtype continuous_of_discreteTopology
    (coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) I)
    (AbsoluteGaloisGroup F) (ZMod p)
    (Subgroup.quotientMkContinuousMonoidHom I) (AddMonoidHom.id (ZMod p))
    continuous_of_discreteTopology (fun _ _ => rfl)
    (ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ I))
    (AddMonoidHom.id ↥(FixedPoints.addSubgroup (↥I) (ZMod p))) continuous_id
    (fun _ _ => rfl)
    (Subgroup.quotientMkContinuousMonoidHom I)
    (FixedPoints.addSubgroup (↥I) (ZMod p)).subtype continuous_of_discreteTopology
    (coe_quotientMk_smul_subtype_fixedPoints (F := F) (p := p) I)
    (ContinuousMonoidHom.ext fun _ => rfl) (AddMonoidHom.ext fun _ => rfl) w).symm

/-! ## `UnramifiedKummer` 由假设变定理 -/

/-- ★★★★★★ **`UnramifiedKummer` 不再需要作假设**：对 `I = inertiaLoc F`（惯性子群）、
`v = normalizedValuation F`（归一化赋值），`ker v̄` 的每个类都是 `infl₁` 的像。

链条：
`v̄ y = 0` ⟹ `res₁ y = 0`（`Hyp747.valLinOf_eq_zero_iff_res1V_eq_zero`）
⟹ `h1ToVEquiv⁻¹ y ∈ ker explicitRes1 = range explicitInfl1`（`explicitInfRes_exact`）
⟹ `y = h1ToVEquiv (explicitInfl1 w)`（`w : H¹(Γ⧸I, μ_p)`）
⟹ `y = infl1Res (eQ (… w))`（`infl1Res_eQ` ＋ `explicitInfl1_eq_comp_coeff`）。 -/
theorem unramifiedKummer_of_inertia (hp : IsUnit (p : F))
    (hpq : ¬ ringChar 𝓀[F] ∣ p) :
    UnramifiedKummer (F := F) p (inertiaLoc F) (v := normalizedValuation F) hp := by
  intro y
  have hres : res1V (F := F) (p := p) (y : GaloBase.V F p) = 0 :=
    (valLinOf_eq_zero_iff_res1V_eq_zero (p := p) hp hpq (normalizedValuation F) rfl
      (y : GaloBase.V F p)).mp y.2
  rw [res1V_apply, ← AddMonoidHom.mem_ker, ← explicitInfRes_exact,
    AddMonoidHom.mem_range] at hres
  obtain ⟨w, hw⟩ := hres
  refine ⟨eQ (F := F) (p := p) (inertiaLoc F)
    (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
      (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
      (ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ inertiaLoc F))
      (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype
      continuous_of_discreteTopology
      (coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) (inertiaLoc F)) w), ?_⟩
  rw [infl1Res_eQ, ← explicitInfl1_eq_comp_coeff (p := p) (I := inertiaLoc F) w, hw,
    AddEquiv.apply_symm_apply]

end Carrier

end L20261018

#print axioms L20261018.restrictScalars_muPQuot_eq
#print axioms L20261018.restrictScalars_muP_eq
#print axioms L20261018.eQ
#print axioms L20261018.eQ_apply
#print axioms restrictScalarsIntEquiv_map
#print axioms L20261018.resRestrictScalarsIntMap_coeffIdHom_eq_pair
#print axioms L20261018.infl1Res_eQ
#print axioms L20261018.coe_quotient_smul_subtype_fixedPoints
#print axioms L20261018.coe_quotientMk_smul_subtype_fixedPoints
#print axioms L20261018.explicitInfl1_eq_comp_coeff
#print axioms L20261018.unramifiedKummer_of_inertia
