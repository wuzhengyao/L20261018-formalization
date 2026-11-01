import L20261018.Ch2.Hensel.ResidueMap.Step084_explicit_cup01_nonzero

/-!
# S78 R1：把 `prop:prelim-residue`(1) 的 `d` **无条件造出来** —— 第 4 章无条件化的最后一段

## 靶子

第 4 章的 4 条陈述（`Hyp763`／`Hyp764`）已机检，但它们吃
`Hyp342.tameResidueFacts_Galo_of_residueMap` 的两条**残差映射值公式**

```
hd_infl    : d (cup y z)         = 0
hd_cup_pi  : d (cup y (π))       = y
```

（＝论文 `prop:prelim-residue`(1)：`∂_q(inf ξ) = 0`、`∂_q(inf η ∪ (π)) = η`）。本件把这两条**做掉**：
不再「假设存在 `d`」，而是**造出** `d = F5 ∘ ∂²`。

## 路线（`GAP3-PLAN` §23.5 ＋ §23.3，零新数学）

```
(1) 系数桥   `coeffInclH1 x := em_{Γ⧸I,id,coeffSubAddHom} x`      （`ZMod p → Mᴵ`，库内 `explicitMap1`）
             `explicitInfl1 (coeffInclH1 x) = em_{φ,id} x`          （库内 `explicitMap1_quot_id_eq_infl_comp_coeff`）
             `infl1Res (eQ x) = h1ToVEquiv (explicitInfl1 (coeffInclH1 x))`
(2) 取值     `projLin a₀ = ∂²(cup a₀ π) = − explicitCup01 …(contM)·(coeffInclH1 x)`
             ← `Hyp796`（第 5 步 (c) 载体比较）
(3) 非零     `x ≠ 0 ⟹ coeffInclH1 x ≠ 0 ⟹ explicitCup01 … ≠ 0`（`Hyp799`，第 5 步 (b)）
             ⟹ **`projLin a₀ ≠ 0`**
(4) 单射     `Hyp134.ker_dependent`（**零假设**：`ker v̄` 内任两元相关）⟹ `projLin` 单
             （**不用维数理论、不用 `FiniteDimensional`、不用杯积非退化性**）
(5) 左逆     `Hyp779.exists_leftInverse_of_injective` ⟹ `F5 ∘ projLin = id`
(6) 装配     `d := F5 ∘ ∂²`；`hd_infl` ← `Hyp757.hd_infl_of_linear`（**对任意线性 `F5`**）；
             `hd_cup_pi` ← `F5 ∘ projLin = id` ⟹ `prop:prelim-residue`(1) **无条件**
```

## 为什么第 (4) 步不需要 `FiniteDimensional`

S77 计划（`GAP3-PLAN` §23.3 第 2 步）原打算用 `finrank_VKG_eq_one`，那要吃
`[FiniteDimensional (ZMod p) (GaloBase.V F p)]` ＋ **杯积非退化性** `∃ a₁ a₂, cup a₁ a₂ ≠ 0`
（两条都**不是**论文假设）。本件改用 `Hyp134.ker_dependent` —— 它把「`ker v̄` 至多一维」
直接写成**任两元相关**，于是「`projLin a₀ ≠ 0` ⟹ `projLin` 单」是纯线性代数，
**两条机器假设同时消失**（`LESSONS` D109）。

## 交付

| 声明 | 内容 |
|---|---|
| **`coeffInclH1`** | `H¹(Γ⧸I, ℤ/p) →+ H¹(Γ⧸I, μ_pᴵ)`（`explicitMap1` 的系数包含） |
| `coeffInclH1_injective` | ★★★ 有左逆（`explicitMap1_subtype_comp_coeff`）⟹ 单 |
| `explicitInfl1_coeffInclH1` | `explicitInfl1 ∘ coeffInclH1 = em_{φ,id}` |
| **`coe_infl1ResToVKG_eQ`** | ★★★★ `↑(infl1ResToVKG (eQ x)) = h1ToVEquiv (explicitInfl1 (coeffInclH1 x))` |
| `projLin_apply` | `projLin y = ∂²(cup ↑y π)`（`def` 级） |
| **`projLin_infl1ResToVKG_eq`** | ★★★★★ `projLin a₀ = − explicitCup01 …` |
| **`projLin_infl1ResToVKG_ne_zero`** | ★★★★★★ `x ≠ 0 ⟹ projLin a₀ ≠ 0` |
| **`projLin_injective`** | ★★★★★★ `projLin` **单射**（零维数假设） |
| **`exists_residueMap`** | ★★★★★★★ **`∃ d`，两条值公式**（`prop:prelim-residue`(1) 无条件） |
| **`tameResidueFacts_uncond`** | ★★★★★★★ **`TameResidueFacts` 无条件**（第 4 章的最后一条假设消失） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
variable (hcop : p.Coprime q)

/-- 技术实例：`I = inertiaLoc F` 闭。 -/
local instance instClosedInertiaLocS78R1 :
    IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 正规。 -/
local instance instNormalInertiaLocS78R1 : (inertiaLoc F).Normal := normal_inertiaLoc F

/-- 技术实例：`μ_pᴵ` 上 `Γ⧸I` 连续作用（`PROMPT-S77` §3 已登记）。 -/
local instance instContSmulMuPInvS78R1 :
    ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)) := inferInstance

/-! ## 1 系数包含 `ℤ/p → μ_pᴵ` 在 `H¹(Γ⧸I, –)` 上 -/

/-- 系数包含 `ZMod p →+ μ_pᴵ` 诱导的 `H¹(Γ⧸I, –)` 映射（`explicitMap1` 形态）。

`π₀(I) = 1` 使 `μ_pᴵ = ℤ/p`（`Hyp751.coeffSubAddHom`），于是 `H¹(Γ⧸I, μ_pᴵ)` 与
`H¹(Γ⧸I, ℤ/p)` 只差这一条系数包含。 -/
noncomputable def coeffInclH1 :
    H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p) →+
      H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
        ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)) :=
  explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
    (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
    ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
    (ContinuousMonoidHom.id _) (coeffSubAddHom (p := p) (I := inertiaLoc F))
    continuous_of_discreteTopology (coeffSubAddHom_smul (F := F) (p := p) (inertiaLoc F))

/-- `coeffInclH1` 的左逆（`explicitMap1_subtype_comp_coeff` 的 `I = inertiaLoc F` 实例）。 -/
theorem subtypeCompCoeffInclH1 :
    (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
        ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
        (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
        (ContinuousMonoidHom.id _)
        (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype
        continuous_of_discreteTopology
        (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p)
          (inertiaLoc F) k n)).comp (coeffInclH1 (F := F) (p := p))
      = AddMonoidHom.id (H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)) :=
  explicitMap1_subtype_comp_coeff (F := F) (p := p) (inertiaLoc F)

/-- ★★★ **`coeffInclH1` 单射**（左逆存在）。 -/
theorem coeffInclH1_injective :
    Function.Injective (coeffInclH1 (F := F) (p := p)) := by
  intro a b hab
  have hcomp := subtypeCompCoeffInclH1 (F := F) (p := p)
  have key : ∀ t : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p),
      (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
        ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
        (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
        (ContinuousMonoidHom.id _)
        (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype
        continuous_of_discreteTopology
        (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p)
          (inertiaLoc F) k n)) (coeffInclH1 (F := F) (p := p) t) = t := by
    intro t
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using
      DFunLike.congr_fun hcomp t
  rw [← key a, ← key b, hab]

/-- `x ≠ 0 ⟹ coeffInclH1 x ≠ 0`。 -/
theorem coeffInclH1_ne_zero {x : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)}
    (hx : x ≠ 0) : coeffInclH1 (F := F) (p := p) x ≠ 0 := by
  intro h
  exact hx (coeffInclH1_injective (F := F) (p := p) (by rw [h, map_zero]))

/-! ## 2 `explicitInfl1 ∘ coeffInclH1` 就是 `ℤ/p` 系数的朴素膨胀 -/

/-- ★★★★ **`explicitInfl1 (coeffInclH1 x)` ＝ `ZMod p` 系数的 `em_{Γ⧸I→Γ, id}`**。

库内 `explicitMap1_quot_id_eq_infl_comp_coeff` 的逐字实例化。 -/
theorem explicitInfl1_coeffInclH1 (x : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)) :
    explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F)
        (coeffInclH1 (F := F) (p := p) x)
      = explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p) (AbsoluteGaloisGroup F)
          (ZMod p) (inertiaLoc F).quotientMkContinuousMonoidHom (AddMonoidHom.id (ZMod p))
          continuous_of_discreteTopology (fun _ _ => rfl) x :=
  (explicitMap1_quot_id_eq_infl_comp_coeff (F := F) (p := p) x).symm

/-- ★★★★ **`infl1Res (eQ x) = h1ToVEquiv (explicitInfl1 (coeffInclH1 x))`**。 -/
theorem infl1Res_eQ_coeff (x : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)) :
    infl1Res (F := F) (p := p) (inertiaLoc F) (eQ (F := F) (p := p) (inertiaLoc F) x)
      = KummerBridge.h1ToVEquiv (F := F) (p := p)
          (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F)
            (coeffInclH1 (F := F) (p := p) x)) := by
  rw [infl1Res_eQ, explicitInfl1_coeffInclH1]

/-- ★★★★ **`a₀ := infl1ResToVKG (eQ x)` 的底层**（`infl1ResToVKG` 的 `toFun` 即 `infl1Res`）。 -/
theorem coe_infl1ResToVKG_eQ (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p)
    {pi0 : Fˣ} (hpi : TauCeti.normalizedValuation F pi0 = Multiplicative.ofAdd (1 : ℤ))
    (x : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)) :
    ((infl1ResToVKG (F := F) (p := p) hp hpq
        (v := TauCeti.normalizedValuation F) (valCompat_normalizedValuation F)
        (π := pi0) hpi (eQ (F := F) (p := p) (inertiaLoc F) x) : GaloBase.V F p))
      = KummerBridge.h1ToVEquiv (F := F) (p := p)
          (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F)
            (coeffInclH1 (F := F) (p := p) x)) := by
  show infl1Res (F := F) (p := p) (inertiaLoc F) (eQ (F := F) (p := p) (inertiaLoc F) x) = _
  exact infl1Res_eQ_coeff (F := F) (p := p) x

/-- `explicitInfl1 (coeffInclH1 x)` 在 `v̄` 下为 `0`（即落在 `ker v̄` 里）。 -/
theorem valLinOf_explicitInfl1_coeffInclH1 (hp : IsUnit (p : F))
    (hpq : ¬ ringChar 𝓀[F] ∣ p) (x : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)) :
    valLinOf (F := F) (p := p) (TauCeti.normalizedValuation F) hp
      (KummerBridge.h1ToVEquiv (F := F) (p := p)
        (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F)
          (coeffInclH1 (F := F) (p := p) x))) = 0 := by
  rw [explicitInfl1_coeffInclH1]
  exact h1ToVEquiv_infl_valLinOf_eq_zero (F := F) (p := p) hp hpq x

/-! ## 3 `projLin` 在 `a₀` 上的值：`− explicitCup01` -/

/-- `projLin` 的取值式（`def` 级展开）。 -/
theorem projLin_apply (hp : IsUnit (p : F))
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    (pi0 : Fˣ) (y : VKG F p (TauCeti.normalizedValuation F) hp) :
    projLin (F := F) (p := p) (q := q) (hcop := hcop) hp pi0 y
      = (AddMonoidHom.toZModLinearMap p (deltaTwoGaloBase' (F := F) p q hcop))
          (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
            (KummerBridge.kummerClass F p hp pi0)) := rfl

/-- ★★★★★ **第 5 步 (c) 落到 `projLin` 上**：`projLin a₀ = − explicitCup01 …(contM z)·yb`。 -/
theorem projLin_infl1ResToVKG_eq (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    {pi0 : Fˣ} (hpi : TauCeti.normalizedValuation F pi0 = Multiplicative.ofAdd (1 : ℤ))
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hp pi0)))
    (x : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)) :
    projLin (F := F) (p := p) (q := q) (hcop := hcop) hp pi0
        (infl1ResToVKG (F := F) (p := p) hp hpq
          (v := TauCeti.normalizedValuation F) (valCompat_normalizedValuation F)
          (π := pi0) hpi (eQ (F := F) (p := p) (inertiaLoc F) x))
      = - explicitCup01 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          (H1 ↥(inertiaLoc F) (ZMod p))
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
          (H1 ↥(inertiaLoc F) (ZMod p))
          (smulPairingH1 (F := F) p) (smulPairingH1_continuous (F := F) p)
          (smulPairingH1_quotient_smul (F := F) p)
          (explicitCoeff0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
            (contInvC (F := F) p (inertiaLoc F)) (contMHom (F := F) p (inertiaLoc F)) z)
          (coeffInclH1 (F := F) (p := p) x) := by
  have hcoe := coe_infl1ResToVKG_eQ (F := F) (p := p) hp hpq (pi0 := pi0) hpi x
  rw [projLin_apply]
  rw [hcoe]
  exact deltaTwoGaloBase'_cup_eq_neg_explicitCup01 (F := F) (p := p) (q := q) (hcop := hcop)
    hp z (coeffInclH1 (F := F) (p := p) x)
    (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
      ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
        (KummerBridge.kummerClass F p hp pi0)))
    hδ rfl

/-! ## 4 非零性：`x ≠ 0 ⟹ projLin a₀ ≠ 0` -/

/-- ★★★★★★ **`projLin a₀ ≠ 0`**（第 5 步 (b) `Hyp799` ＋ 第 5 步 (c) `Hyp796`）。 -/
theorem projLin_infl1ResToVKG_ne_zero (hp : IsUnit (p : F)) (hpq' : ¬ ringChar 𝓀[F] ∣ p)
    (ζ : TameModel F)
    (hζ : ∀ m' : {m' : ℕ // m' ≠ 0 ∧ m'.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m' ζ : ↥(rootsOfUnity (↑m') (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m'))
    (hgen : closedZpowers ζ = ⊤)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    {pi0 : Fˣ} (hpi : TauCeti.normalizedValuation F pi0 = Multiplicative.ofAdd (1 : ℤ))
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hp pi0)))
    {x : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)} (hx : x ≠ 0) :
    projLin (F := F) (p := p) (q := q) (hcop := hcop) hp pi0
        (infl1ResToVKG (F := F) (p := p) hp hpq'
          (v := TauCeti.normalizedValuation F) (valCompat_normalizedValuation F)
          (π := pi0) hpi (eQ (F := F) (p := p) (inertiaLoc F) x)) ≠ 0 := by
  rw [projLin_infl1ResToVKG_eq (F := F) (p := p) (q := q) (hcop := hcop) hp hpq'
    (pi0 := pi0) hpi z hδ x]
  exact neg_ne_zero.mpr (explicitCup01_contM_ne_zero (F := F) (p := p) (q := q)
    (ne_of_coprime (p := p) (q := q) hcop) ζ hζ hgen hp hpq' (pi0 := pi0) hpi z hδ
    (coeffInclH1_ne_zero (F := F) (p := p) hx))

/-! ## 5 单射（`ker_dependent` 路线，零维数假设） -/

/-- ★★★★★★ **`projLin` 单射**。

`Hyp134.ker_dependent`：`ker v̄` 内任两元**相关**。取一条已知 `projLin ≠ 0` 的元素 `b`，
则 `y ∈ span{b} ∨ b ∈ span{y}` 两支都逼出 `y = 0`（若 `projLin y = 0`）。

**不需要** `[FiniteDimensional (ZMod p) (GaloBase.V F p)]`，**不需要**杯积非退化性
（S77 计划的 `finrank_VKG_eq_one` 路线要这两条，见文件头）。 -/
theorem projLin_injective (hp : IsUnit (p : F)) (hpu : IsUnit (p : ↥𝒪[F]))
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    {pi0 : Fˣ} (hπ : TauCeti.normalizedValuation F pi0 = Multiplicative.ofAdd (1 : ℤ))
    {b : VKG F p (TauCeti.normalizedValuation F) hp}
    (hb : projLin (F := F) (p := p) (q := q) (hcop := hcop) hp pi0 b ≠ 0) :
    Function.Injective (projLin (F := F) (p := p) (q := q) (hcop := hcop) hp pi0) := by
  intro y y' hyy'
  have hzero : projLin (F := F) (p := p) (q := q) (hcop := hcop) hp pi0 (y - y') = 0 := by
    rw [map_sub, hyy', sub_self]
  have hker : (y - y' : VKG F p (TauCeti.normalizedValuation F) hp)
      ∈ LinearMap.ker (projLin (F := F) (p := p) (q := q) (hcop := hcop) hp pi0) :=
    LinearMap.mem_ker.mpr hzero
  have hsub : (y - y' : VKG F p (TauCeti.normalizedValuation F) hp) = 0 := by
    rcases ker_dependent (F := F) (p := p) hp (hπ := hπ) hpu
      ((y - y' : VKG F p (TauCeti.normalizedValuation F) hp) : GaloBase.V F p)
      (b : GaloBase.V F p) (y - y').2 b.2 with h | h
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
      have hcs : (y - y' : VKG F p (TauCeti.normalizedValuation F) hp) = c • b :=
        Subtype.ext (by rw [Submodule.coe_smul]; exact hc.symm)
      by_cases hc0 : c = 0
      · rw [hcs, hc0, zero_smul]
      · exfalso
        have hbb : b = c⁻¹ • (y - y') := by
          rw [hcs, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        exact hb (LinearMap.mem_ker.mp (hbb ▸ Submodule.smul_mem (LinearMap.ker
          (projLin (F := F) (p := p) (q := q) (hcop := hcop) hp pi0)) c⁻¹ hker))
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
      exfalso
      have hbs : b = c • (y - y') :=
        Subtype.ext (by rw [Submodule.coe_smul]; exact hc.symm)
      exact hb (LinearMap.mem_ker.mp (hbs ▸ Submodule.smul_mem (LinearMap.ker
        (projLin (F := F) (p := p) (q := q) (hcop := hcop) hp pi0)) c hker))
  exact sub_eq_zero.mp hsub

/-! ## 6 装配：`prop:prelim-residue`(1) 无条件 -/

/-- ★★★★★★★ **`prop:prelim-residue`(1) 无条件化**：**存在** `∂₂ = d` 满足两条值公式。

```
d := F5 ∘ ∂²,   F5 ∘ projLin = id        （Hyp779，由 projLin 单）
hd_infl   ← Hyp757.hd_infl_of_linear（对任意线性 F5）
hd_cup_pi ← F5 (projLin y) = y
```

**`VKG` 平凡时**取 `d := 0`（两条都退化为 `0 = 0`）；**非平凡时**由第 5 节取 `F5`。 -/
theorem exists_residueMap (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q) (hp : IsUnit (p : F)) (hpq' : ¬ ringChar 𝓀[F] ∣ p)
    (hpu : IsUnit (p : ↥𝒪[F])) (ζ : TameModel F)
    (hζ : ∀ m' : {m' : ℕ // m' ≠ 0 ∧ m'.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m' ζ : ↥(rootsOfUnity (↑m') (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m'))
    (hgen : closedZpowers ζ = ⊤)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
    {pi0 : Fˣ} (hpi : TauCeti.normalizedValuation F pi0 = Multiplicative.ofAdd (1 : ℤ))
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hp pi0))) :
    ∃ d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p (TauCeti.normalizedValuation F) hp,
      (∀ y z : VKG F p (TauCeti.normalizedValuation F) hp,
        d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0) ∧
      (∀ y : VKG F p (TauCeti.normalizedValuation F) hp,
        d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
          (KummerBridge.kummerClass F p hp pi0)) = y) := by
  classical
  by_cases htriv : ∀ y : VKG F p (TauCeti.normalizedValuation F) hp, y = 0
  · refine ⟨0, fun y z => rfl, fun y => ?_⟩
    rw [LinearMap.zero_apply]
    exact (htriv y).symm
  · push Not at htriv
    obtain ⟨a₀, ha₀⟩ := htriv
    -- 从非零 `a₀` 造非零 `x`
    set a : ResH1Type (F := F) p (inertiaLoc F) :=
      (infl1EquivVKG (F := F) (p := p) hp hpq'
        (v := TauCeti.normalizedValuation F) (valCompat_normalizedValuation F)
        (π := pi0) hpi).symm a₀ with ha
    have haf : (infl1EquivVKG (F := F) (p := p) hp hpq'
        (v := TauCeti.normalizedValuation F) (valCompat_normalizedValuation F)
        (π := pi0) hpi) a = a₀ := by
      rw [ha]
      exact LinearEquiv.apply_symm_apply _ _
    have han : a ≠ 0 := by
      intro h
      exact ha₀ (by rw [← haf, h, map_zero])
    set x : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p) :=
      (eQ (F := F) (p := p) (inertiaLoc F)).symm a with hx
    have hxa : eQ (F := F) (p := p) (inertiaLoc F) x = a := by
      rw [hx]
      exact AddEquiv.apply_symm_apply _ _
    have hxn : x ≠ 0 := by
      intro h
      exact han (by rw [← hxa, h, map_zero])
    -- 主元素 `b := infl1ResToVKG (eQ x)`，`projLin b ≠ 0`
    set b : VKG F p (TauCeti.normalizedValuation F) hp :=
      infl1ResToVKG (F := F) (p := p) hp hpq'
        (v := TauCeti.normalizedValuation F) (valCompat_normalizedValuation F)
        (π := pi0) hpi (eQ (F := F) (p := p) (inertiaLoc F) x) with hb
    have hbnz : projLin (F := F) (p := p) (q := q) (hcop := hcop) hp pi0 b ≠ 0 :=
      projLin_infl1ResToVKG_ne_zero (F := F) (p := p) (q := q) (hcop := hcop) hp hpq'
        ζ hζ hgen (pi0 := pi0) hpi z hδ hxn
    -- 左逆
    obtain ⟨F5, hF5⟩ := exists_leftInverse_of_injective (F := F) (p := p) (q := q)
      (hcop := hcop) hp pi0 (projLin_injective (F := F) (p := p) (q := q) (hcop := hcop)
        hp hpu (pi0 := pi0) hpi hbnz)
    refine ⟨(F5.comp (AddMonoidHom.toZModLinearMap p (deltaTwoGaloBase' (F := F) p q hcop))),
      fun y z => ?_, fun y => ?_⟩
    · exact hd_infl_of_linear (F := F) (p := p) (q := q) (hcop := hcop) hp
        (valCompat_normalizedValuation F) hpi F5 y z
    · have h1 : projLin (F := F) (p := p) (q := q) (hcop := hcop) hp pi0 y
          = (AddMonoidHom.toZModLinearMap p (deltaTwoGaloBase' (F := F) p q hcop))
              (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
                (KummerBridge.kummerClass F p hp pi0)) :=
        projLin_apply (F := F) (p := p) (q := q) (hcop := hcop) hp pi0 y
      rw [LinearMap.comp_apply, ← h1]
      simpa using LinearMap.congr_fun hF5 y

/-! ## 7 第 4 章的最后一条假设消失 -/

/-- ★★★★★★★ **`TameResidueFacts` 无条件**（`v := normalizedValuation`，`π := π₀`）。

`Hyp342.tameResidueFacts_Galo_of_residueMap` 吃「存在 `d` ＋ 两条值公式」，本件把「存在」变成
`exists_residueMap` 的**构造**。 -/
theorem tameResidueFacts_uncond (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q) (hp : IsUnit (p : F)) (hpq' : ¬ ringChar 𝓀[F] ∣ p)
    (hpu : IsUnit (p : ↥𝒪[F])) (ζ : TameModel F)
    (hζ : ∀ m' : {m' : ℕ // m' ≠ 0 ∧ m'.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m' ζ : ↥(rootsOfUnity (↑m') (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m'))
    (hgen : closedZpowers ζ = ⊤)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
    [HenselianRing (↥(ValuativeRel.valuation F).integer)
      (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer)]
    {π : Fˣ} (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    {z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p)))}
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hp π))) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) (TauCeti.normalizedValuation F) hp)
      (KummerBridge.kummerClass F p hp π) := by
  obtain ⟨d, hd_infl, hd_cup_pi⟩ := exists_residueMap (F := F) (p := p) (q := q) (hcop := hcop)
    hp hpq' hpu ζ hζ hgen (pi0 := π) hπ z hδ
  exact tameResidueFacts_Galo_of_residueMap (F := F) (p := p)
    (v := TauCeti.normalizedValuation F) (π := π) hp d hd_infl hd_cup_pi

end L20261018

#print axioms L20261018.coeffInclH1
#print axioms L20261018.coeffInclH1_injective
#print axioms L20261018.explicitInfl1_coeffInclH1
#print axioms L20261018.infl1Res_eQ_coeff
#print axioms L20261018.coe_infl1ResToVKG_eQ
#print axioms L20261018.projLin_apply
#print axioms L20261018.projLin_infl1ResToVKG_eq
#print axioms L20261018.projLin_infl1ResToVKG_ne_zero
#print axioms L20261018.projLin_injective
#print axioms L20261018.exists_residueMap
#print axioms L20261018.tameResidueFacts_uncond
