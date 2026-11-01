import Hyp789

/-!
# S76 R3：**第 4 步 —— `contM` 与杯积的相容**（`GAP3-PLAN` §11.3 的第 4 步）

## 这一步是什么

`Hyp789` 给出 `∂²(π ⌣ Inf y) = contM (z ⌣ y)`（`z : H⁰(Γ⧸I, Cᴵ)`、`y ∈ H¹(Γ⧸I, μ_p)`）。
第 5 步（非零性）需要把 `contM` **推进**杯积：

```
contM ( z ⌣ y ) = (contM z) ⌣ y
```

这正是 **NSW (1.4.2) 的 `(0,1)` 系数映射自然性**，**库内已有**：
`TauCeti.ContCohomology.explicitCoeff1_explicitCup01`（`Cup/Naturality.lean:361`）。
本件只做**实例化** —— 填好两侧配对并验证 `hpair`：

```
hpair : contM (x • m) = x • contM m          m : Cᴵ, x : μ_p
      ⟸ contInvC 的标量 = nsmul（conv_lhs ＋ ZMod.natCast_zmod_val）
      ⟸ contM 加性（contM_add）⟹ map_nsmul
      ⟸ H1(I,μ_p) 的标量 = nsmul
```

## 交付

| 声明 | 内容 |
|---|---|
| **`contInvC_smul_eq_nsmul_val`**／**`h1Inertia_smul_eq_nsmul_val`** | 两侧 `ZMod p`-标量 = `nsmul` |
| **`smulPairingH1`**＋`_apply`／`_continuous`／`_quotient_smul` | 配对 `H1(I,μ_p) × μ_p → H1(I,μ_p)`（标量作用）及其 `Γ⧼I`-等变性 |
| **`contM_fixedPointsPairing`** | ★★★ `hpair`：`contM (x • m) = x • contM m` |
| **`contM_coeffMap_explicitCup01`** | ★★★★★ **第 4 步**：`contM_coeffMap (z ⌣ y) = (contM z) ⌣ y` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
variable [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
variable [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
  ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))]

local instance instClosedInertiaLocS76R3 :
    IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F
local instance instNormalInertiaLocS76R3 : (inertiaLoc F).Normal := normal_inertiaLoc F
local instance instCompactInertiaLocS76R3 : CompactSpace ↥(inertiaLoc F) :=
  isCompact_iff_compactSpace.mp (isClosed_inertiaLoc F).isCompact

/-! ## 1 两侧标量 = `nsmul` -/

/-- **`Cᴵ = C^I` 的 `ZMod p`-标量就是 `nsmul`**（`a • c = a.val • c`）。 -/
theorem contInvC_smul_eq_nsmul_val (a : ZMod p) (c : contInvC (F := F) p (inertiaLoc F)) :
    a • c = a.val • c := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [Nat.cast_smul_eq_nsmul]

/-- **`H¹(I, μ_p)` 的 `ZMod p`-标量就是 `nsmul`**。 -/
theorem h1Inertia_smul_eq_nsmul_val (a : ZMod p) (x : H1 ↥(inertiaLoc F) (ZMod p)) :
    a • x = a.val • x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [Nat.cast_smul_eq_nsmul]

/-- **`Γ⧼I` 在 `μ_pᴵ` 上作用平凡**（`μ_p = ZMod p` 的 `Γ`-作用平凡）。 -/
theorem quotient_smul_muPInv_trivial (g : AbsoluteGaloisGroup F ⧸ inertiaLoc F)
    (x : ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))) : g • x = x :=
  TauCeti.quotient_smul_fixedPoints_addSubgroup_eq_of_smul_eq (H := inertiaLoc F)
    (fun (g : AbsoluteGaloisGroup F) (m : ZMod p) => GaloBase.muP_ρ (K := F) (p := p) g m) g x

/-- **`Γ⧼I` 在 `μ_p = ZMod p` 上作用平凡**。 -/
theorem quotient_smul_zmod_trivial (g : AbsoluteGaloisGroup F ⧸ inertiaLoc F) (a : ZMod p) :
    g • a = a := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective (inertiaLoc F) g
  exact GaloBase.muP_ρ (K := F) (p := p) γ a

/-! ## 2 `H¹(I, μ_p)` 上的标量配对 -/

/-- 配对 `H¹(I,μ_p) × μ_pᴵ → H¹(I,μ_p)`：标量作用（第二个变量取 `μ_pᴵ = ZMod p`）。 -/
noncomputable def smulPairingH1 :
    H1 ↥(inertiaLoc F) (ZMod p) →+
      (↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)) →+
        H1 ↥(inertiaLoc F) (ZMod p)) where
  toFun m :=
    { toFun := fun x => (x : ZMod p) • m
      map_zero' := by
        show ((0 : ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))) : ZMod p) • m = 0
        rw [show ((0 : ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))) : ZMod p) = 0 from rfl]
        exact zero_smul (ZMod p) m
      map_add' := fun a b => by
        show (((a + b : ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))) : ZMod p)) • m
          = (a : ZMod p) • m + (b : ZMod p) • m
        rw [show (((a + b : ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))) : ZMod p))
          = (a : ZMod p) + (b : ZMod p) from rfl]
        exact add_smul (a : ZMod p) (b : ZMod p) m }
  map_zero' := by
    refine AddMonoidHom.ext fun x => ?_
    exact smul_zero _
  map_add' := fun m m' => by
    refine AddMonoidHom.ext fun x => ?_
    exact smul_add _ m m'

/-- `smulPairingH1` 的取值：`smulPairingH1 m x = x • m`。 -/
theorem smulPairingH1_apply (m : H1 ↥(inertiaLoc F) (ZMod p))
    (x : ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))) :
    smulPairingH1 (F := F) p m x = (x : ZMod p) • m := (rfl)

/-- `smulPairingH1` 连续（两边都离散）。 -/
theorem smulPairingH1_continuous :
    Continuous fun q : H1 ↥(inertiaLoc F) (ZMod p) ×
        ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)) =>
      smulPairingH1 (F := F) p q.1 q.2 :=
  continuous_of_discreteTopology

/-- `smulPairingH1` 的 `Γ⧼I`-等变性。 -/
theorem smulPairingH1_quotient_smul (g : AbsoluteGaloisGroup F ⧸ inertiaLoc F)
    (m : H1 ↥(inertiaLoc F) (ZMod p))
    (x : ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))) :
    smulPairingH1 (F := F) p (g • m) (g • x) = g • smulPairingH1 (F := F) p m x := by
  show (((g • x : ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))) : ZMod p)) • (g • m)
    = g • (((x : ZMod p)) • m)
  rw [quotient_smul_muPInv_trivial (F := F) p g x]
  rw [h1Inertia_smul_eq_nsmul_val (F := F) p ((x : ZMod p)) (g • m),
    h1Inertia_smul_eq_nsmul_val (F := F) p ((x : ZMod p)) m]
  exact (map_nsmul (DistribSMul.toAddMonoidHom (H1 ↥(inertiaLoc F) (ZMod p)) g)
    ((x : ZMod p)).val m).symm

/-- `contM` 的加性同态形态（本件自用；`Hyp579.contMAddHom` 不在本条 import 链上）。 -/
noncomputable def contMAddHomS76 :
    contInvC (F := F) p (inertiaLoc F) →+ H1 ↥(inertiaLoc F) (ZMod p) where
  toFun := contM (F := F) p (inertiaLoc F)
  map_zero' := contM_zero (F := F) p (inertiaLoc F)
  map_add' := fun x y => contM_add (F := F) p (inertiaLoc F) x y

/-- `contMAddHomS76` 就是 `contM`。 -/
theorem contMAddHomS76_apply (x : contInvC (F := F) p (inertiaLoc F)) :
    contMAddHomS76 (F := F) p x = contM (F := F) p (inertiaLoc F) x := (rfl)

/-! ## 3 `hpair`：`contM` 与标量作用相容 -/

/-- ★★★ **`hpair`**：`smulPairingH1 (contM m) x = contM (μᴺ m x)`（`m : Cᴵ`、`x : μ_p`）。

`contM` 只是加性映射，但这已足够：`ZMod p`-标量是 `nsmul`（两侧各用一次标量引理），
`map_nsmul` 一步给出。 -/
theorem contM_fixedPointsPairing (m : contInvC (F := F) p (inertiaLoc F))
    (x : ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))) :
    smulPairingH1 (F := F) p (contM (F := F) p (inertiaLoc F) m) x
      = contM (F := F) p (inertiaLoc F)
          (((inertiaLoc F).fixedPointsPairing (smulPairingC (F := F) p)
            (fun n => smulPairingC_equivariant (F := F) p (n : AbsoluteGaloisGroup F))) m x) := by
  show ((x : ZMod p)) • contM (F := F) p (inertiaLoc F) m = _
  have hμ : (((inertiaLoc F).fixedPointsPairing (smulPairingC (F := F) p)
      (fun n => smulPairingC_equivariant (F := F) p (n : AbsoluteGaloisGroup F))) m x :
        contC (F := F) p) = ((x : ZMod p)) • (m : contC (F := F) p) := by
    rw [Subgroup.coe_fixedPointsPairing, smulPairingC_apply]
  have hsub : (((inertiaLoc F).fixedPointsPairing (smulPairingC (F := F) p)
      (fun n => smulPairingC_equivariant (F := F) p (n : AbsoluteGaloisGroup F))) m x)
      = ((x : ZMod p)).val • m := by
    refine Subtype.ext ?_
    rw [hμ, contC_smul_eq_nsmul_val (F := F) p]
    rfl
  conv_lhs => rw [← ZMod.natCast_zmod_val (x : ZMod p)]
  rw [Nat.cast_smul_eq_nsmul, hsub]
  exact (map_nsmul (contMAddHomS76 (F := F) p) ((x : ZMod p)).val m).symm

/-! ## 4 主定理：第 4 步 -/

/-- ★★★★★ **第 4 步（`GAP3-PLAN` §11.3）**：`contM` 与 `(0,1)` 杯积相容。

```
contM_coeffMap ( z ⌣ y ) = (contM z) ⌣ y        z ∈ H⁰(Γ⧸I, Cᴵ), y ∈ H¹(Γ⧸I, μ_p)
```

由库内 **NSW (1.4.2)** 系数映射自然性 `explicitCoeff1_explicitCup01` 实例化而来；
`hpair` 即 `contM_fixedPointsPairing`。 -/
theorem contM_coeffMap_explicitCup01
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (y : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))) :
    contM_coeffMap (F := F) p (inertiaLoc F)
        (explicitCup01 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))
          ((inertiaLoc F).fixedPointsPairing (smulPairingC (F := F) p)
            (fun n => smulPairingC_equivariant (F := F) p (n : AbsoluteGaloisGroup F)))
          (Subgroup.continuous_fixedPointsPairing (inertiaLoc F) (smulPairingC (F := F) p)
            (fun n => smulPairingC_equivariant (F := F) p (n : AbsoluteGaloisGroup F))
            continuous_of_discreteTopology)
          (Subgroup.fixedPointsPairing_quotient_smul (inertiaLoc F) (smulPairingC (F := F) p)
            (smulPairingC_equivariant (F := F) p)) z y)
      = explicitCup01 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          (H1 ↥(inertiaLoc F) (ZMod p))
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
          (H1 ↥(inertiaLoc F) (ZMod p))
          (smulPairingH1 (F := F) p) (smulPairingH1_continuous (F := F) p)
          (smulPairingH1_quotient_smul (F := F) p)
          (explicitCoeff0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
            (contInvC (F := F) p (inertiaLoc F)) (contMHom (F := F) p (inertiaLoc F)) z)
          y := by
  have key := explicitCoeff1_explicitCup01 (G := AbsoluteGaloisGroup F ⧸ inertiaLoc F)
    (M := contInvC (F := F) p (inertiaLoc F))
    (N := ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)))
    (P := contInvC (F := F) p (inertiaLoc F))
    (M' := H1 ↥(inertiaLoc F) (ZMod p))
    (N' := ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)))
    (P' := H1 ↥(inertiaLoc F) (ZMod p))
    ((inertiaLoc F).fixedPointsPairing (smulPairingC (F := F) p)
      (fun n => smulPairingC_equivariant (F := F) p (n : AbsoluteGaloisGroup F)))
    (Subgroup.continuous_fixedPointsPairing (inertiaLoc F) (smulPairingC (F := F) p)
      (fun n => smulPairingC_equivariant (F := F) p (n : AbsoluteGaloisGroup F))
      continuous_of_discreteTopology)
    (Subgroup.fixedPointsPairing_quotient_smul (inertiaLoc F) (smulPairingC (F := F) p)
      (smulPairingC_equivariant (F := F) p))
    (smulPairingH1 (F := F) p) (smulPairingH1_continuous (F := F) p)
    (smulPairingH1_quotient_smul (F := F) p)
    (contMHom (F := F) p (inertiaLoc F)) (DistribMulActionHom.id _)
    (contMHom (F := F) p (inertiaLoc F))
    continuous_of_discreteTopology continuous_of_discreteTopology
    (fun m x => (contM_fixedPointsPairing (F := F) p m x).symm)
    z y
  simpa only [contM_coeffMap, explicitCoeff1_id, AddMonoidHom.id_apply] using key

/-! ## 5 合成：**GS 6.8.4 的 `p = q = 1` 支**的完整取值公式 -/

/-- ★★★★★★ **GS 6.8.4（`p = q = 1`）在本战役的机检形态**：

`z ∈ H⁰(Γ⧸I, Cᴵ)`、`y ∈ H¹(Γ⧸I, μ_p)`、`π ∈ H¹(Γ, μ_p)`，且 `δ⁰(Inf z) = π`。则

```
∂²(π ⌣ Inf y) = (contM z) ⌣ y        （在 H¹(Γ⧼I, H¹(I,μ_p)) 里）
```

`Hyp789` 给左边 `= contM (Inf z ⌣ Inf y) = contM (z ⌣ y)`，本件第 4 步把 `contM` 推进杯积。
**这是第 3–4 步的合取**；第 5 步（非零性）只剩"`contM z` 生成 `H¹(I,μ_p)`、`y ≠ 0`
⟹ 右边 `≠ 0`"。 -/
theorem deltaTwoCarrierInertia_cup_eq_value
    (q : ℕ) [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q)
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (y : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)))
    (π : continuousCohomology 1
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)))
    (hπ : ((contCoindSES (F := F) p).delta 0).hom
        (h0Emb (F := F) p
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z)) = π) :
    deltaTwoCarrierInertia (F := F) p q hcop
        (cup11A (F := F) p π
          (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
            (explicitInfl1 (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) y)))
      = explicitCup01 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          (H1 ↥(inertiaLoc F) (ZMod p))
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
          (H1 ↥(inertiaLoc F) (ZMod p))
          (smulPairingH1 (F := F) p) (smulPairingH1_continuous (F := F) p)
          (smulPairingH1_quotient_smul (F := F) p)
          (explicitCoeff0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
            (contInvC (F := F) p (inertiaLoc F)) (contMHom (F := F) p (inertiaLoc F)) z)
          y := by
  rw [deltaTwoCarrierInertia_cup_eq (F := F) p q hcop z y π hπ]
  exact contM_coeffMap_explicitCup01 (F := F) p z y

end L20261018

#print axioms L20261018.contInvC_smul_eq_nsmul_val
#print axioms L20261018.h1Inertia_smul_eq_nsmul_val
#print axioms L20261018.quotient_smul_muPInv_trivial
#print axioms L20261018.quotient_smul_zmod_trivial
#print axioms L20261018.smulPairingH1_continuous
#print axioms L20261018.smulPairingH1_quotient_smul
#print axioms L20261018.contM_fixedPointsPairing
#print axioms L20261018.contM_coeffMap_explicitCup01
#print axioms L20261018.deltaTwoCarrierInertia_cup_eq_value
