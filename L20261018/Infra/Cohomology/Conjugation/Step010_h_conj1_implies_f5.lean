import L20261018.Infra.Cohomology.Conjugation.Step009_h_conj1_carrier_inputs

/-!
# S72 R8：`H-conj1` ⟹ **`F5` 第一半**（系数变换 `H¹(Γ⧸I, H¹(I,ℤ/p)) ≃+ H¹(Γ⧸I, ℤ/p)`）

## 位置（`prop:prelim-residue` 无条件化的链条）

```
H-conj1（Hyp762）
  ⟹ Γ⧸I 在 H¹(I,ℤ/p) 上作用平凡          ★`quotient_smul_eq_self`
  ⟹ H¹(I,ℤ/p) ≅ ℤ/p 且**与 Γ⧸I-作用交换**   ★`h1InertiaAddEquiv` ＋ 交换性
  ⟹ explicitCoeff1Equiv（TauCeti）
  ⟹ H¹(Γ⧸I, H¹(I,ℤ/p)) ≃+ H¹(Γ⧸I, ℤ/p)     ★`coeffChangeEquiv`（本件主交付）
  ⟹ F5 = infl1EquivVKG ∘ 第一半 ⟹ hd_cup_pi ⟹ prop:prelim-residue(1)
```

## 交付

| 声明 | 内容 |
|---|---|
| **`quotient_smul_eq_self`** | ★★★★ `Conj1Trivial` ⟹ **`Γ⧸I` 在 `H¹(I,ℤ/p)` 上逐点固定**（把具名假设搬成商群形态） |
| `h1InertiaAddEquiv` | `H¹(I,ℤ/p) ≃+ ℤ/p`（`Hyp765.h1InertiaLinearEquiv` 的加性形） |
| **`coeffChangeEquiv`** | ★★★★★ **`H¹(Γ⧸I, H¹(I,ℤ/p)) ≃+ H¹(Γ⧸I, ℤ/p)`**（`explicitCoeff1Equiv` ＋ 上一条） |

**⟹ 本件之后，`F5` 的**唯一**剩余条件就是具名假设 `H-conj1`**——系数侧的交换性不再欠。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-! ## ① `Conj1Trivial` ⟹ `Γ⧸I` 作用平凡（商群形态） -/

/-- ★★★★ **`H-conj1` ⟹ `Γ⧸I` 在 `H¹(I,ℤ/p)` 上逐点固定**。

`instDistribMulActionQuotientH1` 的 `•` 沿 `conjEndQuot` 下降，而 `conjEndQuot (⟦g⟧) = explicitConj1 I g`
（`Hyp578.conjEndQuot_apply`）⟹ 直接由 `H-conj1` 得。 -/
theorem quotient_smul_eq_self (h : Conj1Trivial F p)
    (g : AbsoluteGaloisGroup F ⧸ inertiaLoc F)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) : g • x = x := by
  induction g using Quotient.inductionOn with
  | h gg =>
    show (instSMulQuotientH1 (inertiaLoc F)).smul
      (⟦gg⟧ : AbsoluteGaloisGroup F ⧸ inertiaLoc F) x = x
    rw [← conjEndQuot_apply (inertiaLoc F)]
    exact h gg x

/-! ## ② `H¹(I,ℤ/p) ≃+ ℤ/p`（加性形，供 `explicitCoeff1Equiv` 消费） -/

/-- `Hyp765.h1InertiaLinearEquiv` 的加性形。 -/
noncomputable def h1InertiaAddEquiv (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hx : x ≠ 0) :
    H1 ↥(inertiaLoc F) (ZMod p) ≃+ ZMod p :=
  (h1InertiaLinearEquiv (F := F) (p := p) (q := q) hpq ζ hζ hgen x hx).symm.toAddEquiv

/-! ## ③ `F5` 第一半：`explicitCoeff1Equiv` -/

section CoeffChange

variable [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
variable [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
variable [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
  (H1 ↥(inertiaLoc F) (ZMod p))]

/-- ★★★★★ **`F5` 第一半**：`H¹(Γ⧸I, H¹(I,ℤ/p)) ≃+ H¹(Γ⧸I, ℤ/p)`。

由 `TauCeti.ContCohomology.explicitCoeff1Equiv` ＋ 本件的两条输入：
* **交换性**：`e (g • m) = e m = g • e m`——第一个等号是 `quotient_smul_eq_self`（`H-conj1`），
  第二个是 `Γ⧸I` 在 `ℤ/p` 上作用平凡（`rfl`，因 `μ_p ⊆ F`）；
* **连续性**：两侧都是离散拓扑（`continuous_of_discreteTopology`）。 -/
noncomputable def coeffChangeEquiv (h : Conj1Trivial F p)
    (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hx : x ≠ 0) :
    H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p)) ≃+
      H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p) :=
  explicitCoeff1Equiv (G := AbsoluteGaloisGroup F ⧸ inertiaLoc F)
    (M := H1 ↥(inertiaLoc F) (ZMod p)) (N := ZMod p)
    (h1InertiaAddEquiv (F := F) (p := p) (q := q) hpq ζ hζ hgen x hx)
    continuous_of_discreteTopology
    continuous_of_discreteTopology
    (fun g m => by
      show (h1InertiaAddEquiv (F := F) (p := p) (q := q) hpq ζ hζ hgen x hx) (g • m) = g •
        (h1InertiaAddEquiv (F := F) (p := p) (q := q) hpq ζ hζ hgen x hx) m
      rw [quotient_smul_eq_self (F := F) (p := p) h g m]
      rfl)

end CoeffChange

end L20261018

#print axioms L20261018.quotient_smul_eq_self
