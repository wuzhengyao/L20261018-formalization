import Hyp712
import Hyp517
import Hyp380

/-!
# S63 R2：把 `Hyp712` 的 C 步落到**战役载体**上（`G = G_F`、`H = inertiaLoc F`、`A = ZMod ℓ`）

## 本件做什么

`Hyp712.subsingleton_cohomology_quot_subgroup` 是抽象形态（任意 `G`、闭子群 `H`、`A`）。
本件把它实例化到 GS 6.8.1 的实际数据：

```
G = AbsoluteGaloisGroup F   （F 为 IsNonarchimedeanLocalField）
H = inertiaLoc F            （GS 的 H = Gal(F^s/F_nr)，即惯性群）
A = ZMod ℓ                  （μ_ℓ 的平凡作用载体，`prop:prelim-residue`(1) 的系数）
Q = Coind_1^G A ⧸ A         （GS (6.14) 的商）
```

`cd_ℓ(H) ≤ 1` 那一格由 `Hyp517.inertiaLoc_subsingleton_Hq`（**无条件**，两载体）供给，
故本件**唯一的假设**仍是 `CoindSubgroupAcyclic (inertiaLoc F)`。

## 机检内容

| 声明 | 内容 |
|---|---|
| `trivialActionZModGalois`／`trivialContinuousSMulZModGalois` | `G_F` 在 `ZMod n` 上的平凡作用（实例） |
| **`inertia_Q_subsingleton_Hq`** | ★★★★★ **`H^j(I, Q) = 0`（`j ≥ 1`）**，唯一假设 = `CoindSubgroupAcyclic` |

## 诚实边界（`D30` comparator 三边界）

* **覆盖率**：本件只覆盖 GS 6.8.1 的 **C 步**（`H^j(H,C)=0`），不覆盖 B／D／E／F 步。
* **假设是否被解除**：`CoindSubgroupAcyclic` **未解除**（下一步 `S63-C2-PLAN.md` §3 路线 ★）。
* **假设类非空**：`Hyp712.coindSubgroupAcyclic_bot` 给 `H = ⊥` 见证；本件的 `H = inertiaLoc F`
  非空由 `inertiaLoc F` 本身的定义保证（`Gal(F^s/F_nr)` 是子群，`Hyp380`）。
* 载体仍是 `IsNonarchimedeanLocalField F`（完备 ＋ 有限剩余域）；论文的「一般 Hensel」需
  `C2` 的「Hensel → 完备」段（`S43-STATUS` §1.9 裁定），本件不触及。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

section GaloisCarrier

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- `G_F` 在 `ZMod n` 上的**平凡作用**（`μ_n` 的系数载体；`p ∤ char κ` ⟹ 惯性在 `μ_p` 上平凡）。 -/
local instance trivialActionZModGalois (n : ℕ) :
    DistribMulAction (AbsoluteGaloisGroup F) (ZMod n) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的 `ContinuousSMul`。 -/
local instance trivialContinuousSMulZModGalois (n : ℕ) :
    ContinuousSMul (AbsoluteGaloisGroup F) (ZMod n) where
  continuous_smul := continuous_snd

/-- `↥(inertiaLoc F)` 在 `ZMod n` 上的平凡作用（`Hyp517` 同款，本件重列以避 `local` 逃逸）。 -/
local instance trivialActionZModInertiaLocI (n : ℕ) :
    DistribMulAction ↥(inertiaLoc F) (ZMod n) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的 `ContinuousSMul`。 -/
local instance trivialContinuousSMulInertiaLocI (n : ℕ) :
    ContinuousSMul ↥(inertiaLoc F) (ZMod n) where
  continuous_smul := continuous_snd

/-- ★★★★★ **GS 6.8.1 的 C 步，在战役载体上**：`H^j(I, Q) = 0`（`j ≥ 1`）。

`Q = Coind_1^{G_F}(ZMod ℓ) ⧸ ZMod ℓ`；`cd_ℓ(I) ≤ 1` 由 `Hyp517`（无条件）供给；
**唯一假设 = `CoindSubgroupAcyclic (inertiaLoc F)`**（即 `Coind_1^{G_F} A` 在惯性群上零调）。 -/
theorem inertia_Q_subsingleton_Hq
    (q' : ℕ) [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q']
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime q')
    (hB : CoindSubgroupAcyclic (G := AbsoluteGaloisGroup F) (A := ZMod ℓ) (inertiaLoc F))
    {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (continuousCohomology j (ofDiscreteModule ℤ ↥(inertiaLoc F)
      (Q (G := AbsoluteGaloisGroup F) (A := ZMod ℓ)))) := by
  haveI : IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F
  exact subsingleton_cohomology_quot_subgroup (G := AbsoluteGaloisGroup F) (A := ZMod ℓ)
    (inertiaLoc F) hB
    (fun k hk => inertiaLoc_subsingleton_Hq q' ℓ hℓ (ZMod ℓ)
      (isPPrimaryTorsion_of_module_zmod ℓ (ZMod ℓ)) hk) hj

end GaloisCarrier

end L20261018

#print axioms L20261018.inertia_Q_subsingleton_Hq
