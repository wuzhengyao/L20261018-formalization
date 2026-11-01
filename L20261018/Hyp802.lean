import Hyp800
import Hyp449

/-!
# S78 R3：第 4 章**唯一具名假设** `Ch4TameSymbolHyp` 的**第三个非空见证**（且无 `p ≠ 2`）

## 靶子

`Hyp449.Ch4TameSymbolHyp` 是本战役为第 4 章登记的**唯一具名假设**（它的 `def` 外形与
`Hyp800.exists_residueMap` 的结论**逐字相同**）：

```
Ch4TameSymbolHyp := ∃ d : H² →ₗ VKG, (∀ y z, d (cup y z) = 0) ∧ (∀ y, d (cup y π) = y)
```

`Hyp800.exists_residueMap` 在 **`IsNonarchimedeanLocalField` ＋ `hpu` ＋ 惯性生成元数据** 下
**无条件**给出它（`v := normalizedValuation F`）。本件把它写成 `Ch4TameSymbolHyp` 的形状，
并与既有两条非空见证对照。

## 三条非空见证的假设画像（缺一不可的对照）

| 见证 | 需要 | **不需要** |
|---|---|---|
| `Hyp449.ch4TameSymbolHyp_of_dependent` | `hζ : IsPrimitiveRoot ζ p`、`hv`、`hπ`、`hp2 : p ≠ 2` | 完备性 |
| **本件 `ch4TameSymbolHyp_viaResidue`** | `[IsNonarchimedeanLocalField F]`、`hpu`、`ζ : TameModel`＋`hζ`＋`hgen`、`hδ` | **`p ≠ 2`**｜**`[FiniteDimensional]`**｜`hp2 : NeZero (2 : ZMod p)`｜`hv`（自动） |
| `Hyp692.ch4TameSymbolHyp_of_merkurjevSuslin` | `MerkurjevSuslin`（外部大定理） | 完备性／`p ≠ 2` 无关 |

**⟹ 本件的价值**：第 4 章的唯一具名假设在**完备（locally compact）档**多一条
**不经 `p ≠ 2`、不经维数假设、且走论文自己的 §2→§4 依赖方向**（`prop:prelim-residue`(1)）的见证。
**残余不变**：`dim ker v̄ = ∞`（如 `κ = ℂ(t)`）的一般 Hensel 情形仍须 `prop:prelim-residue`(2)
（＝ GS 7.1.5 的驯符号公式），本件未触及。
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
local instance instClosedInertiaLocS78R3 :
    IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 正规。 -/
local instance instNormalInertiaLocS78R3 : (inertiaLoc F).Normal := normal_inertiaLoc F

/-- 技术实例：`μ_pᴵ` 上 `Γ⧸I` 连续作用。 -/
local instance instContSmulMuPInvS78R3 :
    ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)) := inferInstance

variable {π : Fˣ}

/-- ★★★★★★★ **`Ch4TameSymbolHyp`（第 4 章唯一具名假设）在完备档成立 —— 第三条见证**。

**不需要 `p ≠ 2`**、**不需要 `[FiniteDimensional]`**、**不需要 `NeZero (2 : ZMod p)`**；
走的是**论文自己的依赖方向**：§2 `prop:prelim-residue`(1) 的 `∂₂` → §4。 -/
theorem ch4TameSymbolHyp_viaResidue (qq : ℕ) [Fact qq.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) qq]
    (hcopq : p.Coprime qq) (hp : IsUnit (p : F))
    (hpq' : ¬ ringChar 𝓀[F] ∣ p) (hpu : IsUnit (p : ↥𝒪[F]))
    (t : TameModel F)
    (ht : ∀ m' : {m' : ℕ // m' ≠ 0 ∧ m'.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m' t : ↥(rootsOfUnity (↑m') (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m'))
    (hgen : closedZpowers t = ⊤)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hp π))) :
    Ch4TameSymbolHyp (F := F) p (v := TauCeti.normalizedValuation F) (π := π) hp :=
  exists_residueMap (F := F) (p := p) (q := qq) (hcop := hcopq) hp hpq' hpu t ht hgen
    (pi0 := π) hπ z hδ

/-- ★★★★★ **同一见证的 `(R2)`（`Disjoint`）形态** —— 由 `Hyp449` 的双向等价搬运。 -/
theorem disjoint_viaResidue (qq : ℕ) [Fact qq.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) qq]
    (hcopq : p.Coprime qq)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2)
    (hp : IsUnit (p : F)) (hpq' : ¬ ringChar 𝓀[F] ∣ p) (hpu : IsUnit (p : ↥𝒪[F]))
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (t : TameModel F)
    (ht : ∀ m' : {m' : ℕ // m' ≠ 0 ∧ m'.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m' t : ↥(rootsOfUnity (↑m') (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m'))
    (hgen : closedZpowers t = ⊤)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p))))
    (hδ : ((contCoindSES (F := F) p).delta 0).hom
        ((explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom
          (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z))
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((KummerBridge.h1ToVEquiv (F := F) (p := p)).symm
            (KummerBridge.kummerClass F p hp π))) :
    Disjoint
      (residuePhi (GaloBase.cup (K := F) (p := p))
        (valLinOf (F := F) (p := p) (TauCeti.normalizedValuation F) hp)
        (KummerBridge.kummerClass F p hp π)).range
      (residueSpan (GaloBase.cup (K := F) (p := p))
        (valLinOf (F := F) (p := p) (TauCeti.normalizedValuation F) hp)) :=
  (ch4TameSymbolHyp_iff_disjoint (F := F) (p := p)
    (v := TauCeti.normalizedValuation F) (π := π) hζ hpu hp
    (valCompat_normalizedValuation F) hπ hp2).mp
    (ch4TameSymbolHyp_viaResidue (F := F) (p := p) (qq := qq) (hcopq := hcopq)
      hp hpq' hpu t ht hgen hπ z hδ)

end L20261018

#print axioms L20261018.ch4TameSymbolHyp_viaResidue
#print axioms L20261018.disjoint_viaResidue
