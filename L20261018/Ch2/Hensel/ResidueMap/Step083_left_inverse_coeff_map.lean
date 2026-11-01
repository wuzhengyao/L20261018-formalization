import L20261018.Ch2.Hensel.ResidueMap.Step082_explicit_cup_nonzero

/-!
# S77 R6：第 5 步 (b) 的**最后一块** —— 为 `explicitCup01` 造左逆系数映射

## 要什么

`Hyp797.explicitCup01_ne_zero_of_leftInverse` 需要一条

```
e : H1 ↥I (ZMod p) →+[Γ⧸I] ↥(FixedPoints.addSubgroup ↥I (ZMod p))
e (smulPairingH1 m x) = x        ∀ x
```

其中 `m := contM z.1 ≠ 0`（`Hyp795`）。**本件只造 `e`，不含数学**。

## 配方（全部既有件）

`ψ := h1InertiaAddEquiv hpq ζ hζ hgen m hm` 是 `h1InertiaLinearEquiv`
（`Hyp765`，正向即 `c ↦ c • x`，**`rfl` 级**）的逆，故

```
ψ m = 1                                    -- Hyp775.h1InertiaAddEquiv_self
ψ ((x:ℤ/p) • m) = x                        -- LinearEquiv.symm_apply_apply
```

`e y := ⟨ψ y, 不变性⟩`（`ℤ/p` 上 `↥I`-作用平凡，`rfl`），等变性由
`Hyp767.quotient_smul_eq_self`（`H-conj1` 已由 `Hyp771.conj1Trivial_of_tameChar` 无条件化）给出。

## 交付

| 声明 | 内容 |
|---|---|
| **`exists_leftInverse_coeff`** | ★★★★★ `m ≠ 0` ⟹ 存在连续等变 `e` 且 `e (x • m) = x` |
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
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-- 技术实例：`I = inertiaLoc F` 闭。 -/
local instance instClosedInertiaLocS77R6 :
    IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 正规。 -/
local instance instNormalInertiaLocS77R6 : (inertiaLoc F).Normal := normal_inertiaLoc F

/-- ★★★★★ **左逆系数映射存在**：`m ≠ 0` ⟹ 存在连续等变
`e : H¹(I,ℤ/p) →+[Γ⧸I] μ_pᴵ` 且 `e (x • m) = x`。 -/
theorem exists_leftInverse_coeff (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m' : {m' : ℕ // m' ≠ 0 ∧ m'.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m' ζ : ↥(rootsOfUnity (↑m') (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m'))
    (hgen : closedZpowers ζ = ⊤)
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    {m : H1 ↥(inertiaLoc F) (ZMod p)} (hm : m ≠ 0) :
    ∃ e : H1 ↥(inertiaLoc F) (ZMod p) →+[AbsoluteGaloisGroup F ⧸ inertiaLoc F]
        ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)),
      Continuous e ∧ ∀ x : ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)),
        e ((smulPairingH1 (F := F) p) m x) = x := by
  classical
  have htriv : ∀ (g : AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (y : H1 ↥(inertiaLoc F) (ZMod p)), g • y = y :=
    fun g y => quotient_smul_eq_self (F := F) (p := p)
      (conj1Trivial_of_tameChar (F := F) (p := p) (q := q) hpq) g y
  have htrivZ : ∀ (g : AbsoluteGaloisGroup F ⧸ inertiaLoc F) (c : ZMod p), g • c = c :=
    fun _ _ => rfl
  have htrivI : ∀ (i : ↥(inertiaLoc F)) (c : ZMod p), i • c = c := fun _ _ => rfl
  let f := h1InertiaLinearEquiv (F := F) (p := p) (q := q) hpq ζ hζ hgen m hm
  let e : H1 ↥(inertiaLoc F) (ZMod p) →+[AbsoluteGaloisGroup F ⧸ inertiaLoc F]
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)) :=
    { toFun := fun y => ⟨f.symm y, by
        rw [FixedPoints.mem_addSubgroup]
        exact fun i => htrivI i (f.symm y)⟩
      map_zero' := by
        apply Subtype.ext
        exact map_zero f.symm
      map_add' := by
        intro a b
        apply Subtype.ext
        exact map_add f.symm a b
      map_smul' := by
        intro g y
        rw [htriv g y]
        exact (quotient_smul_muPInv_trivial (F := F) (p := p) g _).symm }
  refine ⟨e, ?_, ?_⟩
  · exact continuous_of_discreteTopology
  · intro x
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply f (x : ZMod p)

end L20261018
