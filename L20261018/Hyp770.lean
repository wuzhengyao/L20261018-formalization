import L20261018.Hyp769
import TauCeti.RepresentationTheory.Homological.ContCohomology.ConjInvariants

/-!
# S73 R2：★★★ **驯特征在 `p` 层是 `Γ`-不变的**——`H-conj1` 的**不动向量**来源

## 位置

```
inertiaTameCharacter_conj（TauCeti Tame/Character.lean:552）    χ_tame(gσg⁻¹) = g • χ_tame(σ)
  ＋ Hyp769.inertiaEquivInertiaLoc_conj（载体桥与共轭相容）        ← 上一轮
  ＋ 本件：Γ 在 μ_p 上平凡（AlgebraicClosure 侧孪生）             g ζ = ζ  （ζ^p = 1）
  ⟹ tameCharLoc : ↥(inertiaLoc F) →ₜ* ℤ/p  **非平凡** 且 **Γ-共轭不变**
  ⟹ 下一步（`Hyp771`）：`H1ConjInvariants = ⊤` ⟹ `Conj1Trivial`（＝ `H-conj1` 兑现）
```

## 交付

| 声明 | 内容 |
|---|---|
| **`absoluteGaloisGroup_fixes_pow_eq_one`** | ★★★★ **`Γ` 在 `μ_p` 上平凡**（`AlgebraicClosure` 侧；`Hyp766` 的孪生） |
| `exists_primitiveRoot_alg`／`zmodEquivMuP` | `μ_p ≅ ℤ/p`（取 `μ_p ⊆ F` 给的原始根） |
| **`tamePChar`** | ★★★★★ **`p` 层驯特征**：`↥(inertiaSubgroup F) →ₜ* Multiplicative (ZMod p)` |
| **`tamePChar_ne_one`** | ★★★★ 非平凡（`proj_p ∘ χ_tame` 满：`TameModel` 层满 ＋ `χ_tame` 满） |
| **`tamePChar_conj`** | ★★★★★ **共轭不变**：`χ_tame(conjNormal g σ) = χ_tame σ`（twist 被 `μ_p ⊆ F` 抹平） |
| **`tameCharLoc`**／`_ne_one`／**`_conj`** | ★★★★★ 搬到**战役载体** `↥(inertiaLoc F)`（沿 `Hyp769.inertiaEquivInertiaLoc_symm_conj`） |

## 数学（三行）

`inertiaTameCharacter_conj` 给出**带 twist `(1)`** 的等变律 `χ_tame(gσg⁻¹) = g • χ_tame(σ)`。
取 `p` 层的投影得 `proj_p(χ_tame(gσg⁻¹)) = g • proj_p(χ_tame σ)`（`PrimeToPTateModule.coe_proj_smul`）；
而 `proj_p(χ_tame σ) ∈ μ_p`，且 `HasEnoughRootsOfUnity F p`（`μ_p ⊆ F`）⟹ `g • ζ = ζ`
（`absoluteGaloisGroup_fixes_pow_eq_one`）⟹ **twist 抹平** ⟹ `χ_tame` 在 `p` 层是 `Γ`-不变的。

## 诚实边界

* 载体仍是 `IsNonarchimedeanLocalField F`（完备）；`C2`（Hensel → 完备）仍待做。
* 本件只做「**一个**非平凡不动向量」。由 `Hyp761.conj1_eq_of_ne_zero`（`Nat.card = p` 素 ⟹
  一个非零不动点即够）即可升到全部——那是下一步 `Hyp771`。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-! ## ① `Γ` 在 `μ_p` 上平凡（`AlgebraicClosure` 侧） -/

/-- 存在原始的 `p` 次单位根（在 `AlgebraicClosure F` 的单位群里）——由 `μ_p ⊆ F` 搬运。 -/
theorem exists_primitiveRoot_alg : ∃ ζ : (AlgebraicClosure F)ˣ, IsPrimitiveRoot ζ p := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot F p
  have hζ' : IsPrimitiveRoot (algebraMap F (AlgebraicClosure F) ζ) p :=
    hζ.map_of_injective (algebraMap F (AlgebraicClosure F)).injective
  exact ⟨(hζ'.isUnit (Fact.out : Nat.Prime p).ne_zero).unit,
    IsPrimitiveRoot.isUnit_unit (Fact.out : Nat.Prime p).ne_zero hζ'⟩

/-- ★★★★★ **`Γ` 在 `AlgebraicClosure` 上逐点固定 `μ_p`**（`μ_p ⊆ F` 的直接后果）。

这是 `inertiaTameCharacter_conj` 的 twist `g • ζ` 的**抹平输入**——`Hyp766` 的
`AlgebraicClosure` 侧孪生（`Hyp766` 那条在战役载体 `SeparableClosure F` 上）。 -/
theorem absoluteGaloisGroup_fixes_pow_eq_one (g : Gal(AlgebraicClosure F / F))
    {ζ : AlgebraicClosure F} (hζ : ζ ^ p = 1) : g ζ = ζ := by
  obtain ⟨m, hm⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot F p
  have hmap : IsPrimitiveRoot (algebraMap F (AlgebraicClosure F) m) p :=
    hm.map_of_injective (algebraMap F (AlgebraicClosure F)).injective
  obtain ⟨k, -, hk⟩ := hmap.eq_pow_of_pow_eq_one hζ
  rw [← hk, map_pow, AlgEquiv.commutes]

/-! ## ② `μ_p ≅ ℤ/p` 与 `p` 层驯特征 -/

/-- `μ_p ≅ ℤ/p`（加性），沿 `μ_p ⊆ F` 给的原始根。 -/
noncomputable def zmodEquivMuP :
    ZMod p ≃+ Additive ↥(rootsOfUnity p (AlgebraicClosure F)) :=
  (exists_primitiveRoot_alg (F := F) p).choose_spec.zmodEquivRootsOfUnity

/-- `p` 层驯特征的乘法同态形态（连续性在 `tamePChar` 里补）。 -/
noncomputable def tamePCharHom (hpq : p ≠ q) :
    ↥(TauCeti.inertiaSubgroup F) →* Multiplicative (ZMod p) where
  toFun σ := Multiplicative.ofAdd ((zmodEquivMuP (F := F) p).symm
    (Additive.ofMul (PrimeToPTateModule.proj (p := residueChar F)
      (E := AlgebraicClosure F) (OneDim.levelP (F := F) (p := p) (q := q) hpq)
      (TauCeti.inertiaTameCharacter F σ))))
  map_one' := by simp
  map_mul' := by
    intro a b
    simp [map_mul]

/-- ★★★★★ **`p` 层驯特征**：`↥(inertiaSubgroup F) →ₜ* Multiplicative (ZMod p)`。

连续性是「局部常值 ⟹ 连续」：`proj` 局部常值（`PrimeToPTateModule.isLocallyConstant_proj`）、
`χ_tame` 连续，故整条链局部常值。 -/
noncomputable def tamePChar (hpq : p ≠ q) :
    ↥(TauCeti.inertiaSubgroup F) →ₜ* Multiplicative (ZMod p) where
  toMonoidHom := tamePCharHom (F := F) p q hpq
  continuous_toFun :=
    (((PrimeToPTateModule.isLocallyConstant_proj (p := residueChar F)
        (E := AlgebraicClosure F) (OneDim.levelP (F := F) (p := p) (q := q) hpq)).comp_continuous
      (TauCeti.inertiaTameCharacter F).continuous).comp
      (fun y => Multiplicative.ofAdd ((zmodEquivMuP (F := F) p).symm (Additive.ofMul y)))).continuous

/-- ★★★★ **`tamePChar` 非平凡**：`proj_p ∘ χ_tame` 满（`TameModel` 每层满 ＋ `χ_tame` 满）。 -/
theorem tamePChar_ne_one (hpq : p ≠ q) : tamePChar (F := F) p q hpq ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ : ∃ c : ZMod p, c ≠ 0 := ⟨1, one_ne_zero⟩
  set y : ↥(rootsOfUnity p (AlgebraicClosure F)) := (zmodEquivMuP (F := F) p c).toMul with hy
  have hy1 : y ≠ 1 := by
    intro h1
    refine hc ?_
    have h2 : (zmodEquivMuP (F := F) p) c = 0 := by
      have h3 : Additive.ofMul y = (0 : Additive ↥(rootsOfUnity p (AlgebraicClosure F))) := by
        rw [h1]; rfl
      simpa [hy] using h3
    have h4 : (zmodEquivMuP (F := F) p) c = (zmodEquivMuP (F := F) p) 0 := by simpa using h2
    exact (zmodEquivMuP (F := F) p).injective h4
  obtain ⟨u, hu⟩ := proj_surjective_primeToPTateModule (K := F)
    (OneDim.levelP (F := F) (p := p) (q := q) hpq) y
  obtain ⟨σ, hσ⟩ := TauCeti.inertiaTameCharacter_surjective F u
  have hval : tamePChar (F := F) p q hpq σ = Multiplicative.ofAdd c := by
    show Multiplicative.ofAdd ((zmodEquivMuP (F := F) p).symm
      (Additive.ofMul (PrimeToPTateModule.proj (p := residueChar F)
        (E := AlgebraicClosure F) (OneDim.levelP (F := F) (p := p) (q := q) hpq)
        (TauCeti.inertiaTameCharacter F σ)))) = Multiplicative.ofAdd c
    rw [hσ, hu]
    show Multiplicative.ofAdd ((zmodEquivMuP (F := F) p).symm (Additive.ofMul y))
      = Multiplicative.ofAdd c
    rw [hy]
    simp
  have h1 : tamePChar (F := F) p q hpq σ = 1 := by rw [h]; rfl
  rw [hval] at h1
  exact hc (Multiplicative.ofAdd.injective (by simpa using h1))

/-- ★★★★★ **`tamePChar` 共轭不变**：`Γ` 在 `μ_p` 上平凡 ⟹ `p` 层驯特征被共轭固定。

`inertiaTameCharacter_conj` 的 twist `(1)` 在 `p` 层由 `absoluteGaloisGroup_fixes_pow_eq_one`
抹平：`proj_p(g • χ) = g • proj_p(χ) = proj_p(χ)`。 -/
theorem tamePChar_conj (hpq : p ≠ q) (g : Field.absoluteGaloisGroup F)
    (σ : ↥(TauCeti.inertiaSubgroup F)) :
    tamePChar (F := F) p q hpq (MulAut.conjNormal g σ) = tamePChar (F := F) p q hpq σ := by
  have hconj : MulAut.conjNormal g σ =
      ⟨g * (σ : Field.absoluteGaloisGroup F) * g⁻¹,
        (TauCeti.inertiaSubgroup_normal F).conj_mem σ σ.2 g⟩ :=
    Subtype.ext (MulAut.conjNormal_apply g σ)
  have hchar : TauCeti.inertiaTameCharacter F (MulAut.conjNormal g σ) =
      (show Gal(AlgebraicClosure F / F) from g) • TauCeti.inertiaTameCharacter F σ := by
    rw [hconj]
    exact TauCeti.inertiaTameCharacter_conj (show Gal(AlgebraicClosure F / F) from g) σ.2
  have hproj : PrimeToPTateModule.proj (p := residueChar F) (E := AlgebraicClosure F)
        (OneDim.levelP (F := F) (p := p) (q := q) hpq)
        ((show Gal(AlgebraicClosure F / F) from g) • TauCeti.inertiaTameCharacter F σ) =
      PrimeToPTateModule.proj (p := residueChar F) (E := AlgebraicClosure F)
        (OneDim.levelP (F := F) (p := p) (q := q) hpq) (TauCeti.inertiaTameCharacter F σ) := by
    apply Subtype.ext
    apply Units.ext
    rw [PrimeToPTateModule.coe_proj_smul]
    have hx : ((PrimeToPTateModule.proj (p := residueChar F) (E := AlgebraicClosure F)
        (OneDim.levelP (F := F) (p := p) (q := q) hpq)
        (TauCeti.inertiaTameCharacter F σ) : (AlgebraicClosure F)ˣ)) ^ p = 1 :=
      (PrimeToPTateModule.proj (p := residueChar F) (E := AlgebraicClosure F)
        (OneDim.levelP (F := F) (p := p) (q := q) hpq)
        (TauCeti.inertiaTameCharacter F σ)).2
    exact absoluteGaloisGroup_fixes_pow_eq_one (F := F) p (show Gal(AlgebraicClosure F / F) from g)
      (by simpa using congrArg (fun v : (AlgebraicClosure F)ˣ => (v : AlgebraicClosure F)) hx)
  show Multiplicative.ofAdd ((zmodEquivMuP (F := F) p).symm
      (Additive.ofMul (PrimeToPTateModule.proj (p := residueChar F) (E := AlgebraicClosure F)
        (OneDim.levelP (F := F) (p := p) (q := q) hpq)
        (TauCeti.inertiaTameCharacter F (MulAut.conjNormal g σ))))) =
    Multiplicative.ofAdd ((zmodEquivMuP (F := F) p).symm
      (Additive.ofMul (PrimeToPTateModule.proj (p := residueChar F) (E := AlgebraicClosure F)
        (OneDim.levelP (F := F) (p := p) (q := q) hpq)
        (TauCeti.inertiaTameCharacter F σ))))
  rw [hchar, hproj]

/-! ## ③ 搬到战役载体 `↥(inertiaLoc F)` -/

/-- ★★★★★ **战役载体上的 `p` 层驯特征**：`χ(x) := χ_tame(e.symm x)`（`e = inertiaEquivInertiaLoc`）。 -/
noncomputable def tameCharLoc (hpq : p ≠ q) :
    ↥(inertiaLoc F) →ₜ* Multiplicative (ZMod p) :=
  (tamePChar (F := F) p q hpq).comp
    ⟨(inertiaEquivInertiaLoc (F := F)).symm.toMulEquiv.toMonoidHom,
      (inertiaEquivInertiaLoc (F := F)).symm.continuous_toFun⟩

/-- `tameCharLoc` 逐点就是 `tamePChar` 沿载体桥的拉回（`rfl`）。 -/
theorem tameCharLoc_apply (hpq : p ≠ q) (x : ↥(inertiaLoc F)) :
    tameCharLoc (F := F) p q hpq x =
      tamePChar (F := F) p q hpq ((inertiaEquivInertiaLoc (F := F)).symm x) := rfl

/-- ★★★★ `tameCharLoc` 非平凡（沿桥的双射性搬运）。 -/
theorem tameCharLoc_ne_one (hpq : p ≠ q) : tameCharLoc (F := F) p q hpq ≠ 1 := by
  intro h
  apply tamePChar_ne_one (F := F) p q hpq
  ext y
  have h1 : tameCharLoc (F := F) p q hpq ((inertiaEquivInertiaLoc (F := F)) y) = 1 := by
    rw [h]; rfl
  rwa [tameCharLoc_apply, ContinuousMulEquiv.symm_apply_apply] at h1

/-- ★★★★★ **战役载体上的共轭不变性**：`χ(conjNormal g x) = χ x`（`x ∈ ↥(inertiaLoc F)`）。

**这就是 `H-conj1` 所需的「非平凡不动向量」**——`Hyp762.conj1Trivial_of_ne_zero` 只需一个
非零不动元素，本件给出这个元素的**特征形态**。 -/
theorem tameCharLoc_conj (hpq : p ≠ q) (g : TauCeti.AbsoluteGaloisGroup F)
    (x : ↥(inertiaLoc F)) :
    tameCharLoc (F := F) p q hpq (MulAut.conjNormal g x) = tameCharLoc (F := F) p q hpq x := by
  rw [tameCharLoc_apply, tameCharLoc_apply, inertiaEquivInertiaLoc_symm_conj]
  exact tamePChar_conj (F := F) p q hpq
    ((TauCeti.absoluteGaloisGroupRestrictEquiv F).symm g)
    ((inertiaEquivInertiaLoc (F := F)).symm x)

end L20261018

#print axioms L20261018.exists_primitiveRoot_alg
#print axioms L20261018.absoluteGaloisGroup_fixes_pow_eq_one
#print axioms L20261018.zmodEquivMuP
#print axioms L20261018.tamePChar
#print axioms L20261018.tamePChar_ne_one
#print axioms L20261018.tamePChar_conj
#print axioms L20261018.tameCharLoc
#print axioms L20261018.tameCharLoc_ne_one
#print axioms L20261018.tameCharLoc_conj
