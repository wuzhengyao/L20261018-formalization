import L20261018.Hyp774

/-!
# S74 R1：`∂¹` 的两个输入（`x₀ := res₁((π))` 非零 ＋ 共轭不变）—— ③ 的"归一化"被消掉

## 本轮的决策级发现（先写结论）

S73 的 `GAP3-PLAN.md` 把缺口 ③ 拆成三块基建：
**(甲)** `Hom_cont(Ẑ,ℤ/p) ≅ ℤ/p`（路线 B 归约）、**(乙)** `F5` 对 `x` 的齐次性（把 ③ `∂¹(π)=−1` 降为可选参数）、
**(②)** GS 6.8.4（投影公式）。

**本轮实测：`x` 不必"任取后再齐次化"，直接取 `x := −res₁((π))` 就把 ③ 钉死。** 理由（全部机检或一步之遥）：

```
x₀ := res₁ (kummerClass π)        ∈ H¹(I, ℤ/p)
  ✓ x₀ ≠ 0                       ⟸ Hyp747.res1V_kummerClass_eq_zero_iff ＋ v(π) = 1（本件 ②）
  ✓ x₀ 共轭不变（即 ∈ H⁰(Γ⧸I, H¹(I,ℤ/p))）  ⟸ 1-余圈在平凡系数下是同态（本件 ①）
  ✓ e_{x₀}(x₀) = 1               ⟸ h1InertiaLinearEquiv 的定义是 c ↦ c • x（本件 ③）
```

于是 GS `prop-specialization-section` 的 `∂¹((−π)) = 1` **不是一条要证的方程，而是一次选参**：
取 `x := −x₀` 就有 `e_x(x₀) = −1`，投影公式 `∂²(π ∪ Inf a) = ∂¹(π) ∪ a` 经 `e_x` 后给出
`d_x(cup (Inf a) π) = a`（而不是 `c • a`）。

⟹ **(甲) 与 (乙) 从待证清单中永久移除**（`GAP3-PLAN.md` §8 的建议顺序作废，见本件 §5）。

## 交付

| 声明 | 内容 |
|---|---|
| **`explicitRes1_mem_H1ConjInvariants`** | ★★★★ 一般形：`res₁` 的像落在共轭不变子群（平凡系数） |
| **`res1V_mem_H1ConjInvariants`** | ★★★★ 战役形：`res₁(y) ∈ H⁰(Γ⧸I, H¹(I,ℤ/p))`（＝ GS 的 `∂¹` 落点） |
| **`res1V_kummerClass_ne_zero_of_uniformizer`** | ★★★★★ `res₁((π)) ≠ 0`（一致化元）—— ③ 的归一化常数非零 |
| `h1InertiaAddEquiv_self` | `e_x(x) = 1`（`x ≠ 0`） |
| `h1InertiaAddEquiv_neg_self` | `e_{−x}(x) = −1` |
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

/-! ## ① `res₁` 的像落在共轭不变子群（一般形，平凡系数） -/

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- ★★★★ **`res₁` 的像共轭不变**（平凡系数）：限制把全局类送到共轭不变子群。

**证明**（GS `prop-inflation-restriction` 的 `i = 1` 情形）：`res₁` 在 1-余圈层是**拉回**
（`explicitRes1_mk` ＋ `cocyclesMap1_apply`）。平凡系数下 1-余圈是**同态**
（`map_mul_of_smul_eq_self_of_mem_Z1`），故 `c (g n g⁻¹) = c g + c n + c g⁻¹ = c n`
（`map_inv_of_mem_Z1` 给 `c g⁻¹ = −c g`）。 -/
theorem explicitRes1_mem_H1ConjInvariants (htriv : ∀ (g : G) (m : M), g • m = m)
    (N : Subgroup G) [N.Normal] (z : H1 G M) :
    explicitRes1 G M N z ∈ H1ConjInvariants G M N := by
  induction z using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitRes1_mk, mk_mem_H1ConjInvariants_iff_of_smul_eq_self htriv]
    intro g n
    rw [cocyclesMap1_apply, cocyclesMap1_apply]
    simp only [AddMonoidHom.id_apply]
    show (c : G → M) ↑((MulAut.conjNormal g) n) = (c : G → M) ↑n
    rw [MulAut.conjNormal_apply]
    have hinv : (c : G → M) g⁻¹ = -(c : G → M) g := by
      have h := map_inv_of_mem_Z1 c.2 g
      rwa [htriv g] at h
    rw [map_mul_of_smul_eq_self_of_mem_Z1 htriv c.2 (g * ↑n) g⁻¹,
      map_mul_of_smul_eq_self_of_mem_Z1 htriv c.2 g ↑n, hinv]
    abel

end General

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★ **战役形**：`res₁(y) ∈ H⁰(Γ⧸I, H¹(I,ℤ/p))`。

`res1V` 沿 `h1ToVEquiv` 把 `GaloBase.V` 搬到显式 `H1 Γ (ℤ/p)`，故一般形直接适用。
这是 GS `∂¹ : H¹(G,A) → H⁰(G/H, H¹(H,A))` 的落点（`i = 1` 时 `∂¹` 就是限制）。 -/
theorem res1V_mem_H1ConjInvariants (y : GaloBase.V F p) :
    res1V (F := F) (p := p) y
      ∈ H1ConjInvariants (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) := by
  have htriv : ∀ (g : AbsoluteGaloisGroup F) (m : ZMod p), g • m = m := fun _ _ => rfl
  rw [res1V_apply]
  exact explicitRes1_mem_H1ConjInvariants htriv (inertiaLoc F) _

/-! ## ② `x₀ := res₁((π)) ≠ 0`（一致化元） -/

/-- ★★★★★ **一致化元的 Kummer 类在惯性上非零**：`p ∤ v(π) = 1`。

这就是 GS `prop-specialization-section` 证明里的 `∂¹((−π)) = 1` 所依赖的**唯一非平凡输入**
（"`∂¹` 经 Kummer 同构变成 mod `p` 赋值映射，而 `−π` 的赋值是 `1`"）。
本战役的版本更省：`Hyp747.res1V_kummerClass_eq_zero_iff` 已把零点集算成 `p ∣ v(a)`。 -/
theorem res1V_kummerClass_ne_zero_of_uniformizer (hp : IsUnit (p : F))
    (hpq : ¬ ringChar 𝓀[F] ∣ p) {π : Fˣ}
    (hπ : normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ)) :
    res1V (F := F) (p := p) (KummerBridge.kummerClass F p hp π) ≠ 0 := by
  intro h0
  have hdvd : (p : ℤ) ∣ (normalizedValuation F π).toAdd :=
    (res1V_kummerClass_eq_zero_iff (p := p) hp hpq π).mp h0
  rw [hπ] at hdvd
  change (p : ℤ) ∣ 1 at hdvd
  have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).two_le
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h5 : (p : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hdvd
  omega

/-! ## ③ 系数同构在一根生成元上的取值 -/

variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-- ★★★ **`e_x(x) = 1`**：`h1InertiaLinearEquiv` 是 `c ↦ c • x`，取逆后 `x ↦ 1`。 -/
theorem h1InertiaAddEquiv_self (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hx : x ≠ 0) :
    h1InertiaAddEquiv (F := F) (p := p) (q := q) hpq ζ hζ hgen x hx x = 1 := by
  show (h1InertiaLinearEquiv (F := F) (p := p) (q := q) hpq ζ hζ hgen x hx).symm x = 1
  rw [LinearEquiv.symm_apply_eq]
  show x = (1 : ZMod p) • x
  rw [one_smul]

/-- ★★★ **`e_{−x}(x) = −1`**：`x` 换成 `−x` 时系数同构变号（在 `x` 上取值）。 -/
theorem h1InertiaAddEquiv_neg_self (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hx : x ≠ 0) (hx' : -x ≠ 0) :
    h1InertiaAddEquiv (F := F) (p := p) (q := q) hpq ζ hζ hgen (-x) hx' x = -1 := by
  have h1 : h1InertiaAddEquiv (F := F) (p := p) (q := q) hpq ζ hζ hgen (-x) hx' (-x) = 1 :=
    h1InertiaAddEquiv_self (F := F) (p := p) (q := q) hpq ζ hζ hgen (-x) hx'
  have h2 := map_neg (h1InertiaAddEquiv (F := F) (p := p) (q := q) hpq ζ hζ hgen (-x) hx') x
  rw [h1] at h2
  have h3 := congrArg Neg.neg h2
  simpa using h3.symm

end Local

end L20261018

#print axioms L20261018.explicitRes1_mem_H1ConjInvariants
#print axioms L20261018.res1V_mem_H1ConjInvariants
#print axioms L20261018.res1V_kummerClass_ne_zero_of_uniformizer
#print axioms L20261018.h1InertiaAddEquiv_self
#print axioms L20261018.h1InertiaAddEquiv_neg_self
