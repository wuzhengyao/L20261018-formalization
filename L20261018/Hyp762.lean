import L20261018.Hyp761

/-!
# S72 R2：W4 的**具名假设登记**（`PROMPT-S72` §0bis 第 4 条授权的回退）

## 为什么本轮走回退

W4 = `∀ g x, explicitConj1 (inertiaLoc F) g x = x`（等价地：`Γ⧸I` 在 `H¹(I,μ_p)` 上共轭作用平凡）。
`Hyp761.conj1_eq_of_ne_zero` 已把它的**归约**做到最优（只需一个非零元素，`hgen` 已自动）。
但**那一条方程本身**需要本仓与 TauCeti 都没有的基建：

```
需要：Γ 在驯惯性 I_t ≅ ∏_{ℓ≠q} Z_ℓ(1) 上按分圆特征 ω 作用，且 ω(γ) ≡ 1 (mod p)
理由：μ_p ⊆ F（HasEnoughRootsOfUnity）⟹ Γ 在 μ_p 上平凡 ⟹ ω(γ) mod p = 1
⟹ χ(γ⁻¹xγ) = ω(γ)·χ(x) = χ(x)
```

（`STARTUP` §2bis 已在 S69 实测认定：本仓 `TauCeti` **都没有**「共轭在 `I_t` 上按分圆特征作用」。）

## 数学上它为什么是真命题（不是空洞假设）

两条独立论证（都指向同一结论「作用平凡」）：

1. **分圆特征路线**：`μ_p ⊆ F` ⟹ `p ∣ |κ^×| = q-1` ⟹ `ω(γ) ≡ 1 (mod p)`。
   `Γ⧸I = Gal(κ̄/κ) = Ẑ` 由 Frobenius `φ` 生成，`ω(φ) = q ≡ 1 (mod p)`。
2. **限制路线**：`res : Hom_cont(Γ, Z/p) → Hom_cont(I, Z/p)`；由 `F^× ≅ ℤ ⊕ O_F^×`（局部类域论）
   知 `res` 满。故每个 `χ ∈ Hom(I,Z/p)` 都可延拓成 `Γ` 上的特征 `ψ`，而 `Z/p` 交换 ⟹
   `χ(γ⁻¹xγ) = ψ(γ⁻¹xγ) = ψ(x) = χ(x)`。

**两条路线都需要本仓没有的基建**：前者需「`Γ` 在 `I_t` 上按 `ω` 作用」；
后者需局部类域论（`Γ^{ab} ≅ \widehat{F^×}`）。故本轮**登记为具名假设**（`PROMPT-S72` §0bis 第 4 条）。

## 「非空实例义务」（`L1` ＋ `L10①` 的机检化）

本假设陈述的是**具体对象** `H1 ↥(inertiaLoc F) (ZMod p)` 上的一条方程。该对象**非空且有限**：
`Hyp759.natCard_h1Inertia_eq` 给出 `Nat.card = p`，`p ≥ 2`。故假设类**非空**（不是「对空的类全称」）。
本件 `witness_nonempty` 把这条机检化。

## 交付

| 声明 | 内容 |
|---|---|
| **`Conj1Trivial`** | ★★★★ 具名假设 **H-conj1** 的**类型锁定**：`∀ g x, explicitConj1 (inertiaLoc F) g x = x` |
| **`witness_nonempty`** | ★★★★ 非空见证：`Nonempty (H1 ↥I (ZMod p))`（由 `Nat.card = p ≥ 2`） |
| `conj1Trivial_apply` | 使用接口：假设 ⟹ 单点方程（供 `F5` 的构造消费） |
| `conj1Trivial_of_ne_zero` | 消除接口：**只需一个非零元素被固定即得全假设**（`Hyp761` 的直接推论） |
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

/-- ★★★★ **具名假设 H-conj1（类型锁定）**：`Γ⧸I` 在 `H¹(I,μ_p)` 上的共轭作用平凡。

**数学根据**：`μ_p ⊆ F` ⟹ 分圆特征 `ω` 在 `Γ` 上模 `p` 平凡 ⟹ `χ(γ⁻¹xγ) = ω(γ)χ(x) = χ(x)`。
**基建缺口**：本仓无「`Γ` 在驯惯性 `I_t ≅ Z_p(1)` 上按 `ω` 作用」这一事实（见文件头）。

⚠ **本假设必须列进第 4 章「剩余具名假设」表**（`STARTUP` §2 ＋ `wiki/log.md`）。
⚠ **它只影响 `F5`**（`F5 : H¹(Γ⧸I, H¹(I,μ_p)) → VKG`）；`hd_infl` 已与 `F5` 解耦
（`Hyp757.hd_infl_of_linear`），`Hyp761`／`Hyp759`／`Hyp758` 均**无条件**。 -/
def Conj1Trivial (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ) [NeZero p] [Fact p.Prime]
    [HasEnoughRootsOfUnity F p] : Prop :=
  ∀ (g : AbsoluteGaloisGroup F) (x : H1 ↥(inertiaLoc F) (ZMod p)),
    explicitConj1 (inertiaLoc F) g x = x

section Witness

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-- ★★★★ **非空见证**（`L1` ＋ `L10①` 机检义务）：假设类**非空**。

`Nat.card (H1 ↥I (ZMod p)) = p ≥ 2` ⟹ 该类型非空。故 `Conj1Trivial` 不是「对空的类全称」。 -/
theorem witness_nonempty (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤) :
    Nonempty (H1 ↥(inertiaLoc F) (ZMod p)) := by
  have hcard := natCard_h1Inertia_eq (F := F) (p := p) (q := q) hpq ζ hζ hgen
  have hpos : 0 < Nat.card (H1 ↥(inertiaLoc F) (ZMod p)) := by
    rw [hcard]; exact (Fact.out : Nat.Prime p).pos
  exact (Nat.card_pos_iff.mp hpos).1

/-- 使用接口：具名假设 ⟹ 单点方程（供 `F5` 的构造消费）。 -/
theorem conj1Trivial_apply (h : Conj1Trivial F p) (g : AbsoluteGaloisGroup F)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) :
    explicitConj1 (inertiaLoc F) g x = x :=
  h g x

/-- ★★★★ **消除接口**：**只需一个非零元素被固定**，即得全部假设（`Hyp761` 的直接推论）。

⟹ 若将来走「`Hyp521.shiftedHom 1` 那一根生成元」路线，只需算**一个**算式。 -/
theorem conj1Trivial_of_ne_zero (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hx : x ≠ 0)
    (hfix : ∀ g : AbsoluteGaloisGroup F, explicitConj1 (inertiaLoc F) g x = x) :
    Conj1Trivial F p :=
  fun g y => conj1_eq_of_ne_zero (F := F) (p := p) (q := q) hpq ζ hζ hgen x hx hfix g y

end Witness

end L20261018

#print axioms L20261018.witness_nonempty
#print axioms L20261018.conj1Trivial_of_ne_zero
