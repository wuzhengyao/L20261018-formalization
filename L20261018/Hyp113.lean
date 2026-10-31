import Hyp110
import TauCeti.RingTheory.Henselian.Basic

/-!
# R940：把 `∅-open` 残余 ② 推进两步

`STATUS.md`「第 4 章残余」② = **`HenselResidueData` 的可实现性**（真实局部域上的实例）。
本条（规则 17 的 (b) 类项：**可算但未算**，不得以「仍开」结案）本轮拆成两半：

## 1. 论文 T3 第三步的**环论那半**已在库内，且**已在本工作区机检**

论文 `raw/L20261018.tex:1017–1023` 断言：

> 群 $1+\mF$ 称为主单位群；映射 $u\mapsto u^p$ 是该群的自同构。
> 事实上，对 $u\in1+\mF$，多项式 $X^p-u$ 在剩余域中有单根 $1$，
> Hensel 引理给出唯一的主单位根。

L46 侦察（`RECON-CH4.md` §2 Q1）给的是 TauCeti 的**抽象 Hensel 形式**：

```
TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem :
  ∀ {R} [CommRing R] {I J : Ideal R} [HenselianRing R J],
    I ≤ J → ∀ {n : ℕ}, IsUnit ↑n → ∀ {w : R}, w - 1 ∈ I → ∃ a, a ^ n = w ∧ a - 1 ∈ I
```

本轮已用 `import TauCeti.RingTheory.Henselian.Basic`**在本工作区实测该签名**（`#check` 通过，
模块经 `port_tau.py` 就绪），并把它包成论文口径的声明 `principalUnit_pow_surjective`。

**⟹ T3 第三步的「Hensel 那半」不再属 `∅-open`**：它**是定理，不是假设**。
剩下真正缺的只有**上同调层**（`val` 的线性性／`infl`／`split`／`res`＋`tame_*`）。

## 2. `HenselResidueData` **结构本身**非空（结构层非空见证）

`Hyp109` 见证的是 `ResidueCupData`（抽象层）；`Hyp110` 的 `HenselResidueData` 是**按 `cup`
参数化**的论文层结构。本轮补 `toyHenselResidueData`：同一 `Z/3` 辛平面模型在此结构下**逐字段机检**，
于是 T3／T4 的**假设类在结构层非空**（不是空真）。

> **仍未闭合的那一格**（明确登记，不用「仍开」结案）：`HenselResidueData` 在**真实局部域**
> （`ℚ_p`／`𝔽_q((t))`）上的实例。它的四个上同调字段需要 `G_F ↠ G_K` 的膨胀与 `∂₂` 的
> 值等式，是**多轮基建**（侦察估：抽象层 ~350 行移植，或局部域层 ~1700 行）。
> 本轮的处置 = 把该项**拆成**「Hensel／主单位半（已机检）」＋「上同调层半（下一轮的单一入口）」，
> 不让整项以「未算」挂账。
-/

set_option maxHeartbeats 2000000

namespace L20261018

/-! ## 1. 论文 `:1017–1023`：主单位群的 `p` 次幂映射满 -/

/-- **论文 `:1017–1023` 的「Hensel 那半」（环论形式）**：`n` 在 `R` 中可逆、`I ≤ J`、
`w ≡ 1 (mod I)` ⟹ `w` 有 `n` 次根 `a`，且 `a ≡ 1 (mod I)`。

这是论文「映射 `u ↦ u^p` 是 `1+𝔪_F` 的自同构」里**满射**那一半的抽象形式
（单射那一半需要 `1+𝔪` 无 `p`-挠，论文未用）。出处是 TauCeti 的
`HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem`（**定理，不是假设**）。 -/
-- @source file=raw/L20261018.tex locator=line:1017 quote="群 $1+\mF$ 称为主单位群；映射 $u\mapsto u^p$ 是该群的自同构。"
theorem principalUnit_pow_surjective {R : Type*} [CommRing R] {I J : Ideal R}
    [HenselianRing R J] (hIJ : I ≤ J) {n : ℕ} (hn : IsUnit (n : R)) :
    ∀ w : R, w - 1 ∈ I → ∃ a : R, a ^ n = w ∧ a - 1 ∈ I :=
  fun w hw => TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem hIJ hn hw

/-- 论文用的情形 `n = p`（`p` 在 `R` 中可逆 ⟸ `char K ≠ p`）。 -/
theorem principalUnit_pow_surjective_prime {R : Type*} [CommRing R] {I J : Ideal R}
    [HenselianRing R J] (hIJ : I ≤ J) {p : ℕ} [Fact p.Prime]
    (hp : IsUnit (p : R)) :
    ∀ w : R, w - 1 ∈ I → ∃ a : R, a ^ p = w ∧ a - 1 ∈ I :=
  principalUnit_pow_surjective hIJ hp

/-! ## 2. `HenselResidueData` 的结构层非空见证（`Z/3` 辛平面） -/

open ResidueCupData in
/-- 论文层结构 `HenselResidueData` 在 `Z/3` 辛平面模型上**逐字段可满足**。
`cup` 取 `Hyp109.toyResidueCupData` 的辛形式；其余字段与之同源。 -/
noncomputable def toyHenselResidueData :
    HenselResidueData (ZMod 3) (ZMod 3 × ZMod 3) (ZMod 3) (ZMod 3)
      ResidueCupData.toyResidueCupData.cup where
  res := LinearMap.id
  val := LinearMap.snd (ZMod 3) (ZMod 3) (ZMod 3)
  infl := LinearMap.inl (ZMod 3) (ZMod 3) (ZMod 3)
  inj_infl := by
    intro a b h
    simpa using h
  val_infl := by
    intro y
    rfl
  pi := (0, 1)
  val_pi := rfl
  split := by
    intro x
    exact ⟨x.1, x.2, by ext <;> simp⟩
  tame_uu := by
    intro y z
    simp only [ResidueCupData.toyResidueCupData, LinearMap.mk₂_apply, LinearMap.inl_apply,
      LinearMap.id_apply]
    ring
  tame_u_pi := by
    intro y
    simp only [ResidueCupData.toyResidueCupData, LinearMap.mk₂_apply, LinearMap.inl_apply,
      LinearMap.id_apply]
    ring
  tame_pi_u := by
    intro κ hκ z
    simp only [LinearMap.snd_apply, LinearMap.id_apply] at hκ ⊢
    simp only [ResidueCupData.toyResidueCupData, LinearMap.mk₂_apply, LinearMap.inl_apply]
    rw [hκ]
    ring

/-- **结构层非空见证**：`HenselResidueData` 的假设类**非空**。 -/
theorem toyHenselResidueData_nonempty :
    Nonempty (HenselResidueData (ZMod 3) (ZMod 3 × ZMod 3) (ZMod 3) (ZMod 3)
      ResidueCupData.toyResidueCupData.cup) :=
  ⟨toyHenselResidueData⟩

/-- `HenselResidueData` 打包成 `ResidueCupData` 后**仍是**同一份数据（一致性检查）。 -/
theorem toyHensel_toResidueCupData :
    (toyHenselResidueData.toResidueCupData
        (fun x y => ResidueCupData.toyResidueCupData.skew x y)).cup
      = ResidueCupData.toyResidueCupData.cup := rfl

end L20261018

#print axioms L20261018.principalUnit_pow_surjective
#print axioms L20261018.principalUnit_pow_surjective_prime
#print axioms L20261018.toyHenselResidueData_nonempty
