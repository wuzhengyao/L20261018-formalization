import L20261018.Infra.Cohomology.Conjugation.Step011_h_conj1_tauceti_interface

/-!
# S73 R1：★★★ **共轭兼容自己做**（用户令 2026-11-04）——`H-conj1` 的真正入口

## 位置

```
H-conj1（Hyp762 `Conj1Trivial`）
  ⟸ 缺的一步：把 TauCeti 的 `inertiaTameCharacter_conj` 沿载体桥搬到战役载体
  ⟸ **本件：载体桥 `inertiaEquivInertiaLoc` 与共轭的相容**（`Hyp517` 里 `conj` 命中 0）
  ⟹ 下一步：χ_tame 的共轭不变性 ＋ Hyp766 抹 twist ⟹ 一个非零不动向量 ⟹ Hyp761 收口
```

## 交付

| 声明 | 内容 |
|---|---|
| **`transport_apply`** | 一般形：`ContinuousMulEquiv` 沿子群等式 `h ▸` 运输后，取值不变（把 `▸` 的 transport 消掉） |
| **`subgroupMap_conjNormal`** | 一般形：`ContinuousMulEquiv.subgroupMap` 与 `MulAut.conjNormal` 的相容（**与载体无关**） |
| **`inertiaEquivInertiaLoc_coe`** | `inertiaEquivInertiaLoc` 的**使用性质**：`↑(inertiaEquivInertiaLoc σ) = e σ`（消掉 `Hyp517` 的 `h ▸`） |
| **`inertiaEquivInertiaLoc_conj`** | ★★★★★ **共轭兼容**：`e ⟨(e.symm g) σ (e.symm g)⁻¹⟩ = g * e σ * g⁻¹` |
| **`inertiaEquivInertiaLoc_symm_coe`** | 逆方向的取值：`↑(e.symm y) = E.symm y` |
| **`inertiaEquivInertiaLoc_symm_conj`** | ★★★★★ **消费形态**：`e.symm (g • x) = (E.symm g) • e.symm x`（搬 χ_tame 直接用） |

## 证明范式（照 `ConjugateSubgroups.lean:117` 的④档）

用户指定的范式：**把等式推到「共轭是字面乘法」的那一侧**，在那里用 `map_mul`／`map_inv`／
`ext` 三件套收尾，再传回。本件的落点就是 `absoluteGaloisGroupRestrictEquiv F` 的**元素层乘法**：

```lean
apply Subtype.ext                                   -- 推到环境群（共轭即字面乘法）
rw [inertiaEquivInertiaLoc_coe, h1, h2,             -- 两侧各用一次「使用性质」
    map_mul, map_mul, map_inv,                      -- 三件套
    inertiaEquivInertiaLoc_coe,                     -- 传回
    ContinuousMulEquiv.apply_symm_apply]            -- e (e.symm g) = g
```

## 工艺（本轮实弹，`LESSONS` **D87**）

**`h ▸ F`（`F : X ≃ₜ* ↥M`，`h : M = M'`）的 motive 只有在 `↥M` 取「规范的子空间拓扑」时才算得出。**
若把两侧的 `TopologicalSpace ↥M`／`TopologicalSpace ↥M'` 写成**独立实例变量**，Lean 的 `▸`
会把实例一起抽象 ⟹ 报

```
invalid `▸` notation, failed to compute motive for the substitution
```

或（更隐蔽）把 `F` 的实例与目标实例判成两个不同的 metavar ⟹ 报 `Type mismatch … F`。
**修法**：一般形里**不写**这两个实例 binder，让 `↥M` 拿 `instTopologicalSpaceSubtype`
（`Subgroup` 的实际用法正是子空间拓扑）⟹ `cases h; rfl` 一次通过。
（`probe/PC4.lean` 是失败写法，`probe/PC5.lean` 是成功写法，两件留作对照。）

## 诚实边界

* 本件**只**做载体桥的共轭兼容（＝ `H-conj1` 的入口），**不**证明 `H-conj1`。
* 载体仍是 `IsNonarchimedeanLocalField F`（完备）；论文 `F` 是 Hensel ⟹ `C2` 仍待做。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-! ## ① `h ▸` 的取值（一般形） -/

/-- 一般形：`ContinuousMulEquiv` 沿子群等式 `h ▸` 运输后，取值不变。

⚠ 两侧的 `TopologicalSpace ↥M`／`↥M'` **不得**写成独立实例变量：`h ▸ F` 的 motive 只有在
`↥M` 取规范子空间拓扑时才算得出（`LESSONS` **D87**）。 -/
theorem transport_apply {H : Type*} [Group H] [TopologicalSpace H] {M M' : Subgroup H}
    (h : M = M') {X : Type*} [Group X] [TopologicalSpace X]
    (F : X ≃ₜ* ↥M) (x : X) :
    (((h ▸ F) x : ↥M') : H) = ((F x : ↥M) : H) := by
  cases h
  rfl

/-- ★★★★★ **`inertiaEquivInertiaLoc` 的使用性质**：把 `Hyp517` 定义里 `h ▸` 的 transport 消掉。

`Hyp517` 的构造是 `h ▸ ContinuousMulEquiv.subgroupMap e N`，故其**取值**在环境群里就是 `e σ`
（`transport_apply` ＋ `ContinuousMulEquiv.coe_subgroupMap_apply`，后者是 `rfl`）。 -/
theorem inertiaEquivInertiaLoc_coe (σ : ↥(TauCeti.inertiaSubgroup F)) :
    ((inertiaEquivInertiaLoc (F := F) σ : ↥(inertiaLoc F)) : TauCeti.AbsoluteGaloisGroup F) =
      (TauCeti.absoluteGaloisGroupRestrictEquiv F) σ := by
  rw [inertiaEquivInertiaLoc]
  exact transport_apply _ _ σ

/-! ## ② `subgroupMap` 的共轭自然性（一般形，与载体无关） -/

/-- ★★★★ **`ContinuousMulEquiv.subgroupMap` 与共轭的相容**（一般形）。

⚠ `MulAut.conjNormal` 要**像子群**正规（`[hNm]`）；本仓的应用里由 `Subgroup.Normal.map` 提供。 -/
theorem subgroupMap_conjNormal {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (N : Subgroup G) [N.Normal]
    [hNm : (Subgroup.map ((e : G ≃* H) : G →* H) N).Normal] (x : H) (σ : ↥N) :
    ContinuousMulEquiv.subgroupMap e N (MulAut.conjNormal (e.symm x) σ) =
      MulAut.conjNormal x (ContinuousMulEquiv.subgroupMap e N σ) := by
  ext
  simp [MulAut.conjNormal_apply, map_mul, map_inv]

/-! ## ③ ★★★★★ 共轭兼容（`H-conj1` 的入口） -/

/-- ★★★★★ **共轭兼容**：载体桥 `e := absoluteGaloisGroupRestrictEquiv F` 把 TauCeti 侧的共轭
送到战役侧的共轭。

即 `e ⟨(e.symm g) * σ * (e.symm g)⁻¹⟩ = g * e σ * g⁻¹`——这正是 `H-conj1` 搬运用得上的形态
（`Hyp762.Conj1Trivial` 讲的是战役载体 `↥(inertiaLoc F)` 上的共轭作用，而 TauCeti 的
`inertiaTameCharacter_conj` 讲的是 `AlgebraicClosure` 载体）。 -/
theorem inertiaEquivInertiaLoc_conj (g : TauCeti.AbsoluteGaloisGroup F)
    (σ : ↥(TauCeti.inertiaSubgroup F)) :
    inertiaEquivInertiaLoc (F := F)
        (MulAut.conjNormal ((TauCeti.absoluteGaloisGroupRestrictEquiv F).symm g) σ) =
      MulAut.conjNormal g (inertiaEquivInertiaLoc (F := F) σ) := by
  have h1 : ((MulAut.conjNormal ((TauCeti.absoluteGaloisGroupRestrictEquiv F).symm g) σ :
      ↥(TauCeti.inertiaSubgroup F)) : Field.absoluteGaloisGroup F) =
      (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm g * (σ : Field.absoluteGaloisGroup F) *
        ((TauCeti.absoluteGaloisGroupRestrictEquiv F).symm g)⁻¹ := by
    simp [MulAut.conjNormal_apply]
  have h2 : ((MulAut.conjNormal g (inertiaEquivInertiaLoc (F := F) σ) : ↥(inertiaLoc F)) :
      TauCeti.AbsoluteGaloisGroup F) =
      g * ((inertiaEquivInertiaLoc (F := F) σ : ↥(inertiaLoc F)) :
        TauCeti.AbsoluteGaloisGroup F) * g⁻¹ := by
    simp [MulAut.conjNormal_apply]
  apply Subtype.ext
  rw [inertiaEquivInertiaLoc_coe, h1, h2, map_mul, map_mul, map_inv, inertiaEquivInertiaLoc_coe,
    ContinuousMulEquiv.apply_symm_apply]

/-- **逆方向的使用性质**：`inertiaEquivInertiaLoc.symm` 在环境群里就是 `e.symm`。 -/
theorem inertiaEquivInertiaLoc_symm_coe (y : ↥(inertiaLoc F)) :
    (((inertiaEquivInertiaLoc (F := F)).symm y : ↥(TauCeti.inertiaSubgroup F)) :
      Field.absoluteGaloisGroup F) =
      (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm y := by
  have h := inertiaEquivInertiaLoc_coe (F := F) ((inertiaEquivInertiaLoc (F := F)).symm y)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  simpa using (congrArg (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm h).symm

/-- ★★★★★ **共轭兼容（消费形态）**：把战役载体上的共轭推到 TauCeti 载体的共轭。

这是搬 `inertiaTameCharacter_conj` 时**直接**用得上的形态：给定战役载体上的 `χ`，要算
`χ (conjNormal g x)` 就要先把 `x` 沿 `inertiaEquivInertiaLoc.symm` 送到 `AlgebraicClosure` 侧。 -/
theorem inertiaEquivInertiaLoc_symm_conj (g : TauCeti.AbsoluteGaloisGroup F)
    (x : ↥(inertiaLoc F)) :
    ((inertiaEquivInertiaLoc (F := F)).symm (MulAut.conjNormal g x)) =
      MulAut.conjNormal ((TauCeti.absoluteGaloisGroupRestrictEquiv F).symm g)
        ((inertiaEquivInertiaLoc (F := F)).symm x) := by
  apply (inertiaEquivInertiaLoc (F := F)).injective
  rw [ContinuousMulEquiv.apply_symm_apply, inertiaEquivInertiaLoc_conj]
  exact congrArg (MulAut.conjNormal g)
    (ContinuousMulEquiv.apply_symm_apply (inertiaEquivInertiaLoc (F := F)) x).symm

end L20261018

#print axioms L20261018.transport_apply
#print axioms L20261018.inertiaEquivInertiaLoc_coe
#print axioms L20261018.subgroupMap_conjNormal
#print axioms L20261018.inertiaEquivInertiaLoc_conj
#print axioms L20261018.inertiaEquivInertiaLoc_symm_coe
#print axioms L20261018.inertiaEquivInertiaLoc_symm_conj
