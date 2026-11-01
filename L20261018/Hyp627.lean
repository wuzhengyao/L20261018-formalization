import Hyp626

/-!
# S52 R20：**N1 ＋ N2** —— `φ : Γ_F →* MulAut κ̄` 构造出来，且 `ker φ = I`

## 0 本件在路线上的位置

`PROMPT-S52` §1.2 的 **N1**（把 R19 的「良定义」升成**函数／群同态**）与 **N2**（`ker φ = I`）。
`Hyp626.residue_action_welldef` 只给了「`residue x = residue y ⟹ residue (σx) = residue (σy)`」，
**没有**把作用写成 `κ̄ → κ̄`，因此 R19 **明确未声称**复合相容。本件补上这一格：

```
subringAct σ   : ↥𝒪_W →+* ↥𝒪_W                      -- σ 在赋值环上的限制
residueRingAct σ : κ̄ ≃+* κ̄   (κ̄ = ↥𝒪_W ⧸ 𝔪_W)       -- 环自同构
residueAct     : Γ_F →* MulAut κ̄                      -- ★ N1
residueAct_ker : (residueAct W hval).ker = inertia W hval   -- ★ N2
```

## 1 数学（全部是「值保持 ＋ 两条剩余判据」的组合，无新数学）

* `σ` 保 `𝒪_W`（`hstab_of_hval`，由**值保持**给出）⟹ `subringAct σ` 是赋值环的环同态；
* `σ` 保 `𝔪_W`（`x ∈ 𝔪 ⟺ W x < 1`，值保持 ⟹ 两侧同时成立）⟹ `subringAct σ` 是 **local hom**
  （`IsLocalHom` 只需「单位原像仍单位」，由 `σ⁻¹` 也是环同态给出）⟹ 可以过 `ResidueField.map`；
* `residueRingAct σ` 的逆是 `residueRingAct σ⁻¹`（`subringAct σ⁻¹ ∘ subringAct σ = id`）；
* `residueAct` 的乘法相容：在 `residue x` 这类生成元上验证，`subringAct (σ*τ) = subringAct σ ∘ subringAct τ`；
* **N2**：`Hyp625.mem_inertia_iff_residue_eq`（`σ ∈ I ⟺ σ` 在 `κ̄` 上作用平凡）＋ `residue` 满射
  ⟹ `ker φ = I`。

⟹ **`hval` 第五、六次成为唯一实质输入**（`IsLocalHom` 与 `ker` 两处）。

## 2 本件交付（全部机检，零 `sorry`，axioms 恰三条）

| 声明 | 内容 |
|---|---|
| `subringAct` / `subringAct_coe` | `σ` 在 `𝒪_W` 上的限制（环同态） |
| `subringAct_comp_self` / `subringAct_self_comp` | 双向逆（`σ⁻¹` 侧） |
| `subringAct_symm_apply` / `subringAct_apply_symm` | 元素层逆（复合用，绕开 `map_comp` 的依赖实例重写） |
| `subringAct_mul` | `subringAct (σ*τ) x = subringAct σ (subringAct τ x)` |
| `subringAct_isLocalMap` / `subringAct_isLocalHom` | `σ` 保 `𝔪_W` ⟹ `IsLocalHom`（`ResidueField.map` 的前提） |
| **`residueRingAct`** | ★★★★ `κ̄ ≃+* κ̄`（**环**自同构；`MulAut` 的强化形态） |
| **`residueAct`** | ★★★★★★ **N1**：`Γ_F →* MulAut κ̄` |
| `residueAct_apply_residue` | `φ(σ)(residue x) = residue (σ x)`（**接口引理**，N3／N4 全靠它） |
| **`residueAct_ker`** | ★★★★★★ **N2**：`ker φ = I`（核恰是惯性子群） |
| `residueAct_eq_one_iff` / `mem_inertia_iff_residueAct_eq_one` | 成员判据（`σ ∈ I ⟺ φ(σ) = 1`） |

## 3 工艺（本轮唯一卡点，均为记法层 —— `LESSONS` B1／规则 27）

1. **`map_map` 不能在依赖实例下 `rw`**：`ResidueField.map` 带 `[IsLocalHom f]` 实例参数，
   对它 `rw`（把 `f` 换成 `g ∘ f`）会报 `motive is not type correct`。
   ⟹ 改走**元素层**：在 `residue x` 上用 `map_residue`（它是 `rfl`）算，再用 `residue_surjective` 收；
   或用 `subringAct_symm_apply` 这类**元素等式**重写。
2. **`MulAut` 的乘法方向**：`(e₁ * e₂) x = e₁ (e₂ x)`（实测 `rfl`），与 `AlgEquiv` 一致；
   但 `((residueRingAct (σ*τ)).toMulEquiv) y` 与 `(e₁ * e₂) y` 之间隔着一层 `MulEquiv` 包装，
   `simp` 找不到 `MulEquiv.mul_apply`（**不存在**）⟹ 用 `change` 走到元素层
   （`residueRingAct` 的 `toFun` 是 `ResidueField.map`，`map_residue` 是 `rfl`，故 `change` 通得过）。
3. `IsLocalHom` 的 `instance` 体**不可**引用自身：`subringAct_isLocalMap` 里若用
   `IsUnit.of_map (subringAct σ⁻¹) h` 会触发对 `subringAct σ⁻¹` 的**同一实例**的搜索（递归合成失败）。
   ⟹ 直接 `IsUnit.map (subringAct σ⁻¹) h`（`RingHom` 是 `MonoidHomClass`，不经过 `IsLocalHom`）。

## 4 诚实边界

* 仍**不证** `(CI)`：`FbarValuationHyp₄`（`Hyp623`）仍是假设。
* **未做**：`residueAct` 的**满射性**与其像 ＝ `Gal(κ̄/κ)`（**N3**，需 `κ ⊆ κ̄` 的嵌入
  `ResidueField ↥𝒪[F] →+* ResidueField ↥𝒪_W` ＋ 分解群／惯性群的固定域论）。
* **未做**：单位层 Kummer 类在 `I` 上为 0（**N4**）。
* 本件**不增覆盖率**（`(R2)` 仍是 `∅-open`），但把 `hyp-residue-galois` 的 `φ` 从假设变成**构造**。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section ResidueActionHom

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

/-- `σ` 在赋值环 `𝒪_W` 上的限制（环同态）。 -/
def subringAct (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    ↥W.valuationSubring →+* ↥W.valuationSubring where
  toFun x := ⟨σ (x : SeparableClosure F), hstab_of_hval W hval σ x.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp] theorem subringAct_coe (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F)
    (x : ↥W.valuationSubring) :
    ((subringAct W hval σ x : ↥W.valuationSubring) : SeparableClosure F)
      = σ (x : SeparableClosure F) := rfl

theorem subringAct_comp_self (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    (subringAct W hval σ⁻¹).comp (subringAct W hval σ) = RingHom.id ↥W.valuationSubring := by
  ext x
  simp

theorem subringAct_self_comp (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    (subringAct W hval σ).comp (subringAct W hval σ⁻¹) = RingHom.id ↥W.valuationSubring := by
  ext x
  simp

theorem subringAct_symm_apply (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F)
    (x : ↥W.valuationSubring) :
    (subringAct W hval σ⁻¹) ((subringAct W hval σ) x) = x := by
  ext
  simp

theorem subringAct_apply_symm (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F)
    (x : ↥W.valuationSubring) :
    (subringAct W hval σ) ((subringAct W hval σ⁻¹) x) = x := by
  ext
  simp

theorem subringAct_mul (σ τ : SeparableClosure F ≃ₐ[F] SeparableClosure F)
    (x : ↥W.valuationSubring) :
    subringAct W hval (σ * τ) x
      = subringAct W hval σ (subringAct W hval τ x) := by
  ext
  simp

/-- 值保持 ⟹ `σ` 把**非单位映到非单位**（`σ` 是环自同构，故单位原像仍单位）：
这是 `ResidueField.map` 的 `IsLocalHom` 前提。 -/
theorem subringAct_isLocalMap (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    ∀ a, IsUnit (subringAct W hval σ a) → IsUnit a := by
  intro a ha
  have h2 : (subringAct W hval σ⁻¹) ((subringAct W hval σ) a) = a :=
    subringAct_symm_apply W hval σ a
  rw [← h2]
  exact IsUnit.map (subringAct W hval σ⁻¹) ha

instance subringAct_isLocalHom (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    IsLocalHom (subringAct W hval σ) where
  map_nonunit := subringAct_isLocalMap W hval σ

/-- ★★★★ **剩余域上的环自同构** `κ̄ ≃+* κ̄`（`κ̄ = 𝒪_W/𝔪_W`）。 -/
noncomputable def residueRingAct (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    IsLocalRing.ResidueField ↥W.valuationSubring ≃+*
      IsLocalRing.ResidueField ↥W.valuationSubring :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map (subringAct W hval σ)) ⟨by
    intro x y hxy
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    simp only [IsLocalRing.ResidueField.map_residue] at hxy ⊢
    have h := congrArg (IsLocalRing.ResidueField.map (subringAct W hval σ⁻¹)) hxy
    simp only [IsLocalRing.ResidueField.map_residue] at h
    rwa [subringAct_symm_apply W hval σ a, subringAct_symm_apply W hval σ b] at h, by
    intro y
    refine ⟨IsLocalRing.ResidueField.map (subringAct W hval σ⁻¹) y, ?_⟩
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    simp only [IsLocalRing.ResidueField.map_residue]
    rw [subringAct_apply_symm W hval σ r]⟩

@[simp] theorem residueRingAct_apply_residue
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (x : ↥W.valuationSubring) :
    residueRingAct W hval σ (IsLocalRing.residue ↥W.valuationSubring x)
      = IsLocalRing.residue ↥W.valuationSubring (subringAct W hval σ x) :=
  IsLocalRing.ResidueField.map_residue _ _

/-- ★★★★★★ **N1：`Γ_F` 在剩余域 `κ̄ = 𝒪_W/𝔪_W` 上的作用** `φ : Γ_F →* MulAut κ̄`。
`φ` 从此**由 `W` 导出**，不再是对 `hyp-residue-galois` 的假设。 -/
noncomputable def residueAct :
    Gal(SeparableClosure F/F) →*
      MulAut (IsLocalRing.ResidueField ↥W.valuationSubring) :=
  MonoidHom.mk' (fun σ => (residueRingAct W hval σ).toMulEquiv) (by
    intro σ τ
    refine MulEquiv.ext (fun y => ?_)
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    change IsLocalRing.residue ↥W.valuationSubring (subringAct W hval (σ * τ) r)
      = IsLocalRing.residue ↥W.valuationSubring
        (subringAct W hval σ (subringAct W hval τ r))
    rw [subringAct_mul W hval σ τ r])

/-- **接口引理**（N3／N4 全靠它）：`φ(σ)` 把 `residue x` 送到 `residue (σ x)`。 -/
@[simp] theorem residueAct_apply_residue (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F)
    (x : ↥W.valuationSubring) :
    residueAct W hval σ (IsLocalRing.residue ↥W.valuationSubring x)
      = IsLocalRing.residue ↥W.valuationSubring
        ⟨σ (x : SeparableClosure F), hstab_of_hval W hval σ x.2⟩ :=
  residueRingAct_apply_residue W hval σ x

/-- ★★★★★★ **N2：`ker φ = I`** —— 剩余作用的核**恰是**惯性子群。
⟹ `Γ_κ := Γ_F ⧸ I` 就是 `φ` 的像，`Hyp614` 的 `hCI` 里的 `Γ⧸I` 从此有具体载体。 -/
theorem residueAct_ker :
    (residueAct W hval).ker = inertia W hval := by
  ext σ
  rw [MonoidHom.mem_ker, mem_inertia_iff_residue_eq W hval σ]
  constructor
  · intro h x
    have hx := congrArg (fun (e : MulAut (IsLocalRing.ResidueField ↥W.valuationSubring)) =>
      e (IsLocalRing.residue ↥W.valuationSubring x)) h
    simpa using hx
  · intro h
    ext y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    simpa using h x

/-- 成员判据：`σ` 的剩余作用平凡 ⟺ `σ` 在 `I` 里。 -/
theorem mem_inertia_iff_residueAct_eq_one (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    σ ∈ inertia W hval ↔ residueAct W hval σ = 1 := by
  rw [← residueAct_ker W hval, MonoidHom.mem_ker]

end ResidueActionHom

end L20261018

#print axioms L20261018.subringAct_isLocalMap
#print axioms L20261018.residueRingAct
#print axioms L20261018.residueAct
#print axioms L20261018.residueAct_ker
#print axioms L20261018.mem_inertia_iff_residueAct_eq_one
