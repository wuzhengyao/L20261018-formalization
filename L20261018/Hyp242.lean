import L20261018.Hyp241

/-!
# R1113（**(R2)-2 的 `n = 1` 归结：只剩一条具体等式**）

## 本轮的定位

`(R2)-2` 的 `n = 1` 收口需要 `conjMap A S g 1 = 𝟙`（`g ∈ S`）。本轮把它**归结为一条具体等式**：

```
cocyclesMap c_g 1 ≫ π A 1 = π A 1          (★)
```

（`π A 1 : cocycles 1 ⟶ H¹` 是余圈到上同调的商映射，`Epi`。）
由 `π_map`（`π ≫ conjMap = cocyclesMap ≫ π`）与 `cancel_epi (π A 1)` 立得 `conjMap = 𝟙`。

## 为什么 (★) 足够、且 (★) 是「正确的剩余」

`(R2)-2` 的三块：

| # | 内容 | 件 | 状态 |
|---|---|---|---|
| ① | 余链层：`c_g f - f = d₀₁ (f g)` | `Hyp240.conj_one_cochain_sub` | ✅ |
| ② | 余圈层：共轭后仍余圈且**同类** | `Hyp241.H1π_conjCocycle` | ✅ |
| ③ | **(★)**：`cocyclesMap c_g 1 ≫ π = π` | **本轮归结** | ⬜ |

**(★) 的证明路线（已完全确定，下一轮执行）**：对 `w : cycles 1`，令
`u : (Fin 0 → S) → A := fun _ => (w : X 1) (fun _ => g)`。则

```
cocyclesMap c_g 1 w - w = toCycles 0 1 u
```

（用 `cancel_mono (iCycles 1)` ＋ `cyclesMap_i` ＋ `toCycles_i` ＋ ① 的逐点形式。）
再由 **`HomologicalComplex.toCycles_comp_homologyπ : toCycles i j ≫ homologyπ j = 0`**
得 `π 1 (cocyclesMap c_g 1 w - w) = 0`，即 (★)。

## 本轮

| 声明 | 内容 |
|---|---|
| **`iCycles_cyclesMap`** | `iCycles` 关于 `cyclesMap` 的自然性（**任意次数**；`Hyp238` 只有 `n = 0`） |
| **`conjMap_one_eq_one_of`** | ★★★ **(R2)-2 的 `n = 1` 归结**：(★) ⟹ `conjMap A S g 1 = 𝟙` |

## 🔧 工艺发现

**`Epi (groupCohomology.π A n)` 的实例解析需要 `backward.isDefEq.respectTransparency false`。**
`π A n` 是 `(inhomogeneousCochains A).homologyπ n` 的 `abbrev`，而 mathlib 的
`instance : Epi (K.homologyπ i)` 本身就是在该选项下定义的（`ShortComplex/HomologicalComplex.lean:155`）。
⟹ 不设该选项时 `cancel_epi (π A 1)` 报 **`synthInstanceFailed: Epi (π A n)`**（而非实例不存在）。
**动作**：凡对 `groupCohomology.π` 做 `cancel_epi`／`epi_iff_surjective`，先设该选项。
-/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- **`iCycles` 关于 `cyclesMap` 的自然性（任意次数）**：
`iCycles (cyclesMap φ n c) = φ.f n (iCycles c)`。

（`Hyp238.iCocycles_cocyclesMap` 只有 `n = 0`；本件是任意次数的版本。） -/
theorem iCycles_cyclesMap (A B : Rep k G) (φ : A ⟶ B) (n : ℕ)
    (c : (groupCohomology.inhomogeneousCochains A).cycles n) :
    (groupCohomology.inhomogeneousCochains B).iCycles n
        (HomologicalComplex.cyclesMap (groupCohomology.cochainsMap (MonoidHom.id G) φ) n c)
      = ((groupCohomology.cochainsMap (MonoidHom.id G) φ).f n)
          ((groupCohomology.inhomogeneousCochains A).iCycles n c) :=
  congrArg (fun t => t c) (HomologicalComplex.cyclesMap_i
    (groupCohomology.cochainsMap (MonoidHom.id G) φ) n)

/-- ★★★ **(R2)-2 的 `n = 1` 归结**：只要共轭余链映射在 `H¹` 上平凡
（`cocyclesMap c_g 1 ≫ π = π`），就有 `conjMap A S g 1 = 𝟙`。

证明：`π_map` 给 `π ≫ conjMap = cocyclesMap ≫ π`，再用 `π` 的 `Epi` 性消去。 -/
theorem conjMap_one_eq_one_of (A : Rep k G) (S : Subgroup G) [S.Normal] (g : S)
    (h : groupCohomology.cocyclesMap (conjSubtypeHom S g) (conjCoeffHom A S g) 1
          ≫ groupCohomology.π (Rep.res S.subtype A) 1
        = groupCohomology.π (Rep.res S.subtype A) 1) :
    conjMap A S g 1 = 𝟙 (groupCohomology (Rep.res S.subtype A) 1) := by
  rw [conjMap, ← cancel_epi (groupCohomology.π (Rep.res S.subtype A) 1)]
  rw [groupCohomology.π_map]
  rw [h]
  exact (Category.comp_id _).symm

/-- ★★ **(R2)-2 的 `n = 1` 归结（具名假设形式）**：
把 (★) 写成 `innerConjTrivialIn A S 1` 的充分条件，便于下一轮直接接入。 -/
theorem innerConjTrivialIn_one_of (A : Rep k G) (S : Subgroup G) [S.Normal]
    (h : ∀ g : S, groupCohomology.cocyclesMap (conjSubtypeHom S g) (conjCoeffHom A S g) 1
          ≫ groupCohomology.π (Rep.res S.subtype A) 1
        = groupCohomology.π (Rep.res S.subtype A) 1) :
    innerConjTrivialIn A S 1 :=
  fun g => conjMap_one_eq_one_of A S g (h g)

end L20261018

#print axioms L20261018.iCycles_cyclesMap
#print axioms L20261018.conjMap_one_eq_one_of
#print axioms L20261018.innerConjTrivialIn_one_of
