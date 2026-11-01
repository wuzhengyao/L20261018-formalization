import L20261018.Infra.Cohomology.Boundary.Step023_compressed_cocycle

/-!
# R1116（**(R2)-2 装配 a2：逐点棱柱恒等式在 `cycles 1` 上的落地**）

## 内容

`PLAN-R2` §H-22.2 的 a2：对 `w : (inhomogeneousCochains A).cycles 1`，令
`M := iCycles 1 w`（`M : (Fin 1 → S) → A`），则对每个 `j : Fin 1 → S`：

```
((cochainsMap c_g (conjCoeffHom A S g)).f 1 M) j - M j
  = (d 0 1 (fun _ => M (fun _ => g))) j
```

即**共轭余链映射与恒等之差 = 一个上边缘**（棱柱算子 `hM = M (·g)`）。

## 证明（三块拼接，全部来自前面几轮）

1. `cochainsMap_apply`（`Hyp238`）：`((cochainsMap f φ).f 1 M) j = φ (M (f ∘ j))`；
2. `conjCoeffHom_apply`（`Hyp235`）：`φ = ρ_g`（底层）；
3. `d_zero_one_apply`（`Hyp243`）：`(d 0 1 u) j = ρ (j 0) (u _) - u _`；
4. **`Hyp240.conj_one_cochain`**：`ρ_g (f (g⁻¹ s g)) = ρ_s (f g) + f s - f g`，
   其中 `f t := M (·t)`，`s := j 0`，`hf` 由 **`Hyp244.compressed_mem_cocycles`** 提供。

技术要点：`j : Fin 1 → S` 须先化成 `fun _ => j 0`（`funext k; fin_cases k; rfl`）；
`conj_g ∘ (fun _ => j 0) = fun _ => g⁻¹ * (j 0) * g` 须经 `Subtype.ext ＋ conjSubtypeHom_coe`。

## 本轮

| 声明 | 内容 |
|---|---|
| **`cochainsMap_one_sub_apply`** | ★★ **a2**：逐点 `(cochainsMap c_g φ).f 1 M − M = d 0 1 u` |

**下一轮**：a3（`cancel_mono (iCycles 1)` 升到 `cycles 1`）＋ a4（`toCycles_comp_homologyπ`
⟹ (★) ⟹ `conjMap_one_eq_one_of` ⟹ **`deltaTwo` 前提不含具名假设**）。

## 🔧 工艺

1. **`rw` 前须先 `beta_reduce`**：`rw [cochainsMap_apply]` 后出现的形状是
   `(fun j => φ (M (f ∘ j))) (fun x => j 0)`，**未 beta 归约** ⟹ `rw [conjCoeffHom_apply]` 找不到模式。
2. **同一对象的不同记法（`A.ρ (j 0)` vs `(A.ρ.comp S.subtype) (j 0)`）使 `abel` 失败**：
   `abel` 把它们当**不同原子**。须先 `simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]`
   对齐，再 `abel`。
3. **`S`-层的等式用 `Subtype.ext` ＋ `conjSubtypeHom_coe`**（`conjSubtypeHom_coe` 说的是 `G`-层强转）。
-/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- ★★ **(R2)-2 装配 a2**：逐点棱柱恒等式。

`M := iCycles 1 w`。共轭余链映射与恒等之差在每点 `j` 处等于上边缘 `d 0 1 (fun _ => M (·g))`。 -/
theorem cochainsMap_one_sub_apply (A : Rep k G) (S : Subgroup G) [S.Normal] (g : S)
    (w : (groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).cycles 1) (j : Fin 1 → S) :
    (((groupCohomology.cochainsMap (conjSubtypeHom S g) (conjCoeffHom A S g)).f 1)
        ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).iCycles 1 w)) j
      - ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).iCycles 1 w) j
      = ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).d 0 1
          (fun _ => ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).iCycles 1 w)
            (fun _ => g))) j := by
  set M := ((groupCohomology.inhomogeneousCochains (Rep.res S.subtype A)).iCycles 1 w) with hM
  have hf := compressed_mem_cocycles A S w
  have hc := conj_one_cochain A S g (fun t : S => M (fun _ => t)) hf (j 0)
  rw [cochainsMap_apply, d_zero_one_apply]
  have hj : j = (fun _ => j 0) := by funext k; fin_cases k; rfl
  rw [hj]
  beta_reduce
  rw [conjCoeffHom_apply]
  have e1 : (⇑(conjSubtypeHom S g) ∘ (fun _ : Fin 1 => j 0))
      = (fun _ => (g : S)⁻¹ * (j 0) * g) := by
    funext k
    exact Subtype.ext (by simp [conjSubtypeHom_coe])
  rw [e1]
  beta_reduce
  rw [hc]
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  abel

end L20261018

#print axioms L20261018.cochainsMap_one_sub_apply
