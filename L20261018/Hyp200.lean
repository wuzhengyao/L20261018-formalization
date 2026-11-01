import L20261018.Hyp199

/-!
# R1053（**S29 · ④.2 第三步**）：范数形态 —— `normGroup` 版

`Hyp199` 给的是「`y ∈ Lˣ` 的范数」。本文件把它翻译成 **(R1) 的范数形态**所需的群论陈述：

```
u ∈ N_{L/F}(Lˣ) ∩ {v-整单位}   ⟹   u ∈ F^{×p}
```

其中 `N(Lˣ)` 用 `TauCeti.normGroup F L`（`Hyp164` 右端的同一对象）。

## 假设

* `[Fact (Irreducible (Xᵖ − Cπ))]`：**模型是域**。这条是 `normGroup` 的类型要求（`[Field L]`），
  数学上是「`π ∉ Fᵖ`」——在 DVF 里由 `v(π) = 1` 自动成立（若 `π = aᵖ` 则 `1 = p·v(a)` 在 `ℤ` 中不可能）。
  **登记为独立的基建项**（Capelli／`Xᵖ − a` 不可约判据），本阶段先显式作假设。
* `[Module.Finite F L]`：由 `Hyp193.finite_adjoinRoot_uniformizer_f` 可给（此处作假设以免类型类歧义）。
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section NormGroupForm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- **④.2 范数形态**：`v`-整单位 `u`（`valOfUnitOf v u = 0`）若是 `L = AdjoinRoot(Xᵖ − π)` 的范数，
则 `u` 是 `F` 中的 `p` 次幂。

这正是 `Hyp164.residuePhi_injective_iff_norm_of_bridge` 右端的条件（`(R1)` 的范数刻画）。 -/
theorem mem_pow_of_mem_normGroup_of_valOfUnitOf_eq_zero
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hv : ValCompat (F := F) v)
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    {u : Fˣ} (hval : valOfUnitOf (p := p) v u = 0)
    (hmem : u ∈ normGroup F (AdjoinRoot (X ^ p - C (π : F)))) :
    u ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
  obtain ⟨y, hy⟩ := (TauCeti.mem_normGroup_iff (K := F) (L := AdjoinRoot (X ^ p - C (π : F)))).mp hmem
  -- `normUnits F y = u`
  have hyu : TauCeti.Algebra.normUnits F y = u := by
    ext
    rw [TauCeti.Algebra.coe_normUnits]
    exact hy
  have hval' : valOfUnitOf (p := p) v (TauCeti.Algebra.normUnits F y) = 0 := by
    rw [hyu]; exact hval
  have hmain := normUnits_mem_pow_of_valOfUnitOf_eq_zero (F := F) p hp hv hπ hp2 y hval'
  rwa [hyu] at hmain

end NormGroupForm

end L20261018

#print axioms L20261018.mem_pow_of_mem_normGroup_of_valOfUnitOf_eq_zero

