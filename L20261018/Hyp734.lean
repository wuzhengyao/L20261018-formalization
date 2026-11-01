import Hyp733

/-!
# S66 R3：分片 **4c-v（第一格）** —— `map φ fC` 的**分解**

由 `S66-4CV-PLAN.md` §1 锁定的方向：`map φ f : H^n(cod φ, X) → H^n(dom φ, Y)`，
且它就是 "`f ∘（沿 φ 拉回）`"。故当系数映射**逐点分解** `fC = sub ∘ ι`
（`ι : T → Cᴵ` 在同一群 `G⧸I` 上、`sub : Cᴵ ↪ C` 沿 `φ`）时

```
map φ fC  =  coeffMap ι  ≫  map φ sub
```

即 **`map` 可拆成"先系数映射、再纯膨胀"**。这是 4d 追图里把
`map φ fC 1`（连续模型）换成 `Infl_C ∘ coeffMap ι`（`inflStep` 的逆的输入形状）的那一格。

## 出处与纪律

* `ContinuousCohomology.map_comp`（`#check` 实测式见 `S66-4CV-PLAN.md` §1）
  ＝ "compatible pair 的合成"；本件取 `φ := id` 把 `coeffMap` 抽出来；
* `TauCeti.ContinuousCohomology.coeffMap_def`（`Functoriality.lean:218`，**`rfl` 级**）
  ＝ `coeffMap f n = map (id) f n`；
* 方向检查（`M12`）写在 `S66-4CV-PLAN.md` §1，**`map` 与 `φ` 反向**。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

universe u

variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ★★★★ **4c-v 的分解格**：`map φ fC = coeffMap ι ≫ map φ sub`（`φ = G → G⧸I`）。

其中 `f : T ⟶ Cᴵ` 是 `G⧸I` 上的系数映射（`ι`），`g : Cᴵ ⟶ C` 是沿 `φ` 的（`sub`），
右端的 `fC` 是 `(res φ).map f ≫ g`（即 `sub ∘ ι`）。

**用途**：4d 里把 `map φ fC 1 ∘ e` 换成 `coeffMap ι 1 ∘ map φ sub 1 ∘ e`，
于是 `inflStep = (map φ sub)⁻¹` 可直接消去 `map φ sub`，只剩下 `coeffMap ι` 与 `Hyp733` 的 `contM ∘ ι = 0`。 -/
theorem coeffMap_comp_map_quotientMk (I : Subgroup G) [I.Normal]
    (X : TopRep R (G ⧸ I)) (Y : TopRep R (G ⧸ I)) (Z : TopRep R G)
    (f : X ⟶ Y)
    (g : TopRep.res (↑(Subgroup.quotientMkContinuousMonoidHom I) : G →* (G ⧸ I)) Y ⟶ Z)
    (n : ℕ) :
    ContinuousCohomology.coeffMap f n ≫
        ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I) g n =
      ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
        ((TopRep.resFunctor
          (↑(Subgroup.quotientMkContinuousMonoidHom I) : G →* (G ⧸ I))).map f ≫ g) n := by
  rw [TauCeti.ContinuousCohomology.coeffMap_def]
  exact (ContinuousCohomology.map_comp
    (φ := ContinuousMonoidHom.id (G ⧸ I))
    (ψ := Subgroup.quotientMkContinuousMonoidHom I) f g n).symm

end L20261018

#print axioms L20261018.coeffMap_comp_map_quotientMk
