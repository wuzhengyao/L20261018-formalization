import L20261018.Hyp686

/-!
# S59 R9：★★★ **A1 收口** —— `ker (cupLC) ≤ ker (tameLC)` ⟹ `TameSymbolFactors`

## 意义

`G2-PLAN.md` §2 的 A1 格是 `(R2)` 的**判据格**。本件交出它的**构造向**（难向）：

```
tameKernelCond cup val  ⟹  TameSymbolFactors cup val
```

⟹ `(R2)` 从「∃ res 的存在性命题」变成「**`Finsupp` 两像的核包含**」这一条可操作判据；
`Hyp680.tameSymbolFactors_iff` 再把后者等价于 `TameResidueFacts`／`∃D`。
**判据阶梯现在两头都接地**：`TameSymbolFactors ⟺ tameSumCond ⟺ 链式 ⟸ 点式`（`Hyp683`–`Hyp685`）
＋ 本件的反方向。

## 证明（**不用商空间 API** —— 代表选取法）

```
repC cup y := Classical.choose y.2                        -- cupLC cup (repC y) = ↑y
hdiff  : tameLC val (repC x + repC y - repC (x+y)) = 0     -- ⟸ hker（x+y 的系数恰相加）
hdiff' : tameLC val (c • repC x - repC (c • x)) = 0        -- ⟸ hker
g := ⟨fun y => tameLC val (repC cup y), hdiff, hdiff'⟩     -- ↥(range (cupLC cup)) →ₗ ker v̄
proj := (range (cupLC cup)).subtype 的左逆                 -- exists_leftInverse_of_injective
res  := g.comp proj                                        -- res (∪ a b) = tame a b
```

**关键工艺**：`repC` 必须是**顶层 `private noncomputable def`**，不能是 `by` 块里的 `let`
（`let` 绑定的名字在后续 `have` 的**类型**里不可见 —— 本轮实测两次失败的主因）。

## 诚实边界

* 本件只证**构造向**。反方向（`TameSymbolFactors ⟹ tameKernelCond`，需 `Finsupp.induction`
  证 `res ∘ cupLC = tameLC`，≈10 行）**未做** ⟹ 严格说 A1 的 `↔` 尚未闭合。
* **不**证 `tameKernelCond`（`(R2)` 仍 `∅-open`）：本件把它的**入口**固定下来，内容未变。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018
section Assembly
variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- 代表选取（提到顶层，避免 `let` 在 `by` 块内不可见）。 -/
private noncomputable def repC (cup : V →ₗ[k] V →ₗ[k] H2) :
    ↥(LinearMap.range (cupLC cup)) → ((V × V) →₀ k) := fun y => Classical.choose y.2

private theorem repC_spec (cup : V →ₗ[k] V →ₗ[k] H2)
    (y : ↥(LinearMap.range (cupLC cup))) : cupLC cup (repC cup y) = (y : H2) :=
  Classical.choose_spec y.2

/-- ★★★ **A1 收口**：`ker (cupLC) ≤ ker (tameLC)` ⟹ `TameSymbolFactors`。 -/
theorem tameSymbolFactors_of_tameKernelCond (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (h : tameKernelCond cup val) : TameSymbolFactors cup val := by
  classical
  have hker : LinearMap.ker (cupLC cup) ≤ LinearMap.ker (tameLC val) :=
    (tameKernelCond_iff_ker_le cup val).mp h
  have hdiff : ∀ x y : ↥(LinearMap.range (cupLC cup)),
      tameLC val (repC cup x + repC cup y - repC cup (x + y)) = 0 := by
    intro x y
    refine hker (LinearMap.mem_ker.mpr ?_)
    rw [map_sub, map_add, repC_spec, repC_spec, repC_spec, Submodule.coe_add, sub_self]
  have hdiff' : ∀ (c : k) (x : ↥(LinearMap.range (cupLC cup))),
      tameLC val (c • repC cup x - repC cup (c • x)) = 0 := by
    intro c x
    refine hker (LinearMap.mem_ker.mpr ?_)
    rw [map_sub, map_smul, repC_spec, repC_spec, Submodule.coe_smul, sub_self]
  let g : ↥(LinearMap.range (cupLC cup)) →ₗ[k] ↥(LinearMap.ker val) :=
    { toFun := fun y => tameLC val (repC cup y)
      map_add' := fun x y => by
        have h1 := hdiff x y
        rw [map_sub, map_add] at h1
        exact (sub_eq_zero.mp h1).symm
      map_smul' := fun c x => by
        have h1 := hdiff' c x
        rw [map_sub, map_smul] at h1
        exact (sub_eq_zero.mp h1).symm }
  have hg : ∀ x : (V × V) →₀ k, g ⟨cupLC cup x, ⟨x, rfl⟩⟩ = tameLC val x := by
    intro x
    have hz : tameLC val (repC cup ⟨cupLC cup x, ⟨x, rfl⟩⟩ - x) = 0 := by
      refine hker (LinearMap.mem_ker.mpr ?_)
      rw [map_sub, repC_spec, sub_self]
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  obtain ⟨proj, hproj⟩ := LinearMap.exists_leftInverse_of_injective
    (LinearMap.range (cupLC cup)).subtype
    ((LinearMap.ker_eq_bot).mpr (fun x y h => Subtype.ext h))
  have hproj' : ∀ y : ↥(LinearMap.range (cupLC cup)), proj (y : H2) = y := by
    intro y
    have hh := congrFun (congrArg DFunLike.coe hproj) y
    simpa [LinearMap.comp_apply] using hh
  refine ⟨g.comp proj, ?_⟩
  intro a b
  have hsingle : cupLC cup (Finsupp.single (a, b) (1 : k)) = cup a b := by
    rw [cupLC, Finsupp.linearCombination_single, one_smul]
  have htame : tameLC val (Finsupp.single (a, b) (1 : k)) = tameExpr val a b := by
    rw [tameLC, Finsupp.linearCombination_single, one_smul]
  rw [← hsingle, LinearMap.comp_apply,
    hproj' ⟨cupLC cup (Finsupp.single (a, b) (1 : k)), ⟨_, rfl⟩⟩, hg, htame]

end Assembly
end L20261018

/-! ## 机检读数 -/

#print axioms L20261018.tameSymbolFactors_of_tameKernelCond
