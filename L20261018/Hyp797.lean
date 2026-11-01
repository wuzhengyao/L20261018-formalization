import L20261018.Hyp796

/-!
# S77 R5：第 5 步 (b) 的**代数内核** —— 有「左逆系数映射」⟹ `explicitCup01` 非零

## 命题（一般形，无群论假设）

设 `μ : M →+ N →+ P` 是连续 `G`-配对，`m ∈ H⁰(G,M)`，`e : P →+[G] N` 连续且

```
e (μ m x) = x        ∀ x ∈ N          （「在 m 处的左逆」）
```

则 `explicitCup01 μ m : H¹(G,N) → H¹(G,P)` **是单射**：`yb ≠ 0 ⟹ explicitCup01 μ m yb ≠ 0`。

## 为什么这条就够（**不需要**「有左逆 ⟹ 单射」的抽象论证）

因果方向是**反的**：设 `explicitCup01 μ m yb = 0`，用库内
**`explicitCoeff1_explicitCup01`**（NSW (1.4.2)，`Cup/Naturality.lean:362`）把 `e` 推到外面：

```
explicitCoeff1 e (explicitCup01 μ m yb) = explicitCup01 μ' m yb ,   μ' m' x := e (μ m' x)
```

左端是 `0`，而右端逐余环是 `g ↦ e (μ m (b g)) = b g`（`hleft`），故右端就是 `yb`
（`explicitCup01_mk`：`Cup/Product.lean:270`）⟹ `yb = 0`。

**⟹ `e` 只需存在，不需要可逆、不需要连续性以外的任何条件**，也不需要 `H¹(G,M) ≅ Hom(G,M)`。

## 本件交付

| 声明 | 内容 |
|---|---|
| **`explicitCup01_ne_zero_of_leftInverse`** | ★★★★★ 上述一般形（第 5 步 (b) 的全部代数内容） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology

namespace L20261018

/-- ★★★★★ **有左逆系数映射 ⟹ `(0,1)` 杯积非零**（第 5 步 (b) 的代数内核）。

见文件头：因果方向是把 `e` 用 `explicitCoeff1_explicitCup01` 推到杯积外面，
再用 `explicitCup01_mk` 逐余环读值。 -/
theorem explicitCup01_ne_zero_of_leftInverse
    {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [DistribMulAction G M] [ContinuousSMul G M]
    {N : Type} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
      [DistribMulAction G N] [ContinuousSMul G N]
    {P : Type} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
      [DistribMulAction G P] [ContinuousSMul G P]
    (μ : M →+ N →+ P) (hμ : Continuous fun q : M × N => μ q.1 q.2)
    (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)
    (m : H0 G M) (e : P →+[G] N) (he : Continuous e)
    (hleft : ∀ x : N, e (μ (m : M) x) = x)
    {y : H1 G N} (hy : y ≠ 0) :
    explicitCup01 G M N P μ hμ hequiv m y ≠ 0 := by
  intro h0
  -- 配对 `μ' m' x := e (μ m' x)`，输出系数取 `N`
  set μ' : M →+ N →+ N :=
    { toFun := fun m' => (e.toAddMonoidHom).comp (μ m')
      map_zero' := by simp
      map_add' := by intro a b; ext x; simp } with hμ'def
  have hμ' : Continuous fun q : M × N => μ' q.1 q.2 :=
    he.comp (hμ.comp (continuous_fst.prodMk continuous_snd))
  have hequiv' : ∀ (g : G) (m' : M) (x : N), μ' (g • m') (g • x) = g • μ' m' x := by
    intro g m' x
    change e ((μ (g • m')) (g • x)) = g • e ((μ m') x)
    rw [hequiv]
    exact map_smul e g _
  -- NSW (1.4.2)：把 `e` 推到杯积外面
  have hnat := explicitCoeff1_explicitCup01 (G := G) (M := M) (N := N) (P := P)
    (M' := M) (N' := N) (P' := N) (μ := μ) (hμ := hμ) (hequiv := hequiv)
    (μ' := μ') (hμ' := hμ') (hequiv' := hequiv')
    (fM := DistribMulActionHom.id G) (fN := DistribMulActionHom.id G) (fP := e)
    (hcN := continuous_id) (hcP := he)
    (hpair := fun m' x => rfl) m y
  -- `explicitCoeff0`／`explicitCoeff1` 在恒等系数映射上是恒等
  simp only [explicitCoeff0_id, explicitCoeff1_id, AddMonoidHom.id_apply] at hnat
  rw [h0, map_zero] at hnat
  -- 逐余环读右端：它就是 `y`
  have hkey : explicitCup01 G M N N μ' hμ' hequiv' m y = y := by
    induction y using QuotientAddGroup.induction_on with
    | H b =>
      rw [explicitCup01_mk]
      exact congrArg (fun z : Z1 G N => (z : H1 G N))
        (Subtype.ext (funext fun g => hleft ((b : G → N) g)))
  rw [hkey] at hnat
  exact hy hnat.symm

end L20261018
