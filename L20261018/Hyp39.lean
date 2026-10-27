import L20261018.Hyp2
/-!
# 3.4 收口：**完整五项正合列**在 `G_F` 上（第 1→5 段全部）

论文 `thm:hs-tate-exact-sequences` / `prop:hs-special` 的五项正合列是

```
0 → H¹(G/N, M^N) --infl₁--> H¹(G, M) --res--> H¹(N, M)^{G/N} --trans--> H²(G/N, M^N) --infl₂--> H²(G, M)
```

`A.prop_3_4_first_three` 只覆盖**前三项**（inflation 单射 ＋ 第 2 段正合），且是在**抽象群上同调**
（`Rep k G`、`groupCohomology.H1InfRes`）里；`Hyp2.galo_five_term` 覆盖**后两段**（第 3、4 段），
在真对象（`G_F`、`ZMod p`）上。两段此前从未拼在一起。

TauCeti 的四条引理（`Transgression.lean` 的 `## Main statements` 明言「together … this is
exactness at every node」）都在**同一个**显式模型（`explicitInfl1` / `explicitResConj1` /
`transgression` / `explicitInfl2`）里：

| 段 | 引理 |
|---|---|
| 1（`infl₁` 单射） | `TauCeti.ContCohomology.explicitInfl1_injective` |
| 2（`im infl₁ = ker res`） | `TauCeti.ContCohomology.explicitInfResConj_exact` |
| 3（`im res = ker trans`） | `TauCeti.ContCohomology.fiveTerm_exact_H1N`（= `Hyp2` 第一支） |
| 4（`im trans = ker infl₂`） | `TauCeti.ContCohomology.fiveTerm_exact_H2Q`（= `Hyp2` 第二支） |

本文件把它们拼成**一条**定理：五项正合列的**每一段**同时成立。这是论文 3.4 的完整内容，
且**无额外假设**（只有 `N` 正规闭 ＋ `M^N` 上 `G/N` 作用的连续性，后者是记号前提）。
-/

open TauCeti ContCohomology

namespace GaloFive

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime]

/-- **五项正合列，`G_F` 上、`μ_p` 系数、每一段同时成立。** 这是论文 3.4（`prop:hs-special`）
的完整陈述：`H¹(G/N, M^N) → H¹(G, M) → H¹(N, M)^{G/N} → H²(G/N, M^N) → H²(G, M)`。

四条正合性来自 TauCeti：前两段（inflation 单射、`im infl₁ = ker res`）与后两段
（`im res = ker trans`、`im trans = ker infl₂`）都在同一显式模型上，故可直接拼。 -/
-- @source file=raw/L20261018.tex locator=label:prop:hs-special quote="0\longrightarrow H^1(G,\mu_p)"
theorem prop_3_4_galo
    (N : Subgroup (AbsoluteGaloisGroup K)) [N.Normal]
    [ContinuousSMul ((AbsoluteGaloisGroup K) ⧸ N)
      ↥(FixedPoints.addSubgroup (↥N) (ZMod p))]
    (hN : IsClosed (N : Set (AbsoluteGaloisGroup K))) :
    Function.Injective (explicitInfl1 (AbsoluteGaloisGroup K) (ZMod p) N) ∧
      (explicitInfl1 (AbsoluteGaloisGroup K) (ZMod p) N).range
        = (explicitResConj1 (AbsoluteGaloisGroup K) (ZMod p) N).ker ∧
      (explicitResConj1 (AbsoluteGaloisGroup K) (ZMod p) N).range
        = (transgression (AbsoluteGaloisGroup K) (ZMod p) N hN).ker ∧
      (transgression (AbsoluteGaloisGroup K) (ZMod p) N hN).range
        = (explicitInfl2 (AbsoluteGaloisGroup K) (ZMod p) N).ker :=
  ⟨explicitInfl1_injective _ _ N,
   explicitInfResConj_exact _ _ N,
   fiveTerm_exact_H1N _ _ N hN,
   fiveTerm_exact_H2Q _ _ N hN⟩

end GaloFive
