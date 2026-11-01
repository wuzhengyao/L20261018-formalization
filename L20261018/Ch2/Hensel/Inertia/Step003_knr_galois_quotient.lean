import L20261018.Infra.Cohomology.Step004_q_discrete_h1_acyclic

/-!
# R1292（S37 · GS §6.8 战役 **S1**）：`K_nr` 的伽罗瓦性与 `Gal(K_nr/K)` 的商描述

`GS68-CAMPAIGN.md` §1 的 S1 三件（S1a／S1b／S1c）。原文 = `raw/GilleSzamuely2017.tex`
（GS 2017, §6.8.1，label `sec:cohomology-complete-dv`）：

> The extension $K_{nr}|K$ is Galois, and the Galois group
> $G:=\operatorname{Gal}(K_{nr}|K)$ is canonically isomorphic to
> $\operatorname{Gal}(\kappa_{s}|\kappa)$.

本轮把「`K_nr` 是伽罗瓦的」与「`Gal(K_nr/K)` 是 `D ⧸ I`」机检成**条件定理**，
**唯一假设**是 `I*` 在 Krull 拓扑下**闭**（`IsClosed`）—— 其数学理由见文件末「诚实口径」。

| 声明 | 内容 | 引用件 |
|---|---|---|
| **`inertiaAbs_normal_of_decomp_eq_top`** | `D = ⊤ ⟹ I* ◁ G`（Hensel 情形的正规性） | — |
| **`isGalois_Knr`** | ★★★★ `I* ◁ G ⟹ IsGalois K (K_nr)`（**S1a**） | `GS 6.8.1` |
| **`fixingSubgroup_Knr`** | ★★★★★ `I*` 闭 `⟹ (K_nr).fixingSubgroup = I*`（**S1b**） | — |
| **`galoisGroupKnrQuotient`** | ★★★★★ `G ⧸ I* ≃* Gal(K_nr/K)`（**S1c**，无限伽罗瓦理论） | — |
| **`galoisGroupKnrEquivRange`** | ★★★★★ `D = ⊤ ⟹ Gal(K_nr/K) ≃* range(D →* Aut κ_A)` | — |
| `inertiaAbs_le_decompositionSubgroup` | `I* ≤ D` | — |
| `witness_*`（`section Witness`） | 假设类**非空**：`[IsSepClosed K]` 时三假设全成立 | — |

## 与 `GS68-CAMPAIGN.md` §1 的对应

* S1a = `isGalois_Knr`；
* S1b = `fixingSubgroup_Knr`；
* S1c = `galoisGroupKnrQuotient`（＋ `galoisGroupKnrEquivRange` 把 `Hyp374.decompQuotEquivRange`
  拼上，即 GS 的 `Gal(K_nr|K) ↔ Gal(κ_A|κ)` 的**单射半边**）。

## 诚实口径（S1 的剩余缺口）

GS 的定义路线是：`K_nr` := 全部**有限不分歧扩张的复合**（自动伽罗瓦），然后**证明**
`Gal(K_s/K_nr) = I`。本战役（`Hyp375`）走的是**对偶**路线：`K_nr := fixedField I*`，
于是 `fixingSubgroup K_nr = I*` 等价于 `I*` **闭**（`InfiniteGalois.fixingSubgroup_fixedField`
的假设）。两条路线的差距是同一件数学：**惯性子群在 Krull 拓扑下闭**。

* 数学上该闭性来自「`Gal(K_s/K) → Aut(κ_A)` 连续且 `κ_A` 离散」⟹ `I` 是连续同态的核；
  但 mathlib 的 `IsLocalRing.ResidueField A` **没有拓扑**，`RingAut κ_A` 也不是拓扑群
  ⟹ 该连续性在库内**无法陈述**（不是"缺一个引理"，是缺一层载体）。
* GS 真正用的是 `κ_A = κ_s` ＋「`K_nr|K` 伽罗瓦」，这需要**剩余域理论**（Teichmüller 提升／
  Hensel 唯一延拓），正是 S2 的同一层基建。
* ⟹ 本轮按 `PROMPT-S37` §④ 的降级路径：闭性作**具名假设**传下去，
  并给出**非空见证**（`section Witness`：`G` 平凡时三假设全成立）。

⟹ **S1 的剩余 = 一条**：`IsClosed (inertiaAbs A)`（＝ `I* = closure I*`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

variable {K : Type*} [Field K]

/-! ### `I*` 与 `D` 的相对位置 -/

/-- `I* ≤ D`（`I*` 是 `I ≤ D` 经 `D.subtype` 的像）。 -/
theorem inertiaAbs_le_decompositionSubgroup (A : ValuationSubring (SeparableClosure K)) :
    inertiaAbs (K := K) A ≤ A.decompositionSubgroup K := by
  rintro g ⟨x, -, rfl⟩
  exact x.2

/-! ### S1a：`K_nr` 在 `K` 上伽罗瓦 -/

/-- **Hensel 情形的正规性**：若分解子群是整个伽罗瓦群（`D = ⊤`，赋值延拓唯一 ⟹
每个 `σ` 都保持 `A`），则惯性子群的像是正规子群。

（`GS` 的设定里 `v` 唯一延拓到 `K_nr`，故 `K_nr|K` 伽罗瓦 —— 这里把唯一延拓的**推论**
`D = ⊤` 显式作前提。） -/
theorem inertiaAbs_normal_of_decomp_eq_top (A : ValuationSubring (SeparableClosure K))
    (hD : A.decompositionSubgroup K = ⊤) : (inertiaAbs (K := K) A).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hn
  -- `g` 作为 `D` 的元素（`D = ⊤`）
  let d : ↥(A.decompositionSubgroup K) :=
    ⟨g, by rw [hD]; exact Subgroup.mem_top g⟩
  have hd : (d : TauCeti.AbsoluteGaloisGroup K) = g := rfl
  exact ⟨d * x * d⁻¹, (inferInstance : (A.inertiaSubgroup K).Normal).conj_mem x hx d, by
    simp [hd]⟩

/-- **S1a**：`I* ◁ G ⟹ `K_nr` 在 `K` 上伽罗瓦。

数学来源：`IsGalois.of_fixedField_normal_subgroup`（mathlib 的无限伽罗瓦理论：
正规子群的固定域是伽罗瓦的）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=label:sec:cohomology-complete-dv quote="The extension $K_{nr}|K$ is Galois, and the Galois group $G:=\operatorname{Gal}(K_{nr}|K)$ is canonically isomorphic to $\operatorname{Gal}(\kappa_{s}|\kappa)$."
theorem isGalois_Knr (A : ValuationSubring (SeparableClosure K))
    (hN : (inertiaAbs (K := K) A).Normal) : IsGalois K (Knr (K := K) A) :=
  IsGalois.of_fixedField_normal_subgroup (inertiaAbs (K := K) A)

/-- Hen **Hensel 情形**的 `IsGalois`（把 S1a 与正规性合成）。 -/
theorem isGalois_Knr_of_decomp_eq_top (A : ValuationSubring (SeparableClosure K))
    (hD : A.decompositionSubgroup K = ⊤) : IsGalois K (Knr (K := K) A) :=
  isGalois_Knr A (inertiaAbs_normal_of_decomp_eq_top A hD)

/-! ### S1b：`K_nr` 的固定子群恰是 `I*` -/

/-- **S1b**：`I*` 在 Krull 拓扑下闭 ⟹ `Gal(K_s/K_nr) = I*`。

数学来源：`InfiniteGalois.fixingSubgroup_fixedField`（闭子群与其固定域在无限伽罗瓦
对应下互逆）。**这是 `K_nr := fixedField I*` 这条定义路线的唯一额外输入。** -/
theorem fixingSubgroup_Knr (A : ValuationSubring (SeparableClosure K))
    (hI : IsClosed ((inertiaAbs (K := K) A : Subgroup (TauCeti.AbsoluteGaloisGroup K)) :
      Set (TauCeti.AbsoluteGaloisGroup K))) :
    (Knr (K := K) A).fixingSubgroup = inertiaAbs (K := K) A :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨inertiaAbs (K := K) A, hI⟩

/-- `K_nr` 的定义层展开（`fixedField I*`）。 -/
theorem Knr_eq_fixedField (A : ValuationSubring (SeparableClosure K)) :
    Knr (K := K) A = IntermediateField.fixedField (inertiaAbs (K := K) A) := rfl

/-! ### S1c：`Gal(K_nr/K) ≅ G ⧸ I*` -/

/-- **S1c**：`Gal(K_nr/K) ≅ Gal(K_s/K) ⧸ I*`。

数学来源：`InfiniteGalois.normalAutEquivQuotient`（闭**正规**子群 ⟹ 商 ↔ 固定域的
伽罗瓦群）。 -/
noncomputable def galoisGroupKnrQuotient (A : ValuationSubring (SeparableClosure K))
    (hI : IsClosed ((inertiaAbs (K := K) A : Subgroup (TauCeti.AbsoluteGaloisGroup K)) :
      Set (TauCeti.AbsoluteGaloisGroup K)))
    (hN : (inertiaAbs (K := K) A).Normal) :
    TauCeti.AbsoluteGaloisGroup K ⧸ inertiaAbs (K := K) A ≃* Gal(↥(Knr (K := K) A)/K) :=
  InfiniteGalois.normalAutEquivQuotient ⟨inertiaAbs (K := K) A, hI⟩

/-- ★★★★★ **S1 的合成形态**：`Gal(K_nr/K) ≅ D ⧸ I ≅ range(D →* Aut κ_A)`。

由 `galoisGroupKnrQuotient`（无限的伽罗瓦对应）＋ `QuotientGroup.congr`（`D = ⊤` 时
`G ⧸ I* ≅ D ⧸ I`）＋ `Hyp374.decompQuotEquivRange`（`D ⧸ I ≅ range`）三段拼成。
`D = ⊤` 是 Hensel（赋值延拓唯一）的推论，见 `inertiaAbs_normal_of_decomp_eq_top`。

对照 GS：GS 说 `Gal(K_nr|K) ≅ Gal(κ_s|κ)`；这里机检的是它的**单射半边**
（`Gal(K_nr/K)` 落到 `Aut κ_A` 的**像**）。满射半边（`κ_A = κ_s`）需要剩余域理论 = S2 层。 -/
noncomputable def galoisGroupKnrEquivRange (A : ValuationSubring (SeparableClosure K))
    (hI : IsClosed ((inertiaAbs (K := K) A : Subgroup (TauCeti.AbsoluteGaloisGroup K)) :
      Set (TauCeti.AbsoluteGaloisGroup K)))
    (hN : (inertiaAbs (K := K) A).Normal)
    (hD : A.decompositionSubgroup K = ⊤) :
    Gal(↥(Knr (K := K) A)/K) ≃* (decompToResidue (K := K) A).range := by
  -- `D = ⊤` 把 `↥D` 与 `G` 等同
  let e : ↥(A.decompositionSubgroup K) ≃* TauCeti.AbsoluteGaloisGroup K :=
    (MulEquiv.subgroupCongr hD).trans Subgroup.topEquiv
  have hkey : ∀ x : ↥(A.decompositionSubgroup K),
      (e x : TauCeti.AbsoluteGaloisGroup K) = x.1 := fun _ => rfl
  have hmap : Subgroup.map (e : ↥(A.decompositionSubgroup K) →* TauCeti.AbsoluteGaloisGroup K)
      (A.inertiaSubgroup K) = inertiaAbs (K := K) A := by
    ext g
    simp only [Subgroup.mem_map, inertiaAbs, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hkey x).symm⟩
    · rintro ⟨x, hx, hg⟩
      exact ⟨x, hx, (hkey x).trans hg⟩
  exact (InfiniteGalois.normalAutEquivQuotient ⟨inertiaAbs (K := K) A, hI⟩).symm |>.trans
    ((QuotientGroup.congr (A.inertiaSubgroup K) (inertiaAbs (K := K) A) e hmap).symm |>.trans
      (decompQuotEquivRange (K := K) A))

/-! ### 非空见证（L1 ＋ L10① 的机检义务）

假设类 `{A // IsClosed I* ∧ I* ◁ G ∧ D = ⊤}` **非空**：取 `G` 平凡（`K` 可分闭，例如
`K` 为代数闭域）时，任意 `A` 都满足三条。这是**退化的**见证（结论随之平凡），
它只履行「假设类非空」的义务；**实质性的**见证（Hensel 局部域，`D = ⊤` 而 `G` 非平凡）
需要剩余域理论，正是 S2 的同一层基建。 -/

section Witness

variable [IsSepClosed K]

/-- `K` 可分闭 ⟹ `G` 平凡 ⟹ 任意子群都闭。 -/
theorem witness_isClosed (A : ValuationSubring (SeparableClosure K)) :
    IsClosed ((inertiaAbs (K := K) A : Subgroup (TauCeti.AbsoluteGaloisGroup K)) :
      Set (TauCeti.AbsoluteGaloisGroup K)) := by
  rw [show ((inertiaAbs (K := K) A : Subgroup (TauCeti.AbsoluteGaloisGroup K)) :
      Set (TauCeti.AbsoluteGaloisGroup K)) = Set.univ from
    Set.eq_univ_of_forall (fun x => by
      rw [Subsingleton.elim x 1]; exact (inertiaAbs (K := K) A).one_mem)]
  exact isClosed_univ

/-- `K` 可分闭 ⟹ 任意子群都正规。 -/
theorem witness_normal (A : ValuationSubring (SeparableClosure K)) :
    (inertiaAbs (K := K) A).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rwa [Subsingleton.elim (g * n * g⁻¹) n]

/-- `K` 可分闭 ⟹ 分解子群是全体。 -/
theorem witness_decomp_eq_top (A : ValuationSubring (SeparableClosure K)) :
    A.decompositionSubgroup K = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Subsingleton.elim x 1]
  exact (A.decompositionSubgroup K).one_mem

/-- **假设类非空**：三假设同时成立。 -/
theorem witness_hypotheses (A : ValuationSubring (SeparableClosure K)) :
    IsClosed ((inertiaAbs (K := K) A : Subgroup (TauCeti.AbsoluteGaloisGroup K)) :
      Set (TauCeti.AbsoluteGaloisGroup K)) ∧
    (inertiaAbs (K := K) A).Normal ∧ A.decompositionSubgroup K = ⊤ :=
  ⟨witness_isClosed A, witness_normal A, witness_decomp_eq_top A⟩

end Witness

end L20261018

#print axioms L20261018.inertiaAbs_le_decompositionSubgroup
#print axioms L20261018.inertiaAbs_normal_of_decomp_eq_top
#print axioms L20261018.isGalois_Knr
#print axioms L20261018.isGalois_Knr_of_decomp_eq_top
#print axioms L20261018.fixingSubgroup_Knr
#print axioms L20261018.galoisGroupKnrEquivRange
#print axioms L20261018.witness_hypotheses
