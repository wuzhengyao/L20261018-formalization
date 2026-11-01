import L20261018.Infra.Cohomology.Boundary.Step002_coinduced_embedding

/-!
# R1075（**(R2) 建造 H-5-1d（上半）**）：商 `C := M^G(A) / A` 及其结构

GS 6.8.5 的短正合列 `0 → A → M^G(A) → C → 0`。本文件造出**商载体 `C` 及其结构**：

| 声明 | 内容 |
|---|---|
| **`coindSub`** | `coindIncl` 的像（加法子群） |
| **`coindSub_stable`** | 像在 `G`-作用下稳定（由 `coindIncl_equivariant`） |
| **`coindQuot`** | 商类型 `DiscreteCoind G ⊥ A ⧸ coindSub` |
| **实例** | `AddCommGroup`／`TopologicalSpace`（`⊥`）／`DiscreteTopology`／`SMul G`（**良定义性**由 `coindSub_stable` 给） |
| **`proj`** | 商映射 `M^G(A) →+ C`，`proj_apply`／`proj_surjective` |

**本轮追加**：**`proj_eq_zero_iff`（正中正合）**——`QuotientAddGroup.eq_zero_iff` 的 `AddSubgroup.Normal` 实例
**不能靠 TC 推断**（`N` 是元变量 ⟹ "instance problem is stuck"），须 `haveI` **＋** `(N := …)` **显式传参**。

**下一段（H-5-1d 下半）**：`DistribMulAction G C` 的四条（`one_smul`／`mul_smul`／`smul_zero`／`smul_add`
——商上的 `Quotient.map` 形式使 `rfl` 不成立，须逐步 `QuotientAddGroup.induction_on`）；
`proj` 的 `G`-等变；`DiscreteShortExact` 六项数据 ＋ 正中正合 `proj m = 0 ↔ m ∈ range incl`
（`QuotientAddGroup.eq_zero_iff` 的 `Normal` 实例须**显式**给出，不能靠 TC 推断 —— 见下）。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open TauCeti

namespace L20261018

section Quotient

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- `coindIncl` 的像（加法子群）。 -/
def coindSub : AddSubgroup (DiscreteCoind G ⊥ A) := (coindIncl (G := G) (A := A)).range

/-- **像在 `G`-作用下稳定**（GS 造商模的前提）。 -/
theorem coindSub_stable (g : G) {m : DiscreteCoind G ⊥ A} (hm : m ∈ coindSub (G := G) (A := A)) :
    g • m ∈ coindSub (G := G) (A := A) := by
  obtain ⟨a, rfl⟩ := hm
  exact ⟨g • a, coindIncl_equivariant g a⟩

/-- 商 `C := M^G(A) / A`。 -/
def coindQuot : Type := DiscreteCoind G ⊥ A ⧸ coindSub (G := G) (A := A)

namespace CoindQuot

instance : AddCommGroup (coindQuot (G := G) (A := A)) :=
  inferInstanceAs (AddCommGroup (DiscreteCoind G ⊥ A ⧸ coindSub (G := G) (A := A)))
instance : TopologicalSpace (coindQuot (G := G) (A := A)) := ⊥
instance : DiscreteTopology (coindQuot (G := G) (A := A)) := ⟨rfl⟩

/-- **商上的 `G`-作用**：良定义性正是 `coindSub_stable`。 -/
instance : SMul G (coindQuot (G := G) (A := A)) where
  smul g := Quotient.map (fun m => g • m) (by
    intro m₁ m₂ h
    refine QuotientAddGroup.leftRel_apply.mpr ?_
    have h' : -m₁ + m₂ ∈ coindSub (G := G) (A := A) := QuotientAddGroup.leftRel_apply.mp h
    have h'' := coindSub_stable (G := G) (A := A) g h'
    simpa [smul_add, smul_neg] using h'')

/-- 商映射 `M^G(A) → C`。 -/
def proj : DiscreteCoind G ⊥ A →+ coindQuot (G := G) (A := A) :=
  QuotientAddGroup.mk' (coindSub (G := G) (A := A))

@[simp]
theorem proj_apply (m : DiscreteCoind G ⊥ A) :
    proj (G := G) (A := A) m = Quotient.mk _ m := rfl

theorem proj_surjective : Function.Surjective (proj (G := G) (A := A)) :=
  QuotientAddGroup.mk'_surjective _

/-- **正中正合**：`proj m = 0 ↔ m ∈ range incl`（＝ `ker proj = im incl`）。

`QuotientAddGroup.eq_zero_iff` 需要 `AddSubgroup.Normal` 实例；**它不能靠 TC 推断**
（`N` 在那里是元变量，会报 "instance problem is stuck"）⟹ 须用 `haveI` **且** `(N := …)` **显式传参**。 -/
theorem proj_eq_zero_iff (m : DiscreteCoind G ⊥ A) :
    proj (G := G) (A := A) m = 0 ↔ m ∈ coindSub (G := G) (A := A) := by
  haveI : (coindSub (G := G) (A := A)).Normal := ⟨fun n hn g => by simpa using hn⟩
  rw [proj_apply]
  exact QuotientAddGroup.eq_zero_iff (N := coindSub (G := G) (A := A)) m

end CoindQuot

end Quotient

end L20261018

#print axioms L20261018.coindSub_stable
#print axioms L20261018.CoindQuot.proj_surjective
#print axioms L20261018.CoindQuot.proj_eq_zero_iff
