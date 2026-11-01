import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Acyclic

/-!
# R1072（**(R2) 建造 H-5-1**）：短正合列中间项与左项零调 ⟹ 右项零调

这是 GS 6.8.5（`cons-residue-map-finite-coefficients`）的**关键中间步**：
把 `A` 嵌入余诱导模得 `0 → A → M^G(A) → C → 0`，由
`H^j(H, M^G(A)) = 0 (j≥1)` 与 `H^j(H, A) = 0 (j≥2)`（`cd(H) ≤ 1`）推出 **`H^j(H, C) = 0 (j≥1)`**。

GS 原文的论证：`H^j(H, M^G(A)) = 0` ⟹ 长正合列给 `H^j(H,C) ≅ H^{j+1}(H,A)`（`j≥1`），
而 `H^{j+1}(H,A) = 0`（`j+1 ≥ 2`，`cd(H)≤1`）⟹ `H^j(H,C) = 0`。

本文件给出**抽象形式**（不依赖余诱导模的具体构造）：对任意离散短正合列
`0 → A → B → C → 0`，若 `H^k(B) = 0 (k≥1)`、`H^k(A) = 0 (k≥2)`，则 `H^j(C) = 0 (j≥1)`。

| 声明 | 内容 |
|---|---|
| **`subsingleton_cohomology_three_of_acyclic`** | `H^k(B)=0 (k≥1) → H^k(A)=0 (k≥2) → H^j(C)=0 (j≥1)` |

**证明**（照 GS 6.8.5 的 LES 论证，用库内 `longExact_exact₃`）：
`delta j : H^j(C) → H^{j+1}(A)` 的靶零调 ⟹ `delta j = 0`；由正合性
`range (coeffMap proj j) = ker (delta j) = ⊤` ⟹ `coeffMap proj j` 满射；
源 `H^j(B)` 零调 ⟹ 使命题成立。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open TauCeti

namespace L20261018

section ThreeTerm

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
variable {B : Type} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  [ContinuousSMul G B]
variable {C : Type} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]

/-- **GS 6.8.5 的关键中间步**：中间项与左项在正次数上零调 ⟹ 右项零调。 -/
theorem subsingleton_cohomology_three_of_acyclic
    (S : ContCohomology.DiscreteShortExact G A B C)
    (hA : ∀ k, 2 ≤ k → Subsingleton (continuousCohomology k (ofDiscreteModule ℤ G A)))
    (hB : ∀ k, 1 ≤ k → Subsingleton (continuousCohomology k (ofDiscreteModule ℤ G B)))
    {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (continuousCohomology j (ofDiscreteModule ℤ G C)) := by
  classical
  haveI hAj : Subsingleton (continuousCohomology (j + 1) (ofDiscreteModule ℤ G A)) :=
    hA (j + 1) (by omega)
  haveI hBj : Subsingleton (continuousCohomology j (ofDiscreteModule ℤ G B)) := hB j hj
  -- `delta j` 的目标零调 ⟹ `delta j = 0`
  have hdelta : ⇑(CategoryTheory.ConcreteCategory.hom (S.delta j)) = fun _ => 0 := by
    funext x
    exact Subsingleton.elim _ _
  -- 由正合性得 `coeffMap proj j` 满射
  have hex := S.longExact_exact₃ j
  have hsurj : Function.Surjective
      ⇑(CategoryTheory.ConcreteCategory.hom
        (ContinuousCohomology.coeffMap (ofDiscreteModuleMap (R := ℤ) (G := G) S.proj.toIntLinearMap
          S.proj_equivariant) j)) := by
    intro y
    have h := hex y
    rw [hdelta] at h
    exact h.mp rfl
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, hb⟩ := hsurj y
  rw [Subsingleton.elim a b, hb]

/-- **H-5-1b**：特化到余诱导模 —— 中间项的零调性由库内
`subsingleton_continuousCohomology_discreteCoind_bot`（`Hⁿ⁺¹(G, Coind_1^G A) = 0`）供给。 -/
theorem subsingleton_cohomology_three_of_coind
    (S : ContCohomology.DiscreteShortExact G A (DiscreteCoind G ⊥ A) C)
    (hA : ∀ k, 2 ≤ k → Subsingleton (continuousCohomology k (ofDiscreteModule ℤ G A)))
    {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (continuousCohomology j (ofDiscreteModule ℤ G C)) := by
  refine subsingleton_cohomology_three_of_acyclic (A := A) S hA (fun k hk => ?_) hj
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  exact ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot ℤ G A m

end ThreeTerm

end L20261018

#print axioms L20261018.subsingleton_cohomology_three_of_acyclic
#print axioms L20261018.subsingleton_cohomology_three_of_coind
