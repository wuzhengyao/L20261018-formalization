import L20261018.Hyp94
import L20261018.Hyp13
/-!
# 3.6 的有限性（二）：`H0 = Ĥ⁰(G,M) = M^G/N_G(M)` 有限（R918）

论文 `thm:dimension` 的 `τ = dim Ĥ⁰(G,M)` 有限。`MG ⊆ H¹(↥N₀, μ_p)` 而 `↥N₀` **无限**，
故不能靠 `Finite` 直接数；论文的论证是**第一条 SES**：
`0 → V/(U+N) → Ĥ⁰ → K₂ → 0`，两端有限（`V` 由 `d_F < ∞`、`K₂` 由 R917）⟹ 中间有限。

本文件把它做成一条**纯群论引理 ＋ 实例化**：

* `finite_of_addHom_surjective`：`ψ : A →+ B` 满、`B` 有限、`ker ψ` 有限 ⟹ `A` 有限
  （不需要 SES 拆分：取 `ψ` 的**集合论**截面 `s`（`Classical.choice`），
  `x ↦ (x - s(ψ x), ψ x)` 是到 `ker ψ × B` 的单射）；
* **`finite_H0`**：真实对象上的 `Ĥ⁰` 有限。

**已知缺口（下一轮）**：`↥(MG) ⧸ NG` 目前**没有** `Module (ZMod p)` 实例（`MG` 是 `AddSubgroup`
而非 `Submodule`）⟹ `Module.Finite` 那一版（`A.theorem_3_6` 的 `[Module.Finite k H0]`）需要先把
`MG` 升成 `Submodule`（`ZMod p` 是域，加法子群自动是子模，用 `Nsub_coe` 同款构造）。

## 主结果

* `Finiteness36.finite_of_addHom_surjective`
* **`Finiteness36.finite_H0`**
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Finiteness36

/-- **中间项有限**：`ψ : A →+ B` 满、`B` 与 `ker ψ` 都有限 ⟹ `A` 有限。

不需要线性（也不需要 SES 拆分）：取集合论截面 `s : B → A`，`x ↦ (x - s (ψ x), ψ x)`
是 `A ↪ ker ψ × B`。 -/
theorem finite_of_addHom_surjective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (ψ : A →+ B) (hψ : Function.Surjective ψ) [Finite B] [Finite ψ.ker] : Finite A := by
  classical
  choose s hs using hψ
  have hmem : ∀ x : A, x - s (ψ x) ∈ ψ.ker := by
    intro x
    rw [AddMonoidHom.mem_ker, map_sub, hs, sub_self]
  refine Finite.of_injective (f := fun x : A => ((⟨x - s (ψ x), hmem x⟩ : ψ.ker), ψ x)) ?_
  intro x y hxy
  have h1 : ψ x = ψ y := congrArg (fun p : ψ.ker × B => p.2) hxy
  have h2 : (⟨x - s (ψ x), hmem x⟩ : ψ.ker) = ⟨y - s (ψ y), hmem y⟩ :=
    congrArg (fun p : ψ.ker × B => p.1) hxy
  have h3 : x - s (ψ x) = y - s (ψ y) := congrArg Subtype.val h2
  rw [h1] at h3
  calc x = (x - s (ψ y)) + s (ψ y) := (sub_add_cancel _ _).symm
    _ = (y - s (ψ y)) + s (ψ y) := by rw [h3]
    _ = y := sub_add_cancel _ _

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

/-- **`Ĥ⁰(G,M) = M^G/N_G(M)` 有限**（真实对象）。

来自 `GaloFive.theorem_3_5_1_galo` 的第一条 SES：`ker ψ = range φ ≅ V/(ker res + N)` 有限
（`V` 有限，论文的 `d_F < ∞`），`K₂` 有限（`Hyp94`），再用 `finite_of_addHom_surjective`。 -/
theorem finite_H0 (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    [IsGalois K E] [Finite (H1 (AbsoluteGaloisGroup K) (ZMod p))] :
    Finite (↥(GaloFive.MG K p E) ⧸ GaloFive.NG K p E) := by
  haveI := fixingSubgroup_finiteIndex (K := K) E
  obtain ⟨φ, ψ, hφ, hψ, hex⟩ := GaloFive.theorem_3_5_1_galo (K := K) (p := p) E
  -- 第一项有限（`V` 的商）
  haveI hfin1 : Finite (H1 (AbsoluteGaloisGroup K) (ZMod p) ⧸
      ((GaloFive.resMG K p E).ker ⊔ GaloFive.Ncor K p E)) :=
    Quotient.finite _
  -- `ker ψ = range φ` 有限
  haveI hfin2 : Finite ψ.ker := by
    rw [← hex]
    have hsurj : Function.Surjective
        (fun x : H1 (AbsoluteGaloisGroup K) (ZMod p) ⧸
            ((GaloFive.resMG K p E).ker ⊔ GaloFive.Ncor K p E) => (⟨φ x, ⟨x, rfl⟩⟩ : ↥φ.range)) := by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
    exact Finite.of_surjective _ hsurj
  -- `K₂` 有限
  haveI hfin3 : Finite ↥(GaloFive.K2 K p E) := finite_K2 (K := K) (p := p) E
  haveI hfin4 : Finite (↥(GaloFive.MG K p E) ⧸ GaloFive.NG K p E) :=
    finite_of_addHom_surjective (A := ↥(GaloFive.MG K p E) ⧸ GaloFive.NG K p E)
      (B := ↥(GaloFive.K2 K p E)) ψ hψ
  exact hfin4

end Finiteness36

#print axioms Finiteness36.finite_of_addHom_surjective
#print axioms Finiteness36.finite_H0
