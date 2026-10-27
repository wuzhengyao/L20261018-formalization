import L20261018.Hyp104
import L20261018.Hyp13
import L20261018.Hyp93
import L20261018.Hyp100
/-!
# 3.6 组装（八）：第一条 SES 直接建在论文的 `U = span{(a₁),(a₂)}` 上（R932）

**R931 的教训**："先建后搬"是错序——在 `span` 上建 SES 再搬到 `B.U` 会撞上 `AddMonoidHom`
的结构路径。**正解**：`A.three_five_one_add` 只需 `hker : (resMG).ker = U`，
而 `mem_ker_resMG_iff`（R915）**正是** `(resMG).ker = span{(a₁),(a₂)} = B.U`。

于是第一条 SES 的域**从一开始**就是 `(B.U ⊔ Nsub).toAddSubgroup`，与 `A.theorem_3_6` 的
`V ⧸ (B.U + N)` **defeq**（R923 已核实子模商 ≡ 加法子群商）——**零搬运**。

## 主结果

* **`three_five_one_Bex`**：`0 → V/(U+N) → M^G/N_G(M) → K₂ → 0`，`U = B.U`。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Assemble36

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **第一条 SES，`U` 取论文的 `U = span{(a₁),(a₂)}`**（零搬运版）。 -/
theorem three_five_one_Bex (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex
      (Subgroup.closure ({a1, a2} : Set Fˣ))]
    (hroots : ∀ b ∈ Subgroup.closure ({a1, a2} : Set Fˣ),
      ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p)
      (Subgroup.closure ({a1, a2} : Set Fˣ)))]
    [IsGalois F (Theo352.Efield (F := F) (p := p)
      (Subgroup.closure ({a1, a2} : Set Fˣ)))]
    (hne : Theo352.cupLin (F := F) (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    ∃ (φ : (H1 (AbsoluteGaloisGroup F) (ZMod p) ⧸
          (((Theo352.Bex (F := F) (p := p) hp hne).U).toAddSubgroup ⊔
            ((Theo352.Nsub (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ))).toAddSubgroup)))
        →+ (↥(GaloFive.MG F p (Theo352.Efield (F := F) (p := p)
              (Subgroup.closure ({a1, a2} : Set Fˣ)))) ⧸
            GaloFive.NG F p (Theo352.Efield (F := F) (p := p)
              (Subgroup.closure ({a1, a2} : Set Fˣ)))))
      (ψ : (↥(GaloFive.MG F p (Theo352.Efield (F := F) (p := p)
              (Subgroup.closure ({a1, a2} : Set Fˣ)))) ⧸
            GaloFive.NG F p (Theo352.Efield (F := F) (p := p)
              (Subgroup.closure ({a1, a2} : Set Fˣ)))) →+
          ↥(GaloFive.K2 F p (Theo352.Efield (F := F) (p := p)
              (Subgroup.closure ({a1, a2} : Set Fˣ))))),
      Function.Injective φ ∧ Function.Surjective ψ ∧ φ.range = ψ.ker := by
  set E := Theo352.Efield (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ))
  have hker : (GaloFive.resMG F p E).ker
      = ((Theo352.Bex (F := F) (p := p) hp hne).U).toAddSubgroup := by
    ext x
    rw [Submodule.mem_toAddSubgroup]
    exact Theo351.mem_ker_resMG_iff (F := F) (p := p) hp a1 a2 hroots x
  have hNG : GaloFive.NG F p E
      = ((Theo352.Nsub (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ))).toAddSubgroup).map
          (GaloFive.resMG F p E) := by
    rw [Nsub_toAddSubgroup (F := F) (p' := p) (Subgroup.closure ({a1, a2} : Set Fˣ))]
    rfl
  exact L20261018.three_five_one_add ((Theo352.Bex (F := F) (p := p) hp hne).U).toAddSubgroup
    ((Theo352.Nsub (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ))).toAddSubgroup)
    (GaloFive.MG F p E) (GaloFive.resMG F p E) hker
    (GaloFive.NG F p E) hNG (GaloFive.d2' F p E) (GaloFive.d2'_ker F p E)
    (GaloFive.d2'_range F p E)

end Assemble36


