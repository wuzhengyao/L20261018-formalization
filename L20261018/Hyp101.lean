import L20261018.Hyp100
import L20261018.Hyp92
/-!
# 3.6 组装（四）：`hNU` 独立成件（R927）

`A.theorem_3_6` 的前提 `hNU : N ⊆ U^⊥`。`Theo352.theorem_3_5_2_explicit` 里它是内嵌的
（`have hNU` ＋ `Submodule.span_le.mpr` ＋ `GaloCup.lemma_3_3_2_explicit`），本文件把它**独立成件**，
供最终组装直接引用。

## 主结果

* **`Nsub_le_Uperp`**：`Nsub Δ ≤ (Bex hp hne).Uperp`（`a₁,a₂ ∈ Δ` 时）。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Assemble36

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **`N = cor_{E/F}H¹(E,μ_p) ⊆ U^⊥`**（论文 3.3(2) 的投影公式 ＋ `res(aᵢ) = 0`）。

`⊆`：`Nsub` 是 `Ncor` 的张成，故只需对 `cor w` 验证；`GaloCup.lemma_3_3_2_explicit` 给出
`(cor w) ∪ (aᵢ) = 0` 两条，正是 `U^⊥` 的定义（`mem_Uperp_iff`）。 -/
theorem Nsub_le_Uperp (hp : IsUnit (p : F)) (hp2 : p ≠ 2) (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (hU : IsOpen ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
      : Set (AbsoluteGaloisGroup F)))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p) Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p) Δ)]
    {a1 a2 : Fˣ} (ha1 : a1 ∈ Δ) (ha2 : a2 ∈ Δ)
    (hne : Theo352.cupLin (F := F) (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    Theo352.Nsub (F := F) (p := p) Δ ≤ (Theo352.Bex (F := F) (p := p) hp hne).Uperp := by
  haveI h2 : NeZero (2 : ZMod p) := ⟨by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by simpa using h)
    have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    exact hp2 (le_antisymm hple hpge)⟩
  refine Submodule.span_le.mpr ?_
  intro x hx
  rw [SetLike.mem_coe] at hx
  obtain ⟨w, rfl⟩ := hx
  have hmain : Theo352.cupLin (F := F) (p := p) ((GaloFive.corN F p (Theo352.Efield Δ)) w)
        (GaloCup.kummerExplicit (F := F) (p := p) hp a1) = 0 ∧
      Theo352.cupLin (F := F) (p := p) ((GaloFive.corN F p (Theo352.Efield Δ)) w)
        (GaloCup.kummerExplicit (F := F) (p := p) hp a2) = 0 :=
    GaloCup.lemma_3_3_2_explicit (F := F) (p := p) hp Δ hroots ha1 ha2 hU w
  exact (Theo352.Bex (F := F) (p := p) hp hne).mem_Uperp_iff _ |>.mpr hmain

end Assemble36

#print axioms Assemble36.Nsub_le_Uperp
