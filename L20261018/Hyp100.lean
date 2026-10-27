import L20261018.Hyp99
import L20261018.Hyp5
/-!
# 3.6 组装（三）：`U` 的对齐（R926）

`A.theorem_3_6` 的商是 `V ⧸ (B.U + N)`（`Submodule` 的 `+`），而第一条 SES
（`Theo351.theorem_3_5_1_explicit`）的商是 `V ⧸ (span{(a₁),(a₂)}.toAddSubgroup ⊔ Ncor)`
（`AddSubgroup` 的 `⊔`）。本文件把两种写法接起来：

* `submodule_sup_toAddSubgroup`：`(p ⊔ q).toAddSubgroup = p.toAddSubgroup ⊔ q.toAddSubgroup`；
* `closure_toAddSubgroup`：`(span R ↑K).toAddSubgroup = K`（`K` 是加法子群）；
* `Nsub_toAddSubgroup`：`(Nsub Δ).toAddSubgroup = Ncor`；
* **`U_alignment`**：`(B.U ⊔ Nsub Δ).toAddSubgroup = span{(a₁),(a₂)}.toAddSubgroup ⊔ Ncor`。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Assemble36

variable {p : ℕ} [NeZero p] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- 子模的上确界与加法子群的上确界相容。 -/
theorem submodule_sup_toAddSubgroup (P Q : Submodule (ZMod p) V) :
    (P ⊔ Q).toAddSubgroup = P.toAddSubgroup ⊔ Q.toAddSubgroup := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_sup, AddSubgroup.mem_sup]

/-- 子模的 span（生成集是整个加法子群）的底层加法子群就是它自己。 -/
theorem closure_toAddSubgroup (K : AddSubgroup V) :
    (Submodule.span (ZMod p) (K : Set V)).toAddSubgroup = K := by
  ext x
  constructor
  · intro hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy; exact hy
    · exact K.zero_mem
    · intro a b _ _ ha hb; exact K.add_mem ha hb
    · intro c a _ ha
      rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
      exact K.nsmul_mem ha c.val
  · intro hx
    exact Submodule.subset_span hx

variable {F : Type} [Field F] {p' : ℕ} [Fact p'.Prime] [HasEnoughRootsOfUnity F p']

/-- **`Nsub Δ` 的底层加法子群是 `Ncor`**。 -/
theorem Nsub_toAddSubgroup (Δ : Subgroup Fˣ)
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p') Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p') Δ)] :
    (Theo352.Nsub (F := F) (p := p') Δ).toAddSubgroup
      = GaloFive.Ncor F p' (Theo352.Efield (F := F) (p := p') Δ) := by
  rw [Theo352.Nsub]
  exact closure_toAddSubgroup (p := p') _

/-- **`B.U` 的底层加法子群是 `span{(a₁),(a₂)}`**（`B.aᵢ` 就是 `kc aᵢ`，故 `rfl`）。 -/
theorem Bex_U_toAddSubgroup (hp : IsUnit (p' : F)) {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F) (GaloCup.kummerExplicit (F := F) (p := p') hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p') hp a2) ≠ 0) :
    ((Theo352.Bex (F := F) (p := p') hp hne).U).toAddSubgroup
      = (Submodule.span (ZMod p')
          ({GaloCup.kummerExplicit (F := F) (p := p') hp a1,
            GaloCup.kummerExplicit (F := F) (p := p') hp a2} :
            Set (H1 (AbsoluteGaloisGroup F) (ZMod p')))).toAddSubgroup :=
  rfl

/-- **`U` 对齐**：`A.theorem_3_6` 的 `B.U + N`（子模）与第一条 SES 的
`span{(a₁),(a₂)} ⊔ Ncor`（加法子群）**给出同一个商**。 -/
theorem U_alignment (hp : IsUnit (p' : F)) (hp2 : p' ≠ 2) (Δ : Subgroup Fˣ)
    [(powMonoidHom p' : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p') Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p') Δ)]
    {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F) (GaloCup.kummerExplicit (F := F) (p := p') hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p') hp a2) ≠ 0) :
    ((Theo352.Bex (F := F) (p := p') hp hne).U ⊔ Theo352.Nsub (F := F) (p := p') Δ).toAddSubgroup
      = (Submodule.span (ZMod p')
            ({GaloCup.kummerExplicit (F := F) (p := p') hp a1,
              GaloCup.kummerExplicit (F := F) (p := p') hp a2} :
              Set (H1 (AbsoluteGaloisGroup F) (ZMod p')))).toAddSubgroup
          ⊔ GaloFive.Ncor F p' (Theo352.Efield (F := F) (p := p') Δ) := by
  rw [submodule_sup_toAddSubgroup]
  rw [Bex_U_toAddSubgroup (p' := p') hp hne]
  rw [Nsub_toAddSubgroup (F := F) (p' := p') Δ]

end Assemble36

#print axioms Assemble36.submodule_sup_toAddSubgroup
#print axioms Assemble36.closure_toAddSubgroup
#print axioms Assemble36.Nsub_toAddSubgroup
#print axioms Assemble36.U_alignment
