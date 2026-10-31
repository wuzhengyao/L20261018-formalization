import Hyp151

/-!
# R1000：**过渡段第三句 —— `U` 的基选取**（论文 `:1596`）

论文 4.1/4.2 之间：「可选取 `U` 的基 `\gamma_1,\gamma_2`，使 `\bar v(\gamma_1)=1`、`\bar v(\gamma_2)=0`」
（`raw/L20261018.tex:1596`）。`Hyp150` 给了核的一维性，本文件把"一个值 1 的元素 ＋ 核的非零元"
拼成**基**（含线性无关与张成）。

**论文用途**：4.2 的证明就是在这个基下把 `x` 写成 `x=(w)+k(\pi)` 再做两次 `\partial_2` 计算
（该计算已在 `Hyp151.orth_eq_bot_paper_route` 逐步机检，用的正是值 1 与值 0 的两个元素）。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

attribute [local instance] TopRep.distribMulAction

/-- `Set.range ![a, b] = {a, b}`（两元素族的像）。 -/
theorem range_pair_eq (a b : GaloBase.V F p) :
    (Set.range ![a, b] : Set (GaloBase.V F p)) = {a, b} := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- **论文 `:1596`：`U` 的基可取成 `\bar v` 上的 `(1,0)`**。

存在 `\gamma_1,\gamma_2\in U=\Span\{(a_1),(a_2)\}`：`\bar v(\gamma_1)=1`、`\bar v(\gamma_2)=0`、
`\gamma_2\ne0`，且 `\Span\{\gamma_1,\gamma_2\}=U`（即它们构成 `U` 的基）。 -/
-- @source file=raw/L20261018.tex locator=line:1596 quote="可选取 $U$ 的基 $\gamma_1,\gamma_2$，使 $\bar v(\gamma_1)=1$、$\bar v(\gamma_2)=0$。"
theorem exists_basis_val_eq (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    {x y : GaloBase.V F p} (hne : GaloBase.cup (K := F) (p := p) x y ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) x y, valLin F p hp u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    ∃ γ₁ γ₂ : GaloBase.V F p, γ₁ ∈ ResidueCupData.plane (k := ZMod p) x y ∧
      γ₂ ∈ ResidueCupData.plane (k := ZMod p) x y ∧
      valLin F p hp γ₁ = 1 ∧ valLin F p hp γ₂ = 0 ∧ γ₂ ≠ 0 ∧
      ResidueCupData.plane (k := ZMod p) x y
        = Submodule.span (ZMod p) ({γ₁, γ₂} : Set (GaloBase.V F p)) := by
  classical
  -- ① 值 1 的元素
  obtain ⟨u, hu, hvu⟩ := hval
  set κ : GaloBase.V F p := (valLin F p hp u)⁻¹ • u with hκdef
  have hκU : κ ∈ ResidueCupData.plane (k := ZMod p) x y := Submodule.smul_mem _ _ hu
  have hκval : valLin F p hp κ = 1 := by
    rw [hκdef, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hvu
  -- ② 核的非零元（值 0）
  have hfin := finrank_ker_restrict_plane_eq_one_general (F := F) (p := p) (x := x) (y := y)
    (val := valLin F p hp) (hval := ⟨u, hu, hvu⟩) hp2 hne
  have hpos : 0 < Module.finrank (ZMod p) ↥(LinearMap.ker
      ((valLin F p hp).comp (ResidueCupData.plane (k := ZMod p) x y).subtype)) := by omega
  haveI : Nontrivial ↥(LinearMap.ker
      ((valLin F p hp).comp (ResidueCupData.plane (k := ZMod p) x y).subtype)) :=
    Module.nontrivial_of_finrank_pos hpos
  obtain ⟨γc, hγc⟩ := exists_ne (0 : ↥(LinearMap.ker
    ((valLin F p hp).comp (ResidueCupData.plane (k := ZMod p) x y).subtype)))
  set γp : ↥(ResidueCupData.plane (k := ZMod p) x y) :=
    (γc : ↥(ResidueCupData.plane (k := ZMod p) x y)) with hγp
  have hγU : (γp : GaloBase.V F p) ∈ ResidueCupData.plane (k := ZMod p) x y := γp.2
  have hγval : valLin F p hp (γp : GaloBase.V F p) = 0 := LinearMap.mem_ker.mp γc.2
  have hγne : (γp : GaloBase.V F p) ≠ 0 := by
    intro h0
    apply hγc
    exact Subtype.ext (Subtype.ext h0)
  -- ③ 线性无关
  have hli : LinearIndependent (ZMod p) ![κ, (γp : GaloBase.V F p)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := congrArg (valLin F p hp) hst
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hκval, hγval, smul_zero, smul_eq_mul, mul_one, mul_zero, add_zero, map_zero] at h
    refine ⟨h, ?_⟩
    have ht : t • (γp : GaloBase.V F p) = 0 := by
      rw [h, zero_smul, zero_add] at hst
      exact hst
    rcases smul_eq_zero.mp ht with h' | h'
    · exact h'
    · exact absurd h' hγne
  -- ④ 张成
  refine ⟨κ, (γp : GaloBase.V F p), hκU, hγU, hκval, hγval, hγne, ?_⟩
  have hspan_le : Submodule.span (ZMod p) ({κ, (γp : GaloBase.V F p)} : Set _)
      ≤ ResidueCupData.plane (k := ZMod p) x y := by
    rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact hκU
    · exact hγU
  have hset : ({κ, (γp : GaloBase.V F p)} : Set (GaloBase.V F p))
      = Set.range ![κ, (γp : GaloBase.V F p)] := (range_pair_eq (F := F) (p := p) κ _).symm
  have hspan_fr : Module.finrank (ZMod p)
      ↥(Submodule.span (ZMod p) ({κ, (γp : GaloBase.V F p)} : Set _)) = 2 := by
    rw [hset, finrank_span_eq_card hli]
    simp
  have hplane_fr : Module.finrank (ZMod p)
      ↥(ResidueCupData.plane (k := ZMod p) x y) = 2 :=
    finrank_plane_eq_two (F := F) (p := p) hp2 hne
  exact (Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [hspan_fr, hplane_fr])).symm

end L20261018
#print axioms L20261018.range_pair_eq
#print axioms L20261018.exists_basis_val_eq
