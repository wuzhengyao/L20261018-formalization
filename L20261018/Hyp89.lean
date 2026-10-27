import L20261018.Hyp87
import L20261018.Hyp88
/-!
# ζ-无关性 (a)：载体链在两个本原根下只差整数纯量（R911）

`indOfH2_independent`（`Hyp82.indOfH2` 对 ζ 的选取无关）分两块：

* **(a) 载体块**：两个本原 `p` 次单位根给出同一个 `H²(G_K, μ_p)`，但接到 `Br K` 的载体链
  （`H2Bridge.redEquiv`）经 `muNRepEquivTrivialFp` 用了 ζ 的选取，故两条链只差一个纯量；
* **(b) 指数块**：`index` 在单位纯量乘法下不变（`Hyp91`）。

本文件做 (a)，**全程在 `ZMod p`-模层**（`Br K` 没有 `ZMod p`-模结构，只有 `ℕ`-纯量，
见 R908 登记；纯量律在模层免费）：

1. `unitRoot`／`exists_pow_eq`：两个本原根都是**同一个**根（在可分闭包里）的幂，
   `ζ' = ζ ^ n` 且 `(n : ZMod p) ≠ 0`；
2. `muNRepEquivTrivialFp_eq_smul`：`Hyp87` 的纯量关系（`zmodEquivRootsOfUnity.symm` 差 `n⁻¹`）
   推过 `kummerCoeffEquivMuNRep`／`trivialFpEquiv`（两者都是加性等价）；
3. `muNRepIsoTrivialFp_hom_eq_smul`：系数同构的**态射层**只差 `n⁻¹`（`TopRep.hom_ext`）；
4. `muNRepCohomologyEquivTrivialFp_apply_eq_smul`：上同调层只差 `n⁻¹`
   （`coeffMap` 对系数态射线性，`ContinuousCohomology.map_smul`）；
5. `redEquiv_eq_smul`：**整条载体链** `redEquiv hζ' = n • redEquiv hζ`（取逆的纯量律
   `addEquiv_symm_eq_smul`）；
6. `brOfH2_eq_nsmul`：**`Br K` 层** `brOfH2 hζ' x = n • brOfH2 hζ x`（`Nat.cast_smul_eq_nsmul`
   ＋ `map_nsmul`）。

## 主结果

* **`ZetaIndependence.brOfH2_eq_nsmul`**：`brOfH2 hζ' x = n • brOfH2 hζ x`（`n` 是 `ζ' = ζ ^ n`）。
* `natCoprime_of_zmod_ne_zero`：`n` 与 `p` 互素（(b) 块的前提）。
-/

open TauCeti

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ZetaIndependence

open H2Bridge

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

/-! ### 纯量推过加性等价（`ZMod p`-模层） -/

section GenericZMod

variable (p : ℕ) [Fact p.Prime]

/-- **加性等价尊重 `ZMod p`-纯量**（`AddEquiv` 只有 `ℕ`-纯量，故两侧都化到 `nsmul`）。 -/
theorem addEquiv_map_zmod_smul {M N : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] (e : M ≃+ N) (c : ZMod p) (y : M) :
    e (c • y) = c • e y := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul]
  have h := AddMonoidHom.map_nsmul e.toAddMonoidHom c.val y
  simp only [AddEquiv.coe_toAddMonoidHom] at h
  rw [h]
  conv_rhs => rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]

/-- **被纯量缩放的加性等价的逆**：`e' = c • e`（`c ≠ 0`）⟹ `e'.symm = c⁻¹ • e.symm`。 -/
theorem addEquiv_symm_eq_smul {M N : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] {e e' : M ≃+ N} {c : ZMod p} (hc : c ≠ 0)
    (h : ∀ z, e' z = c • e z) (y : N) : e'.symm y = c⁻¹ • e.symm y := by
  have h1 : e' (c⁻¹ • e.symm y) = y := by
    rw [h, addEquiv_map_zmod_smul p e, smul_smul, mul_inv_cancel₀ hc, one_smul,
      AddEquiv.apply_symm_apply]
  exact ((AddEquiv.eq_symm_apply e').mpr h1).symm

end GenericZMod

/-- **`coeffMap` 对系数态射纯量线性**（`ContinuousCohomology.map_smul` 的 `coeffMap` 形式）。 -/
theorem coeffMap_smul {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {X Y : TopRep (ZMod p) G} (c : ZMod p) (f : X ⟶ Y) (d : ℕ) :
    ContinuousCohomology.coeffMap (c • f) d = c • ContinuousCohomology.coeffMap f d := by
  rw [ContinuousCohomology.coeffMap_def, ContinuousCohomology.coeffMap_def]
  exact ContinuousCohomology.map_smul (ContinuousMonoidHom.id G) c f d

/-! ### 两个本原根互为其幂 -/

/-- 所选本原根在可分闭包的单位群里（`muNRepEquivTrivialFp` 里 ζ 出现的形式）。 -/
noncomputable def unitRoot {ζ : K} (hζ : IsPrimitiveRoot ζ p) : (SeparableClosure K)ˣ :=
  Units.map (algebraMap K (SeparableClosure K)).toMonoidHom
    (Units.mk0 ζ (hζ.ne_zero (NeZero.ne p)))

theorem unitRoot_isPrimitiveRoot {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot (unitRoot hζ) p :=
  (IsPrimitiveRoot.coe_units_iff.mp hζ).map_of_injective
    (Units.map_injective (algebraMap K (SeparableClosure K)).injective)

/-- **两个本原 `p` 次单位根互为其幂**：存在 `n`，`unitRoot hζ ^ n = unitRoot hζ'` 且
`(n : ZMod p) ≠ 0`。 -/
theorem exists_pow_eq {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ p) (hζ' : IsPrimitiveRoot ζ' p) :
    ∃ n : ℕ, unitRoot hζ ^ n = unitRoot hζ' ∧ (n : ZMod p) ≠ 0 := by
  classical
  have hζu := unitRoot_isPrimitiveRoot (K := K) hζ
  have hζ'u := unitRoot_isPrimitiveRoot (K := K) hζ'
  have hmem : unitRoot hζ' ∈ rootsOfUnity p (SeparableClosure K) :=
    (mem_rootsOfUnity p (unitRoot hζ')).mpr hζ'u.pow_eq_one
  obtain ⟨n, hn_lt, hn_eq⟩ := hζu.eq_pow_of_mem_rootsOfUnity hmem
  refine ⟨n, hn_eq, ?_⟩
  intro hn0
  have hpdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hn0
  have hn0' : n = 0 := Nat.eq_zero_of_dvd_of_lt hpdvd hn_lt
  rw [hn0', pow_zero] at hn_eq
  exact hζ'u.ne_one (Fact.out : p.Prime).one_lt hn_eq.symm

/-- `(n : ZMod p) ≠ 0`（`p` 素）⟹ `n` 与 `p` 互素。 -/
theorem natCoprime_of_zmod_ne_zero {n : ℕ} (hn : (n : ZMod p) ≠ 0) : Nat.Coprime n p := by
  refine ((Fact.out : p.Prime).coprime_iff_not_dvd).mpr ?_ |>.symm
  intro hpdvd
  exact hn ((ZMod.natCast_eq_zero_iff n p).mpr hpdvd)

/-! ### (1) λ 层：两个系数识别只差纯量 -/

/-- **两个系数识别只差纯量**（`Hyp87` 的纯量关系推过复合的两端）。 -/
theorem muNRepEquivTrivialFp_eq_smul {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ p)
    (hζ' : IsPrimitiveRoot ζ' p) {n : ℕ} (hn : unitRoot hζ ^ n = unitRoot hζ')
    (hn0 : (n : ZMod p) ≠ 0) (x : (ClassFieldTheory.muNRep p K).V) :
    ClassFieldTheory.muNRepEquivTrivialFp p K hζ' x
      = ((n : ZMod p)⁻¹) • ClassFieldTheory.muNRepEquivTrivialFp p K hζ x := by
  have hζu := unitRoot_isPrimitiveRoot (K := K) hζ
  have hζ'u := unitRoot_isPrimitiveRoot (K := K) hζ'
  simp only [ClassFieldTheory.muNRepEquivTrivialFp, AddEquiv.trans_apply]
  have key : (trivialFpEquiv p (Field.absoluteGaloisGroup K)).symm
        (hζ'u.zmodEquivRootsOfUnity.symm ((ClassFieldTheory.kummerCoeffEquivMuNRep p K).symm x))
      = ((n : ZMod p)⁻¹) • (trivialFpEquiv p (Field.absoluteGaloisGroup K)).symm
        (hζu.zmodEquivRootsOfUnity.symm ((ClassFieldTheory.kummerCoeffEquivMuNRep p K).symm x)) := by
    rw [PrimitiveRootScalar.zmodEquivRootsOfUnity_symm_eq_smul (p := p) hζu hζ'u hn hn0]
    exact addEquiv_map_zmod_smul p
      (trivialFpEquiv p (Field.absoluteGaloisGroup K)).symm.toAddEquiv _ _
  exact key

/-! ### (2) 系数同构的态射层 -/

/-- **两个 `TopRep` 系数同构只差纯量**（态射层）。 -/
theorem muNRepIsoTrivialFp_hom_eq_smul {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ p)
    (hζ' : IsPrimitiveRoot ζ' p) {n : ℕ} (hn : unitRoot hζ ^ n = unitRoot hζ')
    (hn0 : (n : ZMod p) ≠ 0) :
    (ClassFieldTheory.muNRepIsoTrivialFp p K hζ').hom
      = ((n : ZMod p)⁻¹) • (ClassFieldTheory.muNRepIsoTrivialFp p K hζ).hom := by
  refine TopRep.hom_ext (DFunLike.ext _ _ fun x => ?_)
  rw [TopRep.hom_smul, ContIntertwiningMap.smul_apply,
    ClassFieldTheory.muNRepIsoTrivialFp_hom_apply,
    ClassFieldTheory.muNRepIsoTrivialFp_hom_apply]
  exact muNRepEquivTrivialFp_eq_smul hζ hζ' hn hn0 x

/-! ### (3) 上同调层 -/

/-- **上同调的系数搬运只差纯量**（对每个类）。 -/
theorem muNRepCohomologyEquivTrivialFp_apply_eq_smul {ζ ζ' : K}
    (hζ : IsPrimitiveRoot ζ p) (hζ' : IsPrimitiveRoot ζ' p) {n : ℕ}
    (hn : unitRoot hζ ^ n = unitRoot hζ') (hn0 : (n : ZMod p) ≠ 0) (d : ℕ)
    (z : ↑(continuousCohomology d (ClassFieldTheory.muNRep p K)).toModuleCat) :
    ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ' d z
      = ((n : ZMod p)⁻¹) • ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ d z := by
  rw [ClassFieldTheory.muNRepCohomologyEquivTrivialFp_apply,
    ClassFieldTheory.muNRepCohomologyEquivTrivialFp_apply]
  have hmap : ContinuousCohomology.coeffMap
        (ClassFieldTheory.muNRepIsoTrivialFp p K hζ').hom d
      = ((n : ZMod p)⁻¹) • ContinuousCohomology.coeffMap
        (ClassFieldTheory.muNRepIsoTrivialFp p K hζ).hom d := by
    rw [muNRepIsoTrivialFp_hom_eq_smul hζ hζ' hn hn0, coeffMap_smul]
  rw [hmap]
  simp

/-! ### (4) 整条载体链 -/

/-- **`redEquiv` 在两个本原根下只差整数纯量**：`redEquiv hζ' = n • redEquiv hζ`。 -/
theorem redEquiv_eq_smul {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ p) (hζ' : IsPrimitiveRoot ζ' p)
    {n : ℕ} (hn : unitRoot hζ ^ n = unitRoot hζ') (hn0 : (n : ZMod p) ≠ 0)
    (x : GaloBase.H2 K p) :
    redEquiv (p := p) (K := K) hζ' x = (n : ZMod p) • redEquiv (p := p) (K := K) hζ x := by
  have hF : ∀ z, ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ' 2 z
      = ((n : ZMod p)⁻¹) • ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ 2 z :=
    fun z => muNRepCohomologyEquivTrivialFp_apply_eq_smul hζ hζ' hn hn0 2 z
  have key : ∀ y : ↑(TauCeti.cohomFp p (Field.absoluteGaloisGroup K) 2).toModuleCat,
      (ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ' 2).symm y
        = (n : ZMod p) •
          (ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ 2).symm y := by
    intro y
    have h1 : (ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ' 2)
        ((n : ZMod p) •
          (ClassFieldTheory.muNRepCohomologyEquivTrivialFp p K hζ 2).symm y) = y := by
      rw [hF, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, smul_smul,
        inv_mul_cancel₀ hn0, one_smul]
    exact ((LinearEquiv.eq_symm_apply _).mpr h1).symm
  simp only [redEquiv, mE, AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv]
  exact key _

/-- **`Br K` 层：`brOfH2 hζ' x = n • brOfH2 hζ x`**（`Br K` 只有 `ℕ`-纯量）。 -/
theorem brOfH2_eq_nsmul {ζ ζ' : K} (hζ : IsPrimitiveRoot ζ p) (hζ' : IsPrimitiveRoot ζ' p)
    {n : ℕ} (hn : unitRoot hζ ^ n = unitRoot hζ') (hn0 : (n : ZMod p) ≠ 0)
    (x : GaloBase.H2 K p) :
    brOfH2 (p := p) (K := K) hζ' x = n • brOfH2 (p := p) (K := K) hζ x := by
  rw [brOfH2_apply, brOfH2_apply, redEquiv_eq_smul hζ hζ' hn hn0]
  conv_lhs => rw [Nat.cast_smul_eq_nsmul (R := ZMod p) n]
  rw [AddMonoidHom.map_nsmul]

end ZetaIndependence

#print axioms ZetaIndependence.exists_pow_eq
#print axioms ZetaIndependence.muNRepEquivTrivialFp_eq_smul
#print axioms ZetaIndependence.muNRepIsoTrivialFp_hom_eq_smul
#print axioms ZetaIndependence.muNRepCohomologyEquivTrivialFp_apply_eq_smul
#print axioms ZetaIndependence.redEquiv_eq_smul
#print axioms ZetaIndependence.brOfH2_eq_nsmul
