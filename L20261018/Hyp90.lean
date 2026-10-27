import L20261018.Hyp89
import TauCeti.Algebra.CentralSimple.Splitting
import TauCeti.Algebra.BrauerGroup.BaseChange
import Mathlib.LinearAlgebra.Matrix.Action

/-!
# ζ-无关性 (b)：`index` 在单位纯量乘法下不变（R911，基建任务）

**(b) 块**：`Br K` 里的纯量乘法 `γ ↦ u • γ`（`u` 与 `exp γ` 互素）不改变 `index`。
本文件把它建成两条基建，再合成主定理。

## 1. `index ∣ 分裂域次数`（四库皆无，本文件新建）

`TauCeti.Algebra.index` 是 Wedderburn 呈现里除代数的次数。要证它整除任意有限分裂域的次数
`[L : K]`，用**除代数上的双模维数计数**（GS §2.4 的标准论证）：

* `L` 分裂 `D`（`deg D = d`）⟹ `L ⊗[K] D ≅ M_d(L)`（`IsSplittingField.nonempty_algEquiv_matrix_deg`）；
* 于是 `L^d`（`V = Fin d → L`）经 `D →⁺* M_d(L)` 成为 `D`-模，且 `K`-作用经 `L` 与经 `D`
  相容（`IsScalarTower K D V`：纯量矩阵与一切交换）；
* 两条塔律：`[L:K] * d = finrank K V = d^2 * finrank_D V` ⟹ `d ∣ [L:K]`。

## 2. 分裂只依赖 Brauer 类

`mk A = mk B ⟹ (L 分裂 A ↔ L 分裂 B)`（`BrauerGroup.mk_mem_ker_baseChange_iff_isSplittingField`
＋ `baseChange` 的 `ker` 只依赖类）。

## 3. 主定理 `index_eq_of_mk_eq_pow`

`mk A ^ p = 1`、`Nat.Coprime u p`、`mk B = mk A ^ u` ⟹ `index A = index B`：

* 取 `L₁` 分裂 `A` 且 `[L₁:K] = index A`（`exists_isSplittingField_finrank_eq_index`）；
  `L₁` 也分裂 `B`（`ker` 对取幂封闭）⟹ `index B ∣ index A`；
* 反向：取 `M` 分裂 `B` 且 `[M:K] = index B`；则 `baseChange M (mk A)` 的 `u` 次幂与 `p` 次幂
  都是 `1`，而 `gcd u p = 1` ⟹ `orderOf = 1` ⟹ `M` 分裂 `A` ⟹ `index A ∣ index B`。

## 主结果

* **`IndexInvariance.index_dvd_finrank_of_isSplittingField`**
* **`IndexInvariance.index_eq_of_mk_eq_pow`**
-/

open TauCeti

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace IndexInvariance

/-- **`index` 整除分裂域的次数（除代数情形）**：双模维数计数。 -/
theorem index_dvd_finrank_of_isSplittingField_division
    {K : Type u} [Field K] (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D]
    {L : Type*} [Field L] [Algebra K L]
    (h : TauCeti.Algebra.IsSplittingField K D L) :
    TauCeti.Algebra.deg K D ∣ Module.finrank K L := by
  classical
  obtain ⟨e⟩ := h.nonempty_algEquiv_matrix_deg
  set d := TauCeti.Algebra.deg K D with hd
  -- `D` 经 `L ⊗[K] D ≅ M_d(L)` 作用在 `L^d` 上
  let φ : D →+* Matrix (Fin d) (Fin d) L :=
    e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := D)).toRingHom
  letI : Module D (Fin d → L) := Module.compHom (Fin d → L) φ
  have hφ_eq : ∀ x : D, φ x = e (Algebra.TensorProduct.includeRight x) := fun x => rfl
  have hφ_alg (k : K) : φ (algebraMap K D k) = algebraMap K (Matrix (Fin d) (Fin d) L) k := by
    rw [hφ_eq, AlgHom.commutes,
      IsScalarTower.algebraMap_apply K L (TensorProduct K L D),
      IsScalarTower.algebraMap_apply K L (Matrix (Fin d) (Fin d) L), AlgEquiv.commutes]
  -- `K`-作用经 `D` 与经 `L` 一致（纯量矩阵）
  haveI : IsScalarTower K D (Fin d → L) :=
    ⟨fun k x v => by
      show φ (k • x) • v = k • (φ x • v)
      rw [Algebra.smul_def k x, map_mul, hφ_alg, Algebra.algebraMap_eq_smul_one,
        Algebra.smul_mul_assoc, one_mul, IsScalarTower.smul_assoc]⟩
  -- 两条塔律
  have hLV : Module.finrank L (Fin d → L) = d := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h1 : Module.finrank K L * d = Module.finrank K (Fin d → L) := by
    have ht := Module.finrank_mul_finrank K L (Fin d → L)
    rwa [hLV] at ht
  have h2 : Module.finrank K D * Module.finrank D (Fin d → L)
      = Module.finrank K (Fin d → L) :=
    Module.finrank_mul_finrank K D (Fin d → L)
  have h3 : Module.finrank K D = d ^ 2 :=
    (TauCeti.Algebra.deg_sq K D).symm
  refine ⟨Module.finrank D (Fin d → L), ?_⟩
  have hdpos : 0 < d := TauCeti.Algebra.deg_pos K D
  have hkey : Module.finrank K L * d = (d * Module.finrank D (Fin d → L)) * d := by
    rw [h1, ← h2, h3]; ring
  exact Nat.mul_right_cancel hdpos hkey

/-- **`index` 整除分裂域的次数（一般中心单代数）**：经 Wedderburn 呈现归约到除代数。 -/
theorem index_dvd_finrank_of_isSplittingField
    {K : Type u} [Field K] {A : Type u} [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A]
    {L : Type u} [Field L] [Algebra K L]
    (h : TauCeti.Algebra.IsSplittingField K A L) :
    TauCeti.Algebra.index K A ∣ Module.finrank K L := by
  classical
  obtain ⟨n, hn, D, hDR, hAlg, hCent, hFin, -, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing K A
  letI := hDR
  letI := hAlg
  letI := hCent
  letI := hFin
  letI := hn
  have hidx : TauCeti.Algebra.index K A = TauCeti.Algebra.deg K D :=
    TauCeti.Algebra.index_eq_deg_of_algEquiv_matrix e
  rw [hidx]
  refine index_dvd_finrank_of_isSplittingField_division D ?_
  have hmk : BrauerGroup.mk (CSA.of K A) = BrauerGroup.mk (CSA.of K D) := by
    rw [BrauerGroup.mk_eq_mk_of_algEquiv (K := K)
      (A := CSA.of K A) (B := CSA.of K (Matrix (Fin n) (Fin n) D)) e]
    exact BrauerGroup.mk_matrix (CSA.of K D) n
  have hker : BrauerGroup.mk (CSA.of K A) ∈ (BrauerGroup.baseChange K L).ker :=
    (BrauerGroup.mk_mem_ker_baseChange_iff_isSplittingField (K := K) (L := L) (A := A)).mpr h
  rw [hmk] at hker
  exact (BrauerGroup.mk_mem_ker_baseChange_iff_isSplittingField (K := K) (L := L) (A := D)).mp hker

/-- **分裂只依赖 Brauer 类**。 -/
theorem isSplittingField_of_mk_eq
    {K : Type u} [Field K] {A : Type u} [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A]
    {B : Type u} [Ring B] [Algebra K B] [Algebra.IsCentral K B]
    [IsSimpleRing B] [FiniteDimensional K B]
    {L : Type u} [Field L] [Algebra K L]
    (h : BrauerGroup.mk (CSA.of K A) = BrauerGroup.mk (CSA.of K B)) :
    TauCeti.Algebra.IsSplittingField K A L ↔ TauCeti.Algebra.IsSplittingField K B L := by
  rw [← BrauerGroup.mk_mem_ker_baseChange_iff_isSplittingField (K := K) (L := L) (A := A),
    ← BrauerGroup.mk_mem_ker_baseChange_iff_isSplittingField (K := K) (L := L) (A := B), h]

/-- **主定理 (b)：与指数互素的纯量乘法不改变 `index`。** -/
theorem index_eq_of_mk_eq_pow
    {K : Type u} [Field K]
    {A : Type u} [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A]
    {B : Type u} [Ring B] [Algebra K B] [Algebra.IsCentral K B] [IsSimpleRing B]
    [FiniteDimensional K B]
    {p u : ℕ} (hu : Nat.Coprime u p)
    (hA : BrauerGroup.mk (CSA.of K A) ^ p = 1)
    (hAB : BrauerGroup.mk (CSA.of K B) = BrauerGroup.mk (CSA.of K A) ^ u) :
    TauCeti.Algebra.index K A = TauCeti.Algebra.index K B := by
  classical
  have hBA : TauCeti.Algebra.index K B ∣ TauCeti.Algebra.index K A := by
    obtain ⟨L, hLf, hLa, hLfin, hLdeg, hLsplit⟩ :=
      TauCeti.Algebra.exists_isSplittingField_finrank_eq_index K A
    letI := hLf
    letI := hLa
    have hkerA : BrauerGroup.mk (CSA.of K A) ∈ (BrauerGroup.baseChange K L).ker :=
      (BrauerGroup.mk_mem_ker_baseChange_iff_isSplittingField (K := K) (L := L) (A := A)).mpr
        hLsplit
    have hkerB : BrauerGroup.mk (CSA.of K B) ∈ (BrauerGroup.baseChange K L).ker := by
      rw [hAB]
      exact Subgroup.pow_mem _ hkerA u
    have hLsplitB : TauCeti.Algebra.IsSplittingField K B L :=
      (BrauerGroup.mk_mem_ker_baseChange_iff_isSplittingField (K := K) (L := L) (A := B)).mp hkerB
    rw [← hLdeg]
    exact index_dvd_finrank_of_isSplittingField hLsplitB
  have hAB' : TauCeti.Algebra.index K A ∣ TauCeti.Algebra.index K B := by
    obtain ⟨L, hLf, hLa, hLfin, hLdeg, hLsplit⟩ :=
      TauCeti.Algebra.exists_isSplittingField_finrank_eq_index K B
    letI := hLf
    letI := hLa
    have hkerB : BrauerGroup.mk (CSA.of K B) ∈ (BrauerGroup.baseChange K L).ker :=
      (BrauerGroup.mk_mem_ker_baseChange_iff_isSplittingField (K := K) (L := L) (A := B)).mpr
        hLsplit
    have hkerA : BrauerGroup.mk (CSA.of K A) ∈ (BrauerGroup.baseChange K L).ker := by
      have hyu : (BrauerGroup.baseChange K L) (BrauerGroup.mk (CSA.of K A)) ^ u = 1 := by
        rw [← MonoidHom.map_pow, ← hAB]
        exact hkerB
      have hyp : (BrauerGroup.baseChange K L) (BrauerGroup.mk (CSA.of K A)) ^ p = 1 := by
        rw [← MonoidHom.map_pow, hA, MonoidHom.map_one]
      have hdvd : orderOf ((BrauerGroup.baseChange K L) (BrauerGroup.mk (CSA.of K A)))
          ∣ Nat.gcd u p :=
        Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hyu) (orderOf_dvd_iff_pow_eq_one.mpr hyp)
      rw [hu] at hdvd
      exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd))
    have hLsplitA : TauCeti.Algebra.IsSplittingField K A L :=
      (BrauerGroup.mk_mem_ker_baseChange_iff_isSplittingField (K := K) (L := L) (A := A)).mp hkerA
    rw [← hLdeg]
    exact index_dvd_finrank_of_isSplittingField hLsplitA
  exact Nat.dvd_antisymm hAB' hBA

end IndexInvariance

#print axioms IndexInvariance.index_dvd_finrank_of_isSplittingField_division
#print axioms IndexInvariance.index_dvd_finrank_of_isSplittingField
#print axioms IndexInvariance.isSplittingField_of_mk_eq
#print axioms IndexInvariance.index_eq_of_mk_eq_pow
