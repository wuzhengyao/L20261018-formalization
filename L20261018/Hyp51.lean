import L20261018.Hyp50
import TauCeti.Algebra.CentralSimple.Wedderburn
import TauCeti.Algebra.BrauerGroup.Division

/-!
# `(f)` A 档的最后一块：**矩阵消去与次数簿记**（Wedderburn 方向）

`(f)` 的 `hNrd` 输入（`Hyp33.exists_nrdOfIso_eq_norm`）需要一个**代数层面**的同构
`φ : D ≃ₐ[K] CrossedProduct c`，其中 `D` 是论文的中心除代数。`Hyp50` 的侦察已确认 TauCeti
只给到**类相等**：

    TauCeti.BrauerGroup.exists_crossedProductClass_eq_of_isSplittingField :
      (L/K 有限 Galois 分裂 A) → ∃ c, crossedProductClass c = mk (CSA.of K A)

本文件补上从**类相等**走到**同构**的两块砖：

1. **矩阵消去（除代数）**：`M_n(D) ≅ M_m(D')`（`D, D'` 中心除代数）⟹ `D ≅ D'`。
   证法：两边取 Brauer 类 ⟹ 类相等 ⟹ TauCeti 的
   `nonempty_algEquiv_of_mk_eq_mk`（除代数间 Wedderburn 唯一性）。
2. **次数簿记**：`finrank (M_m D) = m ^ 2 * finrank D`，故 `finrank (CP) = finrank D`
   且 `CP ≅ M_m(D)` 时 `m = 1`（`M_1(D) ≅ D`）。

这两块与 `TauCeti.IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing`
（Wedderburn–Artin，**自带** `finrank = n ^ 2 * finrank D`）合起来，即得

* `nonempty_algEquiv_of_wedderburn`（Wedderburn 数据显式版）；
* **`nonempty_algEquiv_of_mk_eq_crossedProductClass`（主定理）**：
  中心除代数 `D`、`c ∈ Z²(L/K)`、`mk D = crossedProductClass c`、`finrank D = [L:K]²`
  ⟹ `D ≃ₐ CrossedProduct c`。

**这是 `(f)` 的 `hNrd` 所缺的代数层面呈现**（`Hyp33` 的入口）：TauCeti 给类相等，这里升成同构。

## R863 的根因（上一轮误判的更正）

R862 把卡点记为「`finrank` 搬运撞 `FiniteDimensional` 实例僵局」——**判错了**。
真实根因：`refine eq_one_of_sq_mul_finrank_eq (D := D) ?_` 里**该引理的隐式 `K` 没被推断**，
于是 `?_` 的目标变成 `m ^ 2 * Module.finrank ?K D = …`，报 `FiniteDimensional ?m D`。
**报错位置指向的是 `?_` 的目标，不是它上下文的表达式。** 修法一行：`(K := K)`。
（`finrank` 搬运本身改用 `LinearEquiv.rank_eq` ＋ `simp only [Module.finrank]` 也保留——
它绕开 `FiniteDimensional`，两处都稳。）
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace SymbolWedderburn

open TauCeti

universe u

variable {K : Type u} [Field K]

/-- **矩阵不改变 Brauer 类**（`CSA.matrix` 版本，`TauCeti.BrauerGroup.mk_matrix`）。 -/
theorem mk_matrix_eq (A : CSA K) (n : ℕ) [NeZero n] :
    TauCeti.BrauerGroup.mk (TauCeti.CSA.matrix A n) = TauCeti.BrauerGroup.mk A :=
  TauCeti.BrauerGroup.mk_matrix A n

/-- **矩阵消去（除代数间）**：同阶矩阵代数的 `K`-代数同构给出除代数本身的同构。

证法：`mk (M_n D) = mk D`（`mk_matrix`）；两边取类得 `mk D = mk D'`；
再用 TauCeti 的除代数 Wedderburn 唯一性 `nonempty_algEquiv_of_mk_eq_mk`。 -/
theorem nonempty_algEquiv_of_matrix_algEquiv {D D' : Type u} [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D] [DivisionRing D'] [Algebra K D']
    [Algebra.IsCentral K D'] [FiniteDimensional K D'] {n m : ℕ} [NeZero n] [NeZero m]
    (e : Matrix (Fin n) (Fin n) D ≃ₐ[K] Matrix (Fin m) (Fin m) D') :
    Nonempty (D ≃ₐ[K] D') := by
  refine TauCeti.BrauerGroup.nonempty_algEquiv_of_mk_eq_mk ?_
  calc TauCeti.BrauerGroup.mk (TauCeti.CSA.of K D)
      = TauCeti.BrauerGroup.mk (TauCeti.CSA.matrix (TauCeti.CSA.of K D) n) :=
        (mk_matrix_eq (TauCeti.CSA.of K D) n).symm
    _ = TauCeti.BrauerGroup.mk (TauCeti.CSA.matrix (TauCeti.CSA.of K D') m) :=
        TauCeti.BrauerGroup.mk_eq_mk_of_algEquiv e
    _ = TauCeti.BrauerGroup.mk (TauCeti.CSA.of K D') := mk_matrix_eq (TauCeti.CSA.of K D') m

/-! ### 次数簿记的两块 -/

/-- **`M_1(D) ≅ D`**（`1 × 1` 矩阵代数就是标量代数）。

用 `AlgEquiv.ofBijective`（避免手工构造逆同态与两端的 `commutes`）：取 `M ↦ M 0 0`；
单射性因为 `Fin 1` 只有一个指标、满射性取常值矩阵。 -/
noncomputable def matrixFinOneAlgEquiv (D : Type u) [Ring D] [Algebra K D] :
    Matrix (Fin 1) (Fin 1) D ≃ₐ[K] D :=
  AlgEquiv.ofBijective
    { toFun := fun M => M 0 0
      map_one' := rfl
      map_mul' := fun M N => by
        rw [Matrix.mul_apply, Fin.sum_univ_one]
      map_zero' := rfl
      map_add' := fun M N => rfl
      commutes' := fun r => by
        rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, if_pos rfl]
        rfl }
    ⟨fun M N h => by
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      exact h,
     fun d => ⟨Matrix.of fun _ _ => d, rfl⟩⟩

/-- **次数簿记**：`finrank (M_m D) = m ^ 2 * finrank D`，故若它等于 `finrank D ≠ 0` 则 `m = 1`。 -/
theorem eq_one_of_sq_mul_finrank_eq {D : Type u} [Ring D] [Algebra K D]
    [FiniteDimensional K D] [Nontrivial D] {m : ℕ}
    (h : m ^ 2 * Module.finrank K D = Module.finrank K D) : m = 1 := by
  have hc : 0 < Module.finrank K D := Module.finrank_pos
  have h2 : m * m * Module.finrank K D = 1 * Module.finrank K D := by
    rw [one_mul, ← pow_two]
    exact h
  have h3 : m * m = 1 := Nat.eq_of_mul_eq_mul_right hc h2
  exact Nat.dvd_one.mp ⟨m, h3.symm⟩

/-! ### 主定理：类相等 ＋ 同次数 ⟹ 代数同构 -/

/-- **从类相等回到代数同构（交叉积版，Wedderburn 数据显式）**。

设 `D` 是中心除代数、`c` 是有限 Galois `L/K` 上的 `2`-余环，且
① `mk D_c = mk D`（`D_c` 是 `CrossedProduct c` 的 Wedderburn 除代数部分）；
② `CrossedProduct c ≅ M_m(D_c)`；
③ `finrank D = finrank (CrossedProduct c)`。
则 `D ≃ₐ CrossedProduct c`。

**证明链**：`D_c ≅ D`（除代数唯一性）⟹ 次数簿记给 `m = 1` ⟹ `M_1(D_c) ≅ D_c ≅ D`。

**R863 修法（上一轮卡点的根因）**：`finrank` 搬运不要走 `LinearEquiv.finrank_eq`
（那会撞上 `FiniteDimensional ?m D` 的实例僵局），而走 **`LinearEquiv.rank_eq`
（`Cardinal` 层，无 `FiniteDimensional` 依赖）** 再 `simp only [Module.finrank]`：
`Module.finrank` 的定义就是 `Cardinal.toNat (Module.rank _ _)`。 -/
theorem nonempty_algEquiv_of_wedderburn
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (c : TauCeti.TwoCocycle K L)
    {D : Type u} [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D]
    {m : ℕ} {Dc : Type u} [DivisionRing Dc] [Algebra K Dc] [Algebra.IsCentral K Dc]
    [FiniteDimensional K Dc]
    (hmk : TauCeti.BrauerGroup.mk (CSA.of K Dc) = TauCeti.BrauerGroup.mk (CSA.of K D))
    (hfin : Module.finrank K (TauCeti.CrossedProduct c) = m ^ 2 * Module.finrank K Dc)
    (hdeg : Module.finrank K D = Module.finrank K (TauCeti.CrossedProduct c))
    (eW : TauCeti.CrossedProduct c ≃ₐ[K] Matrix (Fin m) (Fin m) Dc) :
    Nonempty (D ≃ₐ[K] TauCeti.CrossedProduct c) := by
  -- `D_c ≅ D`（除代数间 Wedderburn 唯一性）
  obtain ⟨eD⟩ := TauCeti.BrauerGroup.nonempty_algEquiv_of_mk_eq_mk (D := Dc) (E := D) hmk
  -- 次数簿记：`finrank D_c = finrank D`（走 `Module.rank`，绕开 `FiniteDimensional` 实例僵局）
  have hDcEq : Module.finrank K Dc = Module.finrank K D := by
    have h := LinearEquiv.rank_eq (AlgEquiv.toLinearEquiv (R := K) eD)
    simp only [Module.finrank]
    rw [h]
  have hm1 : m = 1 := by
    refine eq_one_of_sq_mul_finrank_eq (K := K) (D := D) ?_
    calc m ^ 2 * Module.finrank K D = m ^ 2 * Module.finrank K Dc := by rw [hDcEq]
      _ = Module.finrank K (TauCeti.CrossedProduct c) := hfin.symm
      _ = Module.finrank K D := hdeg.symm
  subst hm1
  exact ⟨eD.symm.trans ((matrixFinOneAlgEquiv (K := K) Dc).symm.trans eW.symm)⟩

/-- **`(f)` 的交叉积呈现**：若中心除代数 `D` 与 `L/K` 上某个 `2`-余环的交叉积
**同 Brauer 类**且**同次数**（`finrank D = [L:K]²`），则 `D ≃ₐ CrossedProduct c`。

这就是 `(f)` 的 `hNrd`（`Hyp33.exists_nrdOfIso_eq_norm`）所缺的**代数层面**呈现：
`E` 分裂 `D` 时，TauCeti 的 `exists_crossedProductClass_eq_of_isSplittingField` 给类相等，
本定理把它升成同构。 -/
theorem nonempty_algEquiv_of_mk_eq_crossedProductClass
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (c : TauCeti.TwoCocycle K L)
    {D : Type u} [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D]
    (hmk : TauCeti.BrauerGroup.mk (CSA.of K D) = TauCeti.BrauerGroup.crossedProductClass c)
    (hdeg : Module.finrank K D = Module.finrank K L ^ 2) :
    Nonempty (D ≃ₐ[K] TauCeti.CrossedProduct c) := by
  obtain ⟨m, hm, Dc, hDcRing, hDcAlg, hDcCent, hDcFin, hfin, ⟨eW⟩⟩ :=
    TauCeti.IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing (K := K)
      (A := TauCeti.CrossedProduct c)
  letI : DivisionRing Dc := hDcRing
  letI : Algebra K Dc := hDcAlg
  letI : Algebra.IsCentral K Dc := hDcCent
  letI : FiniteDimensional K Dc := hDcFin
  have hmat : TauCeti.BrauerGroup.mk (CSA.of K (TauCeti.CrossedProduct c))
      = TauCeti.BrauerGroup.mk (CSA.matrix (CSA.of K Dc) m) :=
    TauCeti.BrauerGroup.mk_eq_mk_of_algEquiv eW
  have h1 : TauCeti.BrauerGroup.mk (CSA.of K Dc) = TauCeti.BrauerGroup.mk (CSA.of K D) := by
    rw [← mk_matrix_eq (K := K) (A := CSA.of K Dc) m, ← hmat,
      ← TauCeti.BrauerGroup.crossedProductClass_def, ← hmk]
  have hdeg' : Module.finrank K D = Module.finrank K (TauCeti.CrossedProduct c) := by
    rw [hdeg, TauCeti.CrossedProduct.finrank_eq_finrank_sq]
  exact nonempty_algEquiv_of_wedderburn (K := K) c h1 hfin hdeg' eW

end SymbolWedderburn