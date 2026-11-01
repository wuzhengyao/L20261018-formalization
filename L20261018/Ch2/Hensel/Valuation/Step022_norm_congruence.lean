import L20261018.Witness.Step006_val_compat_complete_field
import L20261018.Ch2.Hensel.Valuation.Step020_left_mul_matrix_shape

/-!
# R1043（路径 A · **S28 第 2 步**）：`N(y) ≡ a₀^p (mod π)`

设 `y = Σ_{i<p} cᵢ sⁱ`，`cᵢ ∈ 𝒪_F`。本文件机检

```
residue (N_{L/F}(y)) = (residue (c 0))^p
```

**路线**：
1. **`𝒪_F`-系数矩阵** `coeffMatrix`：`M₀ i j = c (i−j)`（`j ≤ i`）／`b · c (i+p−j)`（`i < j`，`b` 是 `π` 的像）；
2. `Hyp185` 的两条逐元公式 ＋ `Matrix.ext` ⟹ **`leftMulMatrix B y = algebraMap.mapMatrix M₀`**；
3. `RingHom.map_det` ⟹ `N y = algebraMap (M₀.det)`（且 `N y ∈ 𝒪_F`）；
4. `red := IsLocalRing.residue ↥𝒪_F`：`red (M₀.det) = (red.mapMatrix M₀).det`；
5. `red.mapMatrix M₀` **下三角**（`i < j` 时 `red (b * c·) = 0`，因 `π ∈ 𝔪`）、对角 `red (c 0)`；
6. `det_of_isLowerTriangular` ＋ `Finset.prod_const` ⟹ `= (red (c 0))^p`。
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section NormResidue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **`𝒪_F`-系数矩阵**：`M₀ i j = c (i−j)`（`j ≤ i`）／`b · c (i+p−j)`（`i < j`）。 -/
noncomputable def coeffMatrix (b : ↥𝒪[F]) (c : ℕ → ↥𝒪[F]) :
    Matrix (Fin p) (Fin p) ↥𝒪[F] :=
  fun i j => if (j : ℕ) ≤ (i : ℕ) then c ((i : ℕ) - (j : ℕ))
    else b * c ((i : ℕ) + p - (j : ℕ))

/-- **模 `π` 后的矩阵**：下三角、对角 `red (c 0)`。 -/
noncomputable def residueCoeffMatrix (c : ℕ → ↥𝒪[F]) : Matrix (Fin p) (Fin p) 𝓀[F] :=
  fun i j => if (j : ℕ) ≤ (i : ℕ) then IsLocalRing.residue ↥𝒪[F] (c ((i : ℕ) - (j : ℕ))) else 0

/-- **一致化元的剩余为 `0`**（`π ∈ 𝔪`）。 -/
theorem residue_uniformizer_image_eq_zero (hv : ValCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {b : ↥𝒪[F]} (hb : (b : F) = (π : F)) :
    IsLocalRing.residue ↥𝒪[F] b = 0 := by
  have hπ𝒪 : (π : F) ∈ 𝒪[F] := valCompat_uniformizer_mem_integer (F := F) hv hπ
  have hb' : (⟨(π : F), hπ𝒪⟩ : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] :=
    valCompat_uniformizer_mem_maximalIdeal (F := F) hv hπ
  have hbeq : b = ⟨(π : F), hπ𝒪⟩ := Subtype.ext hb
  have hmem : b ∈ IsLocalRing.maximalIdeal ↥𝒪[F] := by rwa [hbeq]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem

/-- **核心**：`red ((coeffMatrix b c).det) = (red (c 0))^p`。 -/
theorem residue_det_coeffMatrix (hv : ValCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {b : ↥𝒪[F]} (hb : (b : F) = (π : F))
    (c : ℕ → ↥𝒪[F]) :
    IsLocalRing.residue ↥𝒪[F] ((coeffMatrix (F := F) p b c).det)
      = (IsLocalRing.residue ↥𝒪[F] (c 0)) ^ p := by
  rw [RingHom.map_det (IsLocalRing.residue ↥𝒪[F]) (coeffMatrix (F := F) p b c)]
  -- 模 π 后的矩阵就是 `residueCoeffMatrix`
  have htri : (IsLocalRing.residue ↥𝒪[F]).mapMatrix (coeffMatrix (F := F) p b c)
      = residueCoeffMatrix (F := F) p c := by
    ext i j
    rw [RingHom.mapMatrix_apply]
    show IsLocalRing.residue ↥𝒪[F] (if (j : ℕ) ≤ (i : ℕ) then c ((i : ℕ) - (j : ℕ))
      else b * c ((i : ℕ) + p - (j : ℕ))) = residueCoeffMatrix (F := F) p c i j
    by_cases hji : (j : ℕ) ≤ (i : ℕ)
    · rw [if_pos hji, residueCoeffMatrix, if_pos hji]
    · rw [if_neg hji, residueCoeffMatrix, if_neg hji, map_mul,
        residue_uniformizer_image_eq_zero (F := F) hv hπ hb, zero_mul]
  rw [htri]
  -- 下三角
  have hlow : Matrix.IsLowerTriangular (residueCoeffMatrix (F := F) p c) := by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    rw [residueCoeffMatrix, if_neg (by omega : ¬ (j : ℕ) ≤ (i : ℕ))]
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  -- 对角全等 `red (c 0)`
  have hdiag : ∀ i : Fin p, residueCoeffMatrix (F := F) p c i i
      = IsLocalRing.residue ↥𝒪[F] (c 0) := by
    intro i
    rw [residueCoeffMatrix, if_pos le_rfl, Nat.sub_self]
  rw [Finset.prod_congr rfl fun i _ => hdiag i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **矩阵兼容**：`leftMulMatrix B y = algebraMap.mapMatrix (coeffMatrix b c)`。 -/
theorem leftMulMatrix_eq_mapMatrix_coeffMatrix (π : Fˣ) {b : ↥𝒪[F]} (hb : (b : F) = (π : F))
    {B : Module.Basis (Fin p) F (AdjoinRoot (X ^ p - C (π : F)))}
    (hB : ∀ i : Fin p, B i = (AdjoinRoot.root (X ^ p - C (π : F))) ^ (i : ℕ))
    (c : ℕ → ↥𝒪[F]) :
    Algebra.leftMulMatrix B (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F)))
      = (algebraMap ↥𝒪[F] F).mapMatrix (coeffMatrix (F := F) p b c) := by
  ext i j
  rw [RingHom.mapMatrix_apply]
  show Algebra.leftMulMatrix B (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))) i j
    = (algebraMap ↥𝒪[F] F) (coeffMatrix (F := F) p b c i j)
  by_cases hji : (j : ℕ) ≤ (i : ℕ)
  · rw [leftMulMatrix_entry_of_le (F := F) p π hB _ hji, coeffMatrix, if_pos hji]
    rfl
  · push_neg at hji
    rw [leftMulMatrix_entry_of_lt (F := F) p π hB _ hji, coeffMatrix, if_neg (by omega), map_mul]
    have hb' : (algebraMap ↥𝒪[F] F) b = (π : F) := by
      rw [show (algebraMap ↥𝒪[F] F) b = (b : F) from rfl, hb]
    rw [hb']
    rfl

/-- **`N y ∈ 𝒪_F`**（它是 `𝒪_F`-矩阵行列式的像）。 -/
theorem norm_mem_integer (π : Fˣ) {b : ↥𝒪[F]} (hb : (b : F) = (π : F))
    {B : Module.Basis (Fin p) F (AdjoinRoot (X ^ p - C (π : F)))}
    (hB : ∀ i : Fin p, B i = (AdjoinRoot.root (X ^ p - C (π : F))) ^ (i : ℕ))
    (c : ℕ → ↥𝒪[F]) :
    (Algebra.norm F (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))) : F) ∈ 𝒪[F] := by
  rw [Algebra.norm_eq_matrix_det B, leftMulMatrix_eq_mapMatrix_coeffMatrix (F := F) p π hb hB c,
    ← RingHom.map_det (algebraMap ↥𝒪[F] F) (coeffMatrix (F := F) p b c)]
  exact (coeffMatrix (F := F) p b c).det.2

/-- **S28 第 2 步（`N y` 版）**：`red (N y) = (red (c 0))^p`。 -/
theorem norm_residue_eq_pow (hv : ValCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {b : ↥𝒪[F]} (hb : (b : F) = (π : F))
    {B : Module.Basis (Fin p) F (AdjoinRoot (X ^ p - C (π : F)))}
    (hB : ∀ i : Fin p, B i = (AdjoinRoot.root (X ^ p - C (π : F))) ^ (i : ℕ))
    (c : ℕ → ↥𝒪[F])
    (hN : (Algebra.norm F (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))) : F) ∈ 𝒪[F]) :
    IsLocalRing.residue ↥𝒪[F]
        ⟨Algebra.norm F (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))), hN⟩
      = (IsLocalRing.residue ↥𝒪[F] (c 0)) ^ p := by
  have hnorm : (Algebra.norm F (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))) : F)
      = ((coeffMatrix (F := F) p b c).det : F) := by
    rw [Algebra.norm_eq_matrix_det B, leftMulMatrix_eq_mapMatrix_coeffMatrix (F := F) p π hb hB c,
      ← RingHom.map_det (algebraMap ↥𝒪[F] F) (coeffMatrix (F := F) p b c)]
    rfl
  have hsub : (⟨Algebra.norm F (sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))), hN⟩
      : ↥𝒪[F]) = (coeffMatrix (F := F) p b c).det := Subtype.ext hnorm
  rw [hsub]
  exact residue_det_coeffMatrix (F := F) p hv hπ hb c

end NormResidue

end L20261018

#print axioms L20261018.residue_uniformizer_image_eq_zero
#print axioms L20261018.residue_det_coeffMatrix
#print axioms L20261018.leftMulMatrix_eq_mapMatrix_coeffMatrix
#print axioms L20261018.norm_mem_integer
#print axioms L20261018.norm_residue_eq_pow
