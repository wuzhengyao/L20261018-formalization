import L20261018.Hyp90
/-!
# **主定理**：`indOfH2` 与 ζ 的选取无关（R911）

用户指令：「希望 `ind` 对 ζ 的选取无关」。两块已备好：

* **(a)** `Hyp89.brOfH2_eq_nsmul`：`brOfH2 hζ' x = n • brOfH2 hζ x`（`n` 由 `ζ' = ζ ^ n` 给出）；
* **(b)** `Hyp90.index_eq_of_mk_eq_pow`：`mk B = mk A ^ u`、`Nat.Coprime u p`、`mk A ^ p = 1`
  ⟹ `index A = index B`。

本文件把 (a) 抬到 `BrauerGroup` 层（`brauerOfH2 hζ' x = (brauerOfH2 hζ x) ^ n`），
再用 (b) 收口。

## 主结果

* `ZetaIndependence.brauerOfH2_eq_pow`
* **`ZetaIndependence.indOfH2_independent`** —— 用户目标的逐字形式。
-/

open TauCeti

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ZetaIndependence

open H2Bridge

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {ζ ζ' : K}

/-- **(a) 抬到 `BrauerGroup` 层**：`brauerOfH2 hζ' x` 是 `brauerOfH2 hζ x` 的 `n` 次幂。 -/
theorem brauerOfH2_eq_pow (hζ : IsPrimitiveRoot ζ p) (hζ' : IsPrimitiveRoot ζ' p)
    {n : ℕ} (hn : unitRoot hζ ^ n = unitRoot hζ') (hn0 : (n : ZMod p) ≠ 0)
    (x : GaloBase.H2 K p) :
    brauerOfH2 hζ' x = (brauerOfH2 hζ x) ^ n := by
  have h1 : (ClassFieldTheory.brauerGroupEquivBr K).symm
        (n • brOfH2 (p := p) (K := K) hζ x)
      = n • (ClassFieldTheory.brauerGroupEquivBr K).symm (brOfH2 (p := p) (K := K) hζ x) := by
    exact AddMonoidHom.map_nsmul
      (ClassFieldTheory.brauerGroupEquivBr K).symm.toAddMonoidHom n
      (brOfH2 (p := p) (K := K) hζ x)
  simp only [brauerOfH2]
  rw [brOfH2_eq_nsmul hζ hζ' hn hn0, h1]
  rfl

/-- **(b) 的前提**：`brauerOfH2 hζ x` 的 `p` 次幂是 `1`（像在 `p`-挠内，`Hyp88`）。 -/
theorem brauerOfH2_pow_prime (hζ : IsPrimitiveRoot ζ p) (x : GaloBase.H2 K p) :
    (brauerOfH2 hζ x) ^ p = 1 := by
  have hy0 : p • (ClassFieldTheory.brauerGroupEquivBr K).symm
      (brOfH2 (p := p) (K := K) hζ x) = 0 := by
    have h := AddMonoidHom.map_nsmul
      (ClassFieldTheory.brauerGroupEquivBr K).symm.toAddMonoidHom p
      (brOfH2 (p := p) (K := K) hζ x)
    simp only [AddEquiv.coe_toAddMonoidHom] at h
    rw [← h, p_smul_brOfH2, map_zero]
  show Additive.toMul (p • (ClassFieldTheory.brauerGroupEquivBr K).symm
    (brOfH2 (p := p) (K := K) hζ x)) = 1
  rw [hy0]
  rfl

/-- **主定理：`indOfH2` 与 ζ 的选取无关。** -/
theorem indOfH2_independent (hζ : IsPrimitiveRoot ζ p) (hζ' : IsPrimitiveRoot ζ' p)
    (x : GaloBase.H2 K p) : indOfH2 hζ x = indOfH2 hζ' x := by
  classical
  obtain ⟨n, hn, hn0⟩ := exists_pow_eq (K := K) hζ hζ'
  set W := divisionRep (brauerOfH2 hζ x) with hW
  set W' := divisionRep (brauerOfH2 hζ' x) with hW'
  letI := W.instDR
  letI := W.instAlg
  letI := W.instCentral
  letI := W.instFin
  letI := W'.instDR
  letI := W'.instAlg
  letI := W'.instCentral
  letI := W'.instFin
  have hcop : Nat.Coprime n p := natCoprime_of_zmod_ne_zero hn0
  have hmk : BrauerGroup.mk (CSA.of K W'.D) = BrauerGroup.mk (CSA.of K W.D) ^ n := by
    rw [W'.mk_eq, brauerOfH2_eq_pow hζ hζ' hn hn0, W.mk_eq]
  have hαp : BrauerGroup.mk (CSA.of K W.D) ^ p = 1 := by
    rw [W.mk_eq]
    exact brauerOfH2_pow_prime hζ x
  have hidx : W.index = W'.index := by
    have h := IndexInvariance.index_eq_of_mk_eq_pow (p := p) (u := n) (A := W.D) (B := W'.D)
      hcop hαp hmk
    simpa only [DivisionRep.index] using h
  have h1 : indOfH2 hζ x = W.index := rfl
  have h2 : indOfH2 hζ' x = W'.index := rfl
  rw [h1, h2, hidx]

end ZetaIndependence

#print axioms ZetaIndependence.brauerOfH2_eq_pow
#print axioms ZetaIndependence.brauerOfH2_pow_prime
#print axioms ZetaIndependence.indOfH2_independent
