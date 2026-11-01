import L20261018.Hyp802
import TauCeti.FieldTheory.GaloisCohomology.Hilbert90
import TauCeti.FieldTheory.GaloisCohomology.Kummer

/-!
# S78 R5：`(R2)` 无限残域路线的**基建可用性证书**（`L46` 机检化）

## 背景

`GAP3-PLAN` §26.3／§27 把第 4 章的唯一开口钉死为 **`(R2)` 在 `dim ker v̄ ≥ 2` 的一般 Hensel 情形**，
并给出路线：**`κ := 𝓀[F]` 侧的 Kummer 理论**（Hilbert 90 ＋ `κ^×/κ^{×p} ≅ H¹(κ, μ_p)`，`κ` **可无限**）。

`L46` 侦察读数（`raw/TauCeti/TauCeti/FieldTheory/GaloisCohomology/{Hilbert90,Kummer}.lean`）：
这两块**对任意域**都已机检，**无 `[Finite κ]`、无完备性**。
本件把它们**实例化到 `κ = 𝓀[F]`** 并落成声明，使「须自建 `κ` 侧 Hilbert 90／Kummer 理论」
这类判决**永久不可再作出**（`L46` 触发条件 ②）。

## 交付

| 声明 | 内容 |
|---|---|
| **`isUnit_natCast_residueField`** | `p.Coprime q ⟹ IsUnit (p : 𝓀[F])`（`q` = `CharP 𝓀[F] q` 的素数）—— Kummer 理论的 `IsUnit` 侧条件**自动兑现** |
| **`hilbert90_residueField`** | `H¹(G_κ, κ̄^×) = 0`（**任意**剩余域，含无限） |
| **`kummerIso_residueField`** | ★ `κˣ ⧸ (κˣ)^p ≃* H¹(κ, μ_p)`（**任意**剩余域） |
| `kummerMap_residueField_surjective` | `κˣ ↠ H¹(κ, μ_p)` |
| `ker_kummerMap_residueField` | `ker = (κˣ)^p` |

⚠ **本件不证明 `(R2)`**：它只把 §27.2 的**第 1–2 步**（κ 侧输入）落成机检件；
真正的剩余是 `F` 侧的**惯性过滤／载体识别**（§3.5 的范围收紧）。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

variable (p : ℕ) [NeZero p] [Fact p.Prime]
variable {F : Type} [Field F] [ValuativeRel F]

/-- ★★★ **剩余域里 `p` 是单位**（`CharP 𝓀[F] q` ＋ `p.Coprime q` ＋ `q` 素）。

⟹ Kummer／Hilbert 90 所需的 `IsUnit (p : 𝓀[F])` **不必作为假设**。 -/
theorem isUnit_natCast_residueField (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q) :
    IsUnit (p : IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have hdvd : q ∣ p :=
    (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q p).mp h0
  exact (Fact.out : Nat.Prime q).ne_one (Nat.Coprime.eq_one_of_dvd hcop.symm hdvd)

/-- ★★★★ **`κ` 侧的 Hilbert 90**：`H¹(G_κ, κ̄^×) = 0`（`κ` **任意**，含无限）。

`TauCeti.hilbert90`（`GaloisCohomology/Hilbert90.lean`）的实例化。 -/
theorem hilbert90_residueField :
    CategoryTheory.Limits.IsZero
      (continuousCohomology 1
        (ofDiscreteModule ℤ
          (AbsoluteGaloisGroup (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer))
          (UnitsCoeff (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer)))) :=
  hilbert90 (K := IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer)

/-- ★★★★★ **`κ` 侧的 Kummer 同构**：`κˣ ⧸ (κˣ)^p ≃* H¹(κ, μ_p)`（`κ` **任意**，含无限）。

`TauCeti.kummerIso` 的实例化；`IsUnit (p : 𝓀[F])` 由 `isUnit_natCast_residueField` 供给。 -/
noncomputable def kummerIso_residueField (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q) :
    powerClassQuotient (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer)ˣ p ≃*
      Multiplicative (H1
        (AbsoluteGaloisGroup (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer))
        (KummerCoeff (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) p)) :=
  kummerIso _ p (isUnit_natCast_residueField (F := F) (p := p) q hcop)

/-- `κˣ ↠ H¹(κ, μ_p)`（Kummer 映射满，Hilbert 90 的直接推论）。 -/
theorem kummerMap_residueField_surjective (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q) :
    Function.Surjective
      (kummerMap (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) p
        (isUnit_natCast_residueField (F := F) (p := p) q hcop)) :=
  kummerMap_surjective _

/-- `ker (κˣ → H¹(κ, μ_p)) = (κˣ)^p`。 -/
theorem ker_kummerMap_residueField (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q) :
    (kummerMap (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) p
      (isUnit_natCast_residueField (F := F) (p := p) q hcop)).ker
      = powerSubgroup (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer)ˣ p :=
  ker_kummerMap _

end L20261018

#print axioms L20261018.isUnit_natCast_residueField
#print axioms L20261018.hilbert90_residueField
#print axioms L20261018.kummerIso_residueField
#print axioms L20261018.kummerMap_residueField_surjective
#print axioms L20261018.ker_kummerMap_residueField
