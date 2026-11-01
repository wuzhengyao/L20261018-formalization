import L20261018.Infra.Cohomology.Step007_additive_hilbert90

/-!
# R1302（S37 第 10 轮）：S4 的落点 —— Kummer 桥在 `H²` 上、以及战役收尾的两个推论

## 本轮

`Hyp382` 给出 `H^i(G_F, μ_p(F)) ≅ H^i(G_F, ZMod p)`（全次数）。本轮把它**落到第二章/第四章实际用的度数**
（`i = 1, 2`），并给出 `Hyp387` 的一阶推论，使 S4 的「桥落在 `H²(F,μ_p)`」成为一条**可引用的等式**。

| 声明 | 内容 |
|---|---|
| **`muH2Equiv`** | ★★★★★ `H²(G_F, μ_p(F)) ≅ H²(G_F, ZMod p) = GaloBase.H2 F p`（S4 的落点） |
| **`muH1Equiv`** | ★★★★★ `H¹(G_F, μ_p(F)) ≅ GaloBase.V F p`（第四章的 `V`） |
| `additiveHilbert90_one` | `H¹(Gal(L/K), L) = 0`（`Hyp387` 的 `n = 0` 特化，GS 的加性 Hilbert 90） |

## 口径

* `muH1Equiv`／`muH2Equiv` 是 `Hyp382.muCohomologyIso` 的**特化**（`i = 1, 2`），
  载体 `GaloBase.V`／`GaloBase.H2` 就是 `H¹`／`H²(G_F, ZMod p)`（`A.lean:660`），故 `rfl` 级。
* 于是第四章里所有落在 `V`／`H2` 的陈述（`prop:prelim-residue` (1) 的 `d : H2 → VKG` 等）
  **可读作真的 `μ_p` 上同调**。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

variable (F : Type) [Field F]

/-- ★★★★★ **S4 的落点**：`H¹(G_F, μ_p(F)) ≅ GaloBase.V F p`（第四章的 `V = H¹(G_F,μ_p)`）。 -/
noncomputable def muH1Equiv {p : ℕ} [NeZero p] [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    continuousCohomology 1 (muPReal p F) ≅
      continuousCohomology 1 (GaloBase.muP F p) :=
  muCohomologyIso (F := F) (p := p) hζ 1

/-- ★★★★★ **S4 的落点**：`H²(G_F, μ_p(F)) ≅ GaloBase.H2 F p = H²(G_F,μ_p)`。 -/
noncomputable def muH2Equiv {p : ℕ} [NeZero p] [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    continuousCohomology 2 (muPReal p F) ≅
      continuousCohomology 2 (GaloBase.muP F p) :=
  muCohomologyIso (F := F) (p := p) hζ 2

/-- `Gal(L/K)` 的两个 `H¹` 载体相同（`GaloBase.V` 就是 `H¹(G_F, ZMod p)`）。 -/
theorem galoBaseV_eq (p : ℕ) [NeZero p] [Fact p.Prime] :
    GaloBase.V F p =
      ↑(continuousCohomology 1 (GaloBase.muP F p)).toModuleCat := rfl

/-- `GaloBase.H2` 就是 `H²(G_F, ZMod p)`。 -/
theorem galoBaseH2_eq (p : ℕ) [NeZero p] [Fact p.Prime] :
    GaloBase.H2 F p =
      ↑(continuousCohomology 2 (GaloBase.muP F p)).toModuleCat := rfl

end L20261018

namespace L20261018

/-- **GS 的加性 Hilbert 90（一阶）**：`H¹(Gal(L/K), L) = 0`。 -/
theorem additiveHilbert90_one {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace L] [DiscreteTopology L] :
    Subsingleton ↑(continuousCohomology 1
      (TauCeti.ofDiscreteModule ℤ (L ≃ₐ[K] L) L)).toModuleCat :=
  additiveHilbert90 (K := K) (L := L) 0

end L20261018

#print axioms L20261018.muH1Equiv
#print axioms L20261018.muH2Equiv
#print axioms L20261018.galoBaseV_eq
#print axioms L20261018.galoBaseH2_eq
#print axioms L20261018.additiveHilbert90_one
