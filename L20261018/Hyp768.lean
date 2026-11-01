import Hyp767

/-!
# S72 R11：`H-conj1` 搬进 **TauCeti 的 `H1ConjInvariants` 接口**（解锁路线 (c)）

## 为什么这一步值得做

`H-conj1`（`Hyp762.Conj1Trivial`）原本只以本战役的语言陈述：
`∀ g x, explicitConj1 (inertiaLoc F) g x = x`。
而 `RECON-tauceti-lcft.md` §5 选定的**路线 (c)** 需要它的 TauCeti 形态
`H1ConjInvariants Γ μ_p I = ⊤`，才有下列库内件可用：

* `TauCeti.ContCohomology.mem_H1ConjInvariants_iff_of_smul_eq_self`
  （`ConjInvariants.lean:83`，**与 H-conj1 逐字同形**：`χ(conjNormal g n) = χ n`）；
* `TauCeti.ContCohomology.H1ConjInvariantsEquivOfSmulEqSelf`
  （`:123`，`H¹(I,μ_p)^Γ ≅ Hom_cont(I ⧸ I^p[I,Γ], μ_p)`⟹ 把 `H-conj1` 化成**商群命题**）。

本件提供两向的**改写**（等价，不是新假设）。

## 交付

| 声明 | 内容 |
|---|---|
| **`conjInvariants_eq_top_of_conj1Trivial`** | `Conj1Trivial ⟹ H1ConjInvariants Γ (ℤ/p) I = ⊤` |
| **`conj1Trivial_of_conjInvariants_eq_top`** | 反向 |
| **`conj1Trivial_iff_conjInvariants_eq_top`** | ★★★★ 两者**等价**（`Iff`） |
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★ `H-conj1` ⟹ `H1ConjInvariants` 取全集（TauCeti 接口形态）。 -/
theorem conjInvariants_eq_top_of_conj1Trivial (h : Conj1Trivial F p) :
    H1ConjInvariants (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) = ⊤ := by
  ext x
  constructor
  · intro _
    exact AddSubgroup.mem_top x
  · intro _
    exact fun g => h g x

/-- ★★★★ 反向：`H1ConjInvariants = ⊤` ⟹ `H-conj1`。 -/
theorem conj1Trivial_of_conjInvariants_eq_top
    (h : H1ConjInvariants (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) = ⊤) :
    Conj1Trivial F p := by
  intro g x
  have hx : x ∈ H1ConjInvariants (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) := by
    rw [h]; exact AddSubgroup.mem_top x
  exact hx g

/-- ★★★★ **两种形态等价**：`Conj1Trivial ⟺ H1ConjInvariants Γ (ℤ/p) I = ⊤`。

⟹ 路线 (c) 的库内接口（`H1ConjInvariantsEquivOfSmulEqSelf` 等）**现在可以直接消费 `H-conj1`**。 -/
theorem conj1Trivial_iff_conjInvariants_eq_top :
    Conj1Trivial F p ↔
      H1ConjInvariants (AbsoluteGaloisGroup F) (ZMod p) (inertiaLoc F) = ⊤ :=
  ⟨conjInvariants_eq_top_of_conj1Trivial (F := F) p,
    conj1Trivial_of_conjInvariants_eq_top (F := F) p⟩

end L20261018

#print axioms L20261018.conjInvariants_eq_top_of_conj1Trivial
#print axioms L20261018.conj1Trivial_of_conjInvariants_eq_top
#print axioms L20261018.conj1Trivial_iff_conjInvariants_eq_top
