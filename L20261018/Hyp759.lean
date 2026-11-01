import L20261018.Hyp758
import L20261018.Hyp521

/-!
# S71 R1：墙 1 的第一步 —— **战役载体 `H¹(I,μ_p)` 是一维的**

`F5` 第一半的路线（`PROMPT-S71` §0bis 的 W1–W4）第 1–2 步：

```
W1  H¹(I,μ_p) ≅ Hom_cont(I, μ_p)            库内 H1EquivOfSmulEqSelf（htriv := fun _ _ => rfl）
W2  Nat.card (Hom_cont(I, μ_p)) = p         Hyp521.OneDim.hom_cont_inertiaLoc_equiv（GMS (7.3)）
⟹  Nat.card (H¹(I,μ_p)) = p                 ★本件
```

**为什么这一步有用**：W2 只给了 `Hom_cont(I,μ_p)` 的阶；而 `∂²` 的**目标系数**是 `H1 ↥I (ZMod p)`
（`TauCeti.ContCohomology.H1`），两者的桥正是 `H1EquivOfSmulEqSelf`。
有了 `Nat.card = p`，W3（「共轭作用＝乘某个 `λ ∈ (ℤ/p)^×`」）与 W4（`λ = 1`）才有载体。

## 交付

| 声明 | 内容 |
|---|---|
| `natCard_hom_cont_inertiaLoc_eq` | `Nat.card (↥I →ₜ* Multiplicative (ZMod p)) = p` |
| **`natCard_h1Inertia_eq`** | ★★★★ **`Nat.card (H1 ↥I (ZMod p)) = p`** |
| `h1EquivHom_apply` | W1 的显式式（取值于 `→ₜ*` 形态） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-- ★★★★ **`p ≠ q` 由 `p.Coprime q` 推出**（`q` 是素数时）。 -/
theorem ne_of_coprime (hcop : p.Coprime q) : p ≠ q := by
  rintro rfl
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop dvd_rfl) (Fact.out : Nat.Prime p).ne_one

/-- ★★★★ **`Nat.card (Hom_cont(I, μ_p)) = p`**（`Hyp521.hom_cont_inertiaLoc_equiv` ＋ `ZMod.card`）。 -/
theorem natCard_hom_cont_inertiaLoc_eq (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤) :
    Nat.card (↥(inertiaLoc F) →ₜ* Multiplicative (ZMod p)) = p := by
  rw [Nat.card_congr (OneDim.hom_cont_inertiaLoc_equiv (F := F) p q hpq ζ hζ hgen)]
  simp [ZMod.card]

/-- ★★★★ **`Nat.card (H¹(I,μ_p)) = p`**（W1 的基数十字＋上一条）。

`H1EquivOfSmulEqSelf`（`htriv := fun _ _ => rfl`，即本战役 `↥I` 在 `ZMod p` 上作用平凡）把
`H1 ↥I (ZMod p)` 换成 `Additive (↥I →ₜ* Multiplicative (ZMod p))`，阶不变。 -/
theorem natCard_h1Inertia_eq (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤) :
    Nat.card (H1 ↥(inertiaLoc F) (ZMod p)) = p := by
  have htriv : ∀ (g : ↥(inertiaLoc F)) (m : ZMod p), g • m = m := fun _ _ => rfl
  rw [Nat.card_congr (H1EquivOfSmulEqSelf (G := ↥(inertiaLoc F)) (M := ZMod p) htriv).toEquiv]
  exact natCard_hom_cont_inertiaLoc_eq (F := F) (p := p) (q := q) hpq ζ hζ hgen

end L20261018

#print axioms L20261018.natCard_hom_cont_inertiaLoc_eq
#print axioms L20261018.natCard_h1Inertia_eq
