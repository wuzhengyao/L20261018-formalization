import Hyp756

/-!
# S69 R3：A-2 **收口** —— `hd_infl` 的最终形态（不再带 `hpq`）

两件事：

1. **`hpq` 由 `hcop` 推出**：`¬ ringChar 𝓀[F] ∣ p` 不是独立假设——`CharP 𝓀[F] q` ＋ `p.Coprime q`
   ＋ `Fact p.Prime` ＋ `NeZero p` 就够（`ringChar.eq` ＋ `Nat.Prime.dvd_iff_eq`）。
   这样 `Hyp749.unramifiedKummer` 的 `hpq` 输入**自动兑现**。
2. **`hd_infl` 与 `F5` 解耦**：`d = F5 ∘ ∂²` ⟹ `d (cup y z) = F5 (∂² (cup y z)) = F5 0 = 0`。
   故 `hd_infl` **对任意** `F5 : H¹(Γ⧸I,H¹(I,μ_p)) →ₗ VKG` 都成立——
   `F5` 的构造只需服务 `hd_cup_pi`（C3）。

## 交付

| 声明 | 内容 |
|---|---|
| `not_ringChar_dvd_of_coprime` | ★★★★ `p.Coprime q ⟹ ¬ ringChar 𝓀[F] ∣ p` |
| `deltaTwoGaloBase'_cup_eq_zero'` | `y z ∈ VKG ⟹ ∂² (cup y z) = 0`（**无 `hpq`**） |
| **`hd_infl_of_linear`** | ★★★★★ `∀ F5, (F5 ∘ ∂²) (cup y z) = 0`（`hd_infl` 的最终形态） |
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
attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★ **`p.Coprime q` ⟹ `¬ ringChar 𝓀[F] ∣ p`**（`hpq` 不是独立假设）。 -/
theorem not_ringChar_dvd_of_coprime (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q) : ¬ ringChar 𝓀[F] ∣ p := by
  have hq : ringChar 𝓀[F] = q := ringChar.eq _ _
  rw [hq]
  intro hdvd
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hdvd
    exact absurd hdvd (by simp [NeZero.ne p])
  have hprime : Nat.Prime q := (CharP.char_is_prime_or_zero (𝓀[F]) q).resolve_right hq0
  have hpq : p = q := ((Fact.out : Nat.Prime p).dvd_iff_eq hprime.ne_one).mp hdvd
  rw [← hpq] at hcop
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop dvd_rfl) (Fact.out : Nat.Prime p).ne_one

variable (q : ℕ) [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
  (hcop : p.Coprime q)

/-- `y z ∈ ker v̄ ⟹ ∂² (y ∪ z) = 0`（`hpq` 已由 `hcop` 兑现）。 -/
theorem deltaTwoGaloBase'_cup_eq_zero'
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    (hpF : IsUnit (p : F))
    {v : Fˣ →* Multiplicative ℤ} (hv : ValCompat (F := F) v)
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (y z : VKG F p v hpF) :
    deltaTwoGaloBase' (F := F) p q hcop
      (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0 :=
  deltaTwoGaloBase'_cup_eq_zero (F := F) (p := p) (q := q) (hcop := hcop)
    hpF (not_ringChar_dvd_of_coprime (F := F) (p := p) q hcop) hv hπ y z

/-- ★★★★★ **`hd_infl` 的最终形态**（与 `F5` 解耦）：`d := F5 ∘ ∂²` 时
`d (cup y z) = 0` 对**任意**线性 `F5` 成立。 -/
theorem hd_infl_of_linear
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    (hpF : IsUnit (p : F))
    {v : Fˣ →* Multiplicative ℤ} (hv : ValCompat (F := F) v)
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (F5 : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))
      →ₗ[ZMod p] VKG F p v hpF)
    (y z : VKG F p v hpF) :
    (F5.comp (AddMonoidHom.toZModLinearMap p
        (deltaTwoGaloBase' (F := F) p q hcop)))
      (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0 := by
  show F5 (deltaTwoGaloBase' (F := F) p q hcop
      (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p))) = 0
  rw [deltaTwoGaloBase'_cup_eq_zero' (F := F) (p := p) (q := q) (hcop := hcop) hpF hv hπ y z]
  exact map_zero F5

end L20261018

#print axioms L20261018.not_ringChar_dvd_of_coprime
#print axioms L20261018.deltaTwoGaloBase'_cup_eq_zero'
#print axioms L20261018.hd_infl_of_linear
