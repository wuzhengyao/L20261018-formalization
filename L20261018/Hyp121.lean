import L20261018.Hyp120
set_option maxHeartbeats 2000000
open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField
namespace L20261018

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- `toAdd (x⁻¹) = -toAdd x`（`rfl`；`Multiplicative.toAdd` 是 `AddEquiv`，故逆对应负）。 -/
lemma toAdd_inv' (x : Multiplicative ℤ) :
    Multiplicative.toAdd x⁻¹ = - Multiplicative.toAdd x := rfl

/-- `toAdd (v (π^k)) = k`。 -/
lemma toAdd_val_pi_pow {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ)) (k : ℕ) :
    Multiplicative.toAdd (TauCeti.normalizedValuation F (π ^ k)) = (k : ℤ) := by
  have h1 : Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ)) = 1 := rfl
  rw [map_pow, hπ, toAdd_pow', h1]
  ring

/-- **关键计算**：`toAdd (v (a · ((π^k)^p)⁻¹)) = toAdd (v a) - p·k`（全程在 `ℤ` 层面）。 -/
lemma toAdd_val_mul_pow_inv {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ)) (a : Fˣ) (k : ℕ) :
    Multiplicative.toAdd (TauCeti.normalizedValuation F (a * ((π ^ k) ^ p)⁻¹))
      = Multiplicative.toAdd (TauCeti.normalizedValuation F a) - (p : ℤ) * k := by
  have hmul : TauCeti.normalizedValuation F (a * ((π ^ k) ^ p)⁻¹)
      = TauCeti.normalizedValuation F a * (TauCeti.normalizedValuation F ((π ^ k) ^ p))⁻¹ := by
    rw [map_mul, map_inv]
  rw [hmul, toAdd_mul', toAdd_inv', map_pow, toAdd_pow',
    toAdd_val_pi_pow (F := F) hπ k]
  ring

end L20261018
#print axioms L20261018.toAdd_inv'
#print axioms L20261018.toAdd_val_pi_pow
#print axioms L20261018.toAdd_val_mul_pow_inv
