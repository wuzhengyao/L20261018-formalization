import L20261018.Ch2.Hensel.ResidueMap.Step006_tame_pi_u_of
set_option maxHeartbeats 2000000
open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField
namespace L20261018

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- `V = H¹(G_F, μ_p)` 上 `p • y = 0`（系数环是 `ZMod p`）。 -/
theorem p_smul_V_eq_zero (y : GaloBase.V F p) : p • y = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) p y, ZMod.natCast_self, zero_smul]

/-- `(a^n) = n • (a)`（Kummer 类的幂律）。 -/
theorem kummerClass_pow (hp : IsUnit (p : F)) (x : Fˣ) (n : ℕ) :
    KummerBridge.kummerClass F p hp (x ^ n) = n • KummerBridge.kummerClass F p hp x := by
  induction n with
  | zero => simp [KummerBridge.kummerClass_eq_zero_iff]
  | succ k ih =>
    rw [pow_succ, KummerV.kummerClass_mul (F := F) (p := p) hp, ih, succ_nsmul]

/-- **`(π^p) = 0`**：`p` 次幂的 Kummer 类为零（这是「吸收 `p` 次幂」的种子）。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-kummer-valuation quote="单位约化诱导同构 $\mathcal O_F^\times/\mathcal O_F^{\times p} \simeq K^\times/K^{\times p}$；"
theorem kummerClass_pow_prime (hp : IsUnit (p : F)) (π : Fˣ) :
    KummerBridge.kummerClass F p hp (π ^ p) = 0 := by
  rw [kummerClass_pow (F := F) (p := p) hp, p_smul_V_eq_zero]

/-- **`(a · b^p) = (a)`**：乘一个 `p` 次幂不改 Kummer 类。 -/
theorem kummerClass_mul_pow_eq (hp : IsUnit (p : F)) (a b : Fˣ) :
    KummerBridge.kummerClass F p hp (a * b ^ p) = KummerBridge.kummerClass F p hp a := by
  rw [KummerV.kummerClass_mul (F := F) (p := p) hp,
    kummerClass_pow_prime (F := F) (p := p) hp b, add_zero]

end L20261018
#print axioms L20261018.p_smul_V_eq_zero
#print axioms L20261018.kummerClass_pow
#print axioms L20261018.kummerClass_pow_prime
#print axioms L20261018.kummerClass_mul_pow_eq
