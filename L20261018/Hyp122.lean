import Hyp121
set_option maxHeartbeats 2000000
open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField
namespace L20261018

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- `toAdd (1 : Multiplicative ℤ) = 0`（`rfl`）。 -/
lemma toAdd_one' : Multiplicative.toAdd (1 : Multiplicative ℤ) = 0 := rfl

/-- `x = 1 ↔ toAdd x = 0`（`ofAdd`／`toAdd` 是同一函数，故 `rfl` ＋ `simpa` 即可）。 -/
lemma toAdd_eq_one_iff {x : Multiplicative ℤ} :
    x = 1 ↔ Multiplicative.toAdd x = 0 := by
  constructor
  · intro h; rw [h]; exact toAdd_one'
  · intro h
    have h2 : Multiplicative.ofAdd (Multiplicative.toAdd x) = Multiplicative.ofAdd (0 : ℤ) := by
      rw [h]
    simpa using h2

/-- 对偶计算：`toAdd (v (a · (π^k)^p)) = toAdd (v a) + p·k`。 -/
lemma toAdd_val_mul_pow {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ)) (a : Fˣ) (k : ℕ) :
    Multiplicative.toAdd (TauCeti.normalizedValuation F (a * (π ^ k) ^ p))
      = Multiplicative.toAdd (TauCeti.normalizedValuation F a) + (p : ℤ) * k := by
  have hmul : TauCeti.normalizedValuation F (a * (π ^ k) ^ p)
      = TauCeti.normalizedValuation F a * TauCeti.normalizedValuation F ((π ^ k) ^ p) := map_mul _ _ _
  rw [hmul, toAdd_mul', map_pow, toAdd_pow', toAdd_val_pi_pow (F := F) (hπ := hπ) (k := k)]

/-- **`\ker\bar v` 恰是单位类的集合**（`prop:prelim-kummer-valuation`(1) 的载体版）：
`\bar v(y) = 0` 的类都可由**单位** `u`（整数赋值 `0`，即 `v u = 1`）代表。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-kummer-valuation quote="单位约化诱导同构 $\mathcal O_F^\times/\mathcal O_F^{\times p} \simeq K^\times/K^{\times p}$；"
theorem exists_unit_rep (hp : IsUnit (p : F)) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    {y : GaloBase.V F p} (hy : (valLin F p hp) y = 0) :
    ∃ u : Fˣ, TauCeti.normalizedValuation F u = 1 ∧
      KummerBridge.kummerClass F p hp u = y := by
  obtain ⟨a, rfl⟩ := KummerV.kummerClass_surjective (F := F) (p := p) (hp := hp) y
  have hva0 : valOfUnit F p a = 0 := by
    rw [← valLin_kummerClass (F := F) (p := p) (hp := hp) (a := a)]
    exact hy
  have hva : ((Multiplicative.toAdd (TauCeti.normalizedValuation F a) : ℤ) : ZMod p) = 0 := hva0
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd
    (Multiplicative.toAdd (TauCeti.normalizedValuation F a)) p).mp hva
  rcases Int.lt_or_le m 0 with hlt | hge
  · -- `m < 0`：`u := a * (π ^ m.natAbs) ^ p`
    have hk : (m.natAbs : ℤ) = -m := by
      rw [← Int.natAbs_neg m]
      exact Int.natAbs_of_nonneg (by omega)
    have hmz : (m : ℤ) = -(m.natAbs : ℤ) := by omega
    refine ⟨a * (π ^ m.natAbs) ^ p, ?_, ?_⟩
    · rw [toAdd_eq_one_iff,
        toAdd_val_mul_pow (F := F) (p := p) (hπ := hπ) (a := a) (k := m.natAbs), hm]
      nth_rewrite 1 [hmz]
      ring
    · rw [kummerClass_mul_pow_eq (F := F) (p := p) (hp := hp) (a := a) (b := π ^ m.natAbs)]
  · -- `0 ≤ m`：`u := a * ((π ^ m.natAbs) ^ p)⁻¹`
    have hmz : (m : ℤ) = (m.natAbs : ℤ) := (Int.natAbs_of_nonneg hge).symm
    refine ⟨a * ((π ^ m.natAbs) ^ p)⁻¹, ?_, ?_⟩
    · rw [toAdd_eq_one_iff,
        toAdd_val_mul_pow_inv (F := F) (p := p) (hπ := hπ) (a := a) (k := m.natAbs), hm]
      nth_rewrite 1 [hmz]
      ring
    · rw [KummerV.kummerClass_mul (F := F) (p := p) (hp := hp),
        KummerV.kummerClass_inv (F := F) (p := p) (hp := hp),
        kummerClass_pow (F := F) (p := p) (hp := hp), p_smul_V_eq_zero (F := F) (p := p)]
      simp

end L20261018
#print axioms L20261018.exists_unit_rep
