import TauCeti.NumberTheory.ClassFieldTheory.Local.TameSymbol
set_option maxHeartbeats 2000000
open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField
namespace L20261018

/-- **两个单位类的杯积为零**（`hUU` 的 TauCeti 载体版）：
由 `localSymbol` 的单位-单位定理 ＋ `localSymbol = tr ∘ cup` ＋ `tr` 单射得到。

数学上正确：单位类的杯积落在**不分歧**部分，而剩余域有限 ⟹ `H²(𝔽_q, μ_n^{⊗2}) = 0`
（平凡作用时 `H² = M^G/NM = M/M`）。 -/
theorem cup_unit_unit_eq_zero {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (tr : ↑(continuousCohomology 2 (ClassFieldTheory.muNRep n K)).toModuleCat ≃+ ZMod n)
    (hp : ¬ ringChar 𝓀[K] ∣ n) {a b : Kˣ}
    (ha : a ∈ unitFiltration K 0) (hb : b ∈ unitFiltration K 0) :
    ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit a)
        (ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit b) = 0 := by
  have h := ClassFieldTheory.localSymbol_kummerClass_eq_zero_of_mem_unitFiltration
    (hζ := hζ) (tr := tr) hp ha hb
  rw [ClassFieldTheory.localSymbol_apply] at h
  exact tr.injective (by rw [h, map_zero])

end L20261018
#print axioms L20261018.cup_unit_unit_eq_zero
