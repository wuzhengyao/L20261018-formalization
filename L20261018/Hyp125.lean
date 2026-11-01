import L20261018.Hyp124
set_option maxHeartbeats 2000000
open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField
namespace L20261018

/-- **载体桥第 1 段**：`muNRep` 载体的杯积零 ⟹ `trivialFp`（`cupFp`）载体的杯积零。
用 `muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup`（`Symbol.lean:297`）搬运。 -/
theorem cupFp_unit_unit_eq_zero {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (tr : ↑(continuousCohomology 2 (ClassFieldTheory.muNRep n K)).toModuleCat ≃+ ZMod n)
    (hp : ¬ ringChar 𝓀[K] ∣ n) {a b : Kˣ}
    (ha : a ∈ unitFiltration K 0) (hb : b ∈ unitFiltration K 0) :
    TauCeti.cupFp n (Field.absoluteGaloisGroup K)
        (ClassFieldTheory.muNRepCohomologyEquivTrivialFp n K hζ 1
          (ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit a))
        (ClassFieldTheory.muNRepCohomologyEquivTrivialFp n K hζ 1
          (ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit b)) = 0 := by
  rw [← ClassFieldTheory.muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup
    (hζ := hζ) (x := ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit a)
    (y := ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit b),
    cup_unit_unit_eq_zero (hζ := hζ) (tr := tr) hp ha hb, map_zero]

end L20261018
#print axioms L20261018.cupFp_unit_unit_eq_zero
