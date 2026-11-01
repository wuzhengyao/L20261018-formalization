import TauCeti.FieldTheory.GaloisCohomology.Kummer

/-!
# Restriction of Kummer classes: the exact kernel

`Hyp6.lean` proves the easy direction of campaign item (e): if the image of `a : Kˣ` in `Lˣ` is an
`n`-th power, then the Kummer class of `a` restricts to `1`. This file proves the **converse**, so
that the kernel of `res_{L/K}` on Kummer classes is *exactly* "the units that become `n`-th powers
in `L`":

`kummerRes (kummerMap a) = 1 ↔ ∃ b : Lˣ, algebraMap a = bⁿ`.

That is the precise reduction of (e) to field theory: the paper's `prop:bi-kummer-kernel` becomes
the statement `Eˣ ∩ Fˣ = F^{×p}⟨a₁,a₂⟩` for the bi-Kummer extension `E = F(a₁^{1/p}, a₂^{1/p})`,
with no further cohomology.

The same statement on power classes, `kummerIso`-transport of `TauCeti.kummerIso_res`, exhibits the
restriction as the natural map `Kˣ⧸(Kˣ)ⁿ → Lˣ⧸(Lˣ)ⁿ`, whose kernel is the image of
`Lˣ`-`n`-th powers.
-/

open TauCeti

/-- **The kernel of restriction on Kummer classes**: `res_{L/K}` kills the Kummer class of `a`
exactly when `a` becomes an `n`-th power in `L`. This is the converse of Hyp6's
`kummerRes_kummerMap_eq_one_of_isPow` and makes that lemma an `iff`. -/
theorem kummerRes_kummerMap_eq_one_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (n : ℕ) (σ : L →ₐ[K] SeparableClosure K) (hn : IsUnit (n : K)) (a : Kˣ) :
    kummerRes K n L σ (kummerMap K n hn a) = 1 ↔
      ∃ b : Lˣ, Units.map (algebraMap K L).toMonoidHom a = b ^ n := by
  rw [kummerRes_kummerMap K n L σ hn a,
    kummerMap_eq_one_iff (K := L) (n := n) (by simpa using hn.map (algebraMap K L))]
  exact exists_congr fun b => eq_comm

/-- **Restriction is the natural map of power classes.** On `x : Kˣ⧸(Kˣ)ⁿ`, restriction of
Kummer classes corresponds, under the Kummer isomorphisms of `K` and `L`, to the map induced by
`K → L` on power classes. -/
theorem kummerRes_kummerIso_eq_one_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (n : ℕ) (σ : L →ₐ[K] SeparableClosure K) (hn : IsUnit (n : K))
    (x : powerClassQuotient Kˣ n) :
    kummerRes K n L σ (kummerIso K n hn x) = 1 ↔
      powerClassMap n (Units.map (algebraMap K L).toMonoidHom) x = 1 := by
  rw [kummerIso_res, MulEquiv.map_eq_one_iff]
