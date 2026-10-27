import L20261018.Hyp19
import L20261018.A
/-!
# The paper's bi-Kummer data, from the real Kummer classes

> **R902 注（用户指示）**：本文件原有的 `theorem_3_2_1_kummer`（带 `ind`/`hind` 参数）已**移除**；
> 论文 3.2(1) 的机检陈述现由 `Hyp86.theorem_3_2_1_kummer'`（不带参数）承担。

`A.lean` proves the six statements of Chapter 3 for an abstract `BiKummerData`, and already
instantiates it at the real TauCeti cup product (`L20261018.galoBiKummer`), leaving only

* the two classes `a₁, a₂ : V = H¹(F, μ_p)`, and
* the paper's standing hypothesis `(a₁) ∪ (a₂) ≠ 0`

as inputs. This file supplies the classes: `KummerBridge.kummerClass` (`Hyp19.lean`) transports
`TauCeti.kummerMap` to `GaloBase.V F p` along the coefficient identification
`μ_p ≃ ZMod p` and the model comparison `H¹(ℤ-coefficients) ≃ continuousCohomology 1 (muP)`.

The result `biKummerDataKummer` is the paper's `BiKummerData` with **no abstract data left**: the
only hypothesis is `(a₁) ∪ (a₂) ≠ 0` (plus `μ_p ⊂ F`), which is precisely what
`thm:hs-tate-exact-sequences` assumes.
-/

open TauCeti ContCohomology

set_option maxHeartbeats 1000000

namespace L20261018

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **The paper's bi-Kummer data from two units.** The classes are the Kummer classes
`(a₁), (a₂) ∈ H¹(F, μ_p)`; the cup product is `GaloBase.cup`; skew-symmetry is `cup_skew`; and the
nonvanishing of `(a₁) ∪ (a₂)` is the paper's hypothesis. -/
noncomputable def biKummerDataKummer (hp : IsUnit (p : F)) (a1 a2 : Fˣ)
    (hne : GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1)
      (KummerBridge.kummerClass F p hp a2) ≠ 0) :
    BiKummerData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p) :=
  galoBiKummer (K := F) (p := p) (KummerBridge.kummerClass F p hp a1)
    (KummerBridge.kummerClass F p hp a2) hne

/-- The two classes of the realised data are the Kummer classes. -/
@[simp]
theorem biKummerDataKummer_a1 (hp : IsUnit (p : F)) (a1 a2 : Fˣ)
    (hne : GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1)
      (KummerBridge.kummerClass F p hp a2) ≠ 0) :
    (biKummerDataKummer F p hp a1 a2 hne).a1 = KummerBridge.kummerClass F p hp a1 := (rfl)

@[simp]
theorem biKummerDataKummer_a2 (hp : IsUnit (p : F)) (a1 a2 : Fˣ)
    (hne : GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1)
      (KummerBridge.kummerClass F p hp a2) ≠ 0) :
    (biKummerDataKummer F p hp a1 a2 hne).a2 = KummerBridge.kummerClass F p hp a2 := (rfl)

/-- For `p` prime and `p ≠ 2`, `2` is invertible in `ZMod p`. -/
theorem neZero_two_zmod (hp2 : p ≠ 2) : NeZero (2 : ZMod p) := ⟨by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).1 h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  exact hp2 (by omega)⟩

end L20261018
