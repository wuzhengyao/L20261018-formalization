import L20261018.Hyp19
import L20261018.Hyp14
import L20261018.Hyp20
import L20261018.A
/-!
> **R902 注（用户指示）**：本文件原有的 `theorem_3_2_2_kummer`（带 `ind`/`hind` 参数）已**移除**；
> 论文 3.2(2) 的机检陈述现由 `Hyp86.theorem_3_2_2_kummer'`（不带参数）承担。

# Chapter 3 at the paper's own objects

`A.lean` proves the six statements of Chapter 3 for an abstract `BiKummerData`. `Hyp20.lean`
realises that structure at the paper's cohomology (`biKummerDataKummer`: the real cup product of
`μ_p` with itself, and the Kummer classes `(a₁), (a₂) ∈ H¹(F, μ_p)`). This file restates the
statements at those objects, so that no abstract data remains — the hypotheses are exactly the
paper's ( `(a₁) ∪ (a₂) ≠ 0`, `μ_p ⊂ F`, `p` odd where used).

The interesting case is 3.3(3): it is proved here **directly** in the continuous model by
`GaloCup.lemma_3_3_3_continuous` (`Hyp14.lean`), i.e. from associativity and graded commutativity of
the canonical cup product, rather than through the abstract statement.
-/

open TauCeti ContCohomology

set_option maxHeartbeats 1000000

namespace L20261018

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **Lemma 3.1(1) for the paper's objects**: `U ∩ U^⊥ = 0`, where `U = ⟨(a₁), (a₂)⟩` and
`U^⊥ = {x : x ∪ (a₁) = x ∪ (a₂) = 0}`. -/
-- @source file=raw/L20261018.tex locator=label:lem:orthogonal quote="两个子空间满足 $U\cap U^\perp=0$；"
theorem lemma_3_1_1_kummer (hp : IsUnit (p : F)) (hp2 : p ≠ 2) (a1 a2 : Fˣ)
    (hne : GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1)
      (KummerBridge.kummerClass F p hp a2) ≠ 0) :
    (biKummerDataKummer F p hp a1 a2 hne).U ⊓ (biKummerDataKummer F p hp a1 a2 hne).Uperp
      = ⊥ := by
  haveI := neZero_two_zmod (p := p) hp2
  exact BiKummerData.lemma_3_1_1 (biKummerDataKummer F p hp a1 a2 hne)

/-- **Lemma 3.1(3) for the paper's objects**: `rank Φ ≥ 2`, i.e. `(a₁), (a₂)` together with their
cup product span at least two dimensions — the nondegeneracy that makes the `U`/`U^⊥` picture
non-vacuous. -/
-- @source file=raw/L20261018.tex locator=label:lem:orthogonal quote="共同杯积映射满足 $\rank(\Phi)\ge2$。"
theorem lemma_3_1_3_kummer (hp : IsUnit (p : F)) (hp2 : p ≠ 2) (a1 a2 : Fˣ)
    (hne : GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1)
      (KummerBridge.kummerClass F p hp a2) ≠ 0) :
    (2 : Cardinal) ≤ Module.rank (ZMod p)
      ↥(biKummerDataKummer F p hp a1 a2 hne).Phi.range := by
  haveI := neZero_two_zmod (p := p) hp2
  exact BiKummerData.lemma_3_1_3 (biKummerDataKummer F p hp a1 a2 hne)

-- 注（R902）：本文件原有的 `theorem_3_2_2_kummer`（带 `ind`/`hind` 参数）已按用户指示**移除**；
-- 论文 3.2(2) 的机检陈述现由 `Hyp86.theorem_3_2_2_kummer'`（不带参数）承担。

/-- **Lemma 3.3(3) for the paper's objects**: `U^⊥ ⊆ R`, where `R` is the kernel of cupping with
`[D] = (a₁) ∪ (a₂)`. Proved **directly in the continuous model** — from associativity and graded
commutativity of the canonical cup product (`GaloCup.lemma_3_3_3_continuous`, `Hyp14.lean`), not
through the abstract statement. -/
-- @source file=raw/L20261018.tex locator=label:lem:basic-inclusions quote="共同正交空间满足 $U^\perp\subseteq R$。"
theorem lemma_3_3_3_kummer (hp : IsUnit (p : F)) (a1 a2 : Fˣ) (v : GaloBase.V F p)
    (h1 : GaloBase.cup (K := F) (p := p) v (KummerBridge.kummerClass F p hp a1) = 0)
    (h2 : GaloBase.cup (K := F) (p := p) v (KummerBridge.kummerClass F p hp a2) = 0) :
    GaloCup.cupH F p v
      (GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1)
        (KummerBridge.kummerClass F p hp a2)) = 0 := by
  have h := GaloCup.lemma_3_3_3_continuous F p (KummerBridge.kummerClass F p hp a1)
    (KummerBridge.kummerClass F p hp a2) (KummerBridge.kummerClass F p hp a2) 0 v h1 h2
  simpa using h

end L20261018
