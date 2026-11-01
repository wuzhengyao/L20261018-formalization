import L20261018.Ch2.Hensel.Inertia.Step022_cd_p_inertia_unconditional
import TauCeti.Topology.Algebra.Group.Profinite.ProP.H1Dual

/-!
# S43 R23（**B1 的前半 ＋ GMS `lemma-7.5` 的机检形态**）

## 1. GMS `lemma-7.5`：`H^i(I, C) = 0`（`i ≥ 2`）——（★）解锁的那一格

`Hyp506` 的诚实边界①记着：GMS §7 的证明体**经由（★）**，具体是 `lemma-7.5`
（`H^i(I,C) = 0, i ≥ 2`），其证明一句「`I` 的 ℓ-Sylow ≅ `ℤ_ℓ`」。
现在（★）已无条件（`Hyp516`／`Hyp517`），本件把这条**显式机检**：

```
H^i(inertiaLoc F, M) = 0   （i ≥ 2，M 为 ℓ-primary 挠离散模，作用任意）
```

这正是 `inertiaLoc_subsingleton_Hq` 的命名化 —— **GMS §7 证明体对（★）的依赖已消除**。
（要造的仍是残数映射 `r` 本身及其两条性质，那是 GMS §7 的实质内容，不是（★）的推论。）

## 2. B1：**野惯性没有 `p`-特征**（`Hom_cont(P_K, μ_p) = 0`）

`PROMPT-S43` §2.6 指出 B1（`Finite (H¹(I, μ_p))`）的关键是 **`Hom_cont(P_K, μ_p) = 0`**（`p ≠ char κ`）。
本件机检它，走**度数论证**（比 `ker` 路线短）：

```
F : P_K →ₜ* Multiplicative (ZMod p)
  ⟹ F.ker 开（靶离散有限）⟹ I_K 的 pro-q 性给 F.range 是 q-群（IsProP.isPGroup_range）
  ⟹ 又 F.range ≤ ZMod p ⟹ |F.range| ∣ p
  ⟹ q^n = |F.range| ∈ {1, p}，而 q ≠ p ⟹ |F.range| = 1 ⟹ F = 1
```

⟹ `Subsingleton (continuousZModDual p ↥P_K)`。

## 诚实边界

* §1 是**命名化**：它把「GMS §7 对（★）的依赖」显式化，**不**给出 `KnrResidueObligation`。
* §2 只给 `Hom_cont(P_K, μ_p) = 0`（**野部分**）。B1 的另一半 ——
  `H¹(I, μ_p)` 是 **1 维**、由 `res_I(π)` 生成（`ASSUMPTIONS.md` R941 记的最小缺口）—— **未做**。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti
open scoped TauCeti.zHat

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **`↥(inertiaLoc F)` 在任意 `ZMod n` 上的平凡作用**（与 `Hyp517` 同款，供 §1 用）。 -/
local instance trivialActionZModInertiaLoc' (n : ℕ) :
    DistribMulAction ↥(inertiaLoc F) (ZMod n) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的 `ContinuousSMul`。 -/
local instance trivialContinuousSMulInertiaLoc' (n : ℕ) :
    ContinuousSMul ↥(inertiaLoc F) (ZMod n) where
  continuous_smul := continuous_snd

/-- ★★★★★ **GMS `lemma-7.5`**（`H^i(I,C) = 0`，`i ≥ 2`），**无条件** ——
（★）解锁的那一格。`I = Gal(F^s/F_nr)`（战役载体），`C` 为 `p`-primary 挠离散模。

对应 `raw/gms.tex` 的 `lemma:7.5`：**其证明正是「`I` 的 `p`-Sylow ≅ `ℤ_p`」**，
而后者已由 `Hyp516`／`Hyp517` 无条件机检。 -/
theorem inertiaLoc_Hq_eq_zero (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (p : ℕ) [Fact p.Prime] (hpq : p.Coprime q)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ↥(inertiaLoc F) M] [ContinuousSMul ↥(inertiaLoc F) M]
    (hM : IsPPrimaryTorsion p M) {i : ℕ} (hi : 2 ≤ i) :
    Subsingleton (continuousCohomology i (ofDiscreteModule ℤ ↥(inertiaLoc F) M)) :=
  inertiaLoc_subsingleton_Hq q p hpq M hM hi

/-- ★★★★★ **GMS `lemma-7.5` 的 `C = μ_p` 形态**（`i ≥ 2`），无条件。 -/
theorem inertiaLoc_Hq_zmod_eq_zero (q p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q] (hq : q.Prime)
    (hpq : p.Coprime q) {i : ℕ} (hi : 2 ≤ i) :
    Subsingleton (continuousCohomology i
      (ofDiscreteModule ℤ ↥(inertiaLoc F) (ZMod p))) := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact inertiaLoc_subsingleton_Hq q p hpq (ZMod p)
    (isPPrimaryTorsion_of_module_zmod p (ZMod p)) hi

/-! ### B1：野惯性没有 `p`-特征 -/

/-- ★★★★★ **`Hom_cont(P_K, μ_p) = 0`**（`p ≠ char κ`）：野惯性是 pro-`q`（`q = char κ`），
而 `μ_p` 是 `p`-群，两素数不同 ⟹ 唯一连续同态是平凡的。

**这就是 `PROMPT-S43` §2.6 记的 B1 第一块砖。** -/
theorem continuousZModDual_wildInertia_subsingleton {K : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) q] (hpq : p ≠ q) :
    Subsingleton (continuousZModDual p ↥(wildInertiaSubgroup K)) := by
  -- 所有连续同态都是 `1`
  have htriv : ∀ G : ↥(wildInertiaSubgroup K) →ₜ* Multiplicative (ZMod p), G = 1 := by
    intro G
    -- 核开（靶离散有限）
    let K' : Subgroup ↥(wildInertiaSubgroup K) :=
      ((G : ↥(wildInertiaSubgroup K) →* Multiplicative (ZMod p))).ker
    have hker : IsOpen (K' : Set ↥(wildInertiaSubgroup K)) := by
      have hset : (K' : Set ↥(wildInertiaSubgroup K))
          = (G : ↥(wildInertiaSubgroup K) → Multiplicative (ZMod p)) ⁻¹' {1} := rfl
      rw [hset]
      exact G.continuous_toFun.isOpen_preimage {1} (isOpen_discrete _)
    -- 像同时是 `q`-群与 `p`-群的子群 ⟹ 平凡
    have hq : IsPGroup q ↥((G : ↥(wildInertiaSubgroup K) →* Multiplicative (ZMod p))).range :=
      (isProP_wildInertiaSubgroup K q).isPGroup_range _ hker
    haveI : Finite (Multiplicative (ZMod p)) := inferInstance
    have hdvd : Nat.card ↥((G : ↥(wildInertiaSubgroup K) →* Multiplicative (ZMod p))).range ∣ p := by
      have h1 := Subgroup.card_subgroup_dvd_card
        ((G : ↥(wildInertiaSubgroup K) →* Multiplicative (ZMod p))).range
      have h2 : Nat.card (Multiplicative (ZMod p)) = p := by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, ZMod.card]
      rwa [h2] at h1
    haveI hfin : Finite ↥((G : ↥(wildInertiaSubgroup K) →* Multiplicative (ZMod p))).range :=
      inferInstance
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).1 hq
    -- `q^n ∣ p` ⟹ `q^n = 1`（因 `q ≠ p`）
    have hqn : q ^ n ∣ p := hn ▸ hdvd
    have hqn1 : q ^ n = 1 := by
      rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (q ^ n) hqn with h | h
      · exact h
      · exfalso
        have hpdvd : p ∣ q := by
          refine (Fact.out : p.Prime).dvd_of_dvd_pow (m := q) (n := n) ?_
          rw [h]
        rcases (Nat.dvd_prime (Fact.out : q.Prime)).1 hpdvd with h1 | h1
        · exact (Fact.out : p.Prime).ne_one h1
        · exact hpq h1
    have hcard1 : Nat.card ↥((G : ↥(wildInertiaSubgroup K) →* Multiplicative (ZMod p))).range = 1 := by
      rw [hn, hqn1]
    -- 像平凡 ⟹ `G = 1`
    ext x
    have hx : (G : ↥(wildInertiaSubgroup K) →* Multiplicative (ZMod p)) x
        ∈ (G : ↥(wildInertiaSubgroup K) →* Multiplicative (ZMod p)).range :=
      ⟨x, rfl⟩
    haveI hsub : Subsingleton ↥((G : ↥(wildInertiaSubgroup K) →* Multiplicative (ZMod p))).range :=
      (Nat.card_eq_one_iff_unique.1 hcard1).1
    have := Subsingleton.elim
      (⟨(G : ↥(wildInertiaSubgroup K) →* Multiplicative (ZMod p)) x, hx⟩ :
        ↥((G : ↥(wildInertiaSubgroup K) →* Multiplicative (ZMod p))).range)
      ⟨1, ((G : ↥(wildInertiaSubgroup K) →* Multiplicative (ZMod p))).range.one_mem⟩
    simpa using congrArg Subtype.val this
  refine ⟨fun f g => ?_⟩
  have hf : (Additive.toMul f : ↥(wildInertiaSubgroup K) →ₜ* Multiplicative (ZMod p)) = 1 :=
    htriv _
  have hg : (Additive.toMul g : ↥(wildInertiaSubgroup K) →ₜ* Multiplicative (ZMod p)) = 1 :=
    htriv _
  rw [← Additive.toMul.injective.eq_iff, hf, hg]

end L20261018

#print axioms L20261018.inertiaLoc_Hq_eq_zero
#print axioms L20261018.inertiaLoc_Hq_zmod_eq_zero
#print axioms L20261018.continuousZModDual_wildInertia_subsingleton
