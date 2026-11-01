import Hyp513
import TauCeti.NumberTheory.LocalField.Tame.Quotient

/-!
# S43 R19（S3c 的第二半）：**驯模 `ℤ̂^{(p')}(1)` 的 ℓ-部分无限**

## 本件在（★）的哪一格

`Hyp513` 已把 S3c 化为两条关于模型 `M := ℤ̂^{(p')}(1) = lim_{p ∤ m} μ_m(K^{alg})` 的输入：
① `M` procyclic（`Hyp512`）；② `M` 的 **ℓ-部分无限**。

本件证 ②。**不是**用 `S42-S3-ASSESSMENT` §2 设想的「Eisenstein 塔」（路线 β），而是用
**有限层的阶无界** ＋ Sylow 指数判据（**十几行群论**）。

## 机制（本件的全部数学）

设 `P := closedZpowers (ζ ^ᶻ ω_ℓ)` 是 `M` 的 ℓ-Sylow（`Hyp513`），`ζ` 拓扑生成 `M`。
**若 `P` 有限**，取 `k := Nat.card ↥P + 1`，看模型在 `ℓ^k` 层的商 `U := ker(proj_{ℓ^k})`：

```
[M : U] = |μ_{ℓ^k}| = ℓ^k > |P| ≥ |image of P in M/U|          -- 层投影满射 ＋ 像 ≤ P
⟹ [M/U : image of P] = ℓ^k / |image| > 1                        -- card_mul_index
⟹ ℓ ∣ [M/U : image of P] = (P.map (mk' U)).index                -- 指数是 ℓ 的幂且 > 1
```

但 `IsProPSylow.not_dvd_index` 说 `ℓ ∤ (P.map (mk' U)).index`。**矛盾**。

## 关键库内件（全部已移植）

| 件 | 位置 | 作用 |
|---|---|---|
| `PrimeToPTateModule.isLocallyConstant_proj` | `RootsOfUnity/TateModule.lean` | `proj m` 局部常值 ⟹ `ker` 开；**且 `IsLocallyConstant f = ∀ s, IsOpen (f ⁻¹' s)`，不需要目标拓扑** |
| `proj_inertiaTameCharacter_surjective` | `LocalField/Tame/Character.lean:459` | 每层投影满射（经 `inertiaTameCharacter` 搬运） |
| `Subgroup.card_mul_index` | mathlib | `|H| * H.index = |G|` |
| `IsProPSylow.not_dvd_index` | `Profinite/Sylow/Basic.lean` | ℓ ∤ 像的指数 |
| `HasEnoughRootsOfUnity.natCard_rootsOfUnity` | mathlib | `|μ_n| = n` |
| `natCast_ne_zero_of_isUnit` ＋ `IsLocalRing.isUnit_natCast_iff_not_dvd` | `Valuation/ValuativeRel/Basic.lean:75` | 由 `ℓ.Coprime p` 得 `NeZero (ℓ^k : K)` |

## 机检内容

| 声明 | 内容 |
|---|---|
| **`proj_surjective_primeToPTateModule`** | 每层投影满射（`ℓ^k`-层尤其） |
| **`infinite_tameModel_pPart`** | ★★★★★ **模型的 ℓ-部分无限** |
| **`inertiaProPSylowData_tameModel`** | ★★★★★ **S3c 闭合**：`InertiaProPSylowData M ℓ` |

## 诚实边界

* 本件只对**模型** `M ≅ I_K/P_K` 给结论；**尚未**沿 S2（`I_K ↠ I_K/P_K` 的 Sylow 指标）
  与 S4（`inertiaLoc` 载体）搬运到 `I_K`／战役载体。
* `Ch4TameSymbolHyp`（一般 `K`）仍 `∅-open`。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti
open scoped TauCeti.zHat

namespace L20261018

/-- **驯惯性的模型**：`ℤ̂^{(p')}(1) = lim_{p ∤ m} μ_m(K^{alg})`，`p = ringChar κ`。 -/
abbrev TameModel (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Type :=
  PrimeToPTateModule (residueChar K) (AlgebraicClosure K)

/-- **模型在每一层的投影满射**（沿 `inertiaTameCharacter` 的满射性搬运）。 -/
theorem proj_surjective_primeToPTateModule {K : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar K)}) :
    Function.Surjective (PrimeToPTateModule.proj (p := residueChar K)
      (E := AlgebraicClosure K) m) := by
  intro y
  obtain ⟨σ, hσ⟩ := proj_inertiaTameCharacter_surjective K m y
  exact ⟨inertiaTameCharacter K σ, hσ⟩

/-- ★★★★★ **模型的 ℓ-部分无限**。

设 `ζ` 拓扑生成 `M`。则 `closedZpowers (ζ ^ᶻ ω_ℓ)`（`M` 的 ℓ-Sylow，`Hyp513`）无限。
证明：若有限，取 `k = |P| + 1`，`ℓ^k`-层商的指数会给出 `ℓ ∣ (P.map (mk' U)).index`，
与 `IsProPSylow.not_dvd_index` 矛盾。 -/
theorem infinite_tameModel_pPart {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime (residueChar K))
    (ζ : TameModel K) (hζ : closedZpowers ζ = ⊤) :
    Infinite ↥(closedZpowers (ζ ^ᶻ zHat.idem.{0} ℓ)) := by
  rw [← not_finite_iff_infinite]
  -- 反设 `P` 有限
  intro hfin
  haveI := hfin
  set P : Subgroup (TameModel K) := closedZpowers (ζ ^ᶻ zHat.idem.{0} ℓ) with hPdef
  set N : ℕ := Nat.card ↥P with hN
  -- 层 `ℓ ^ (N+1)`
  have hpκ : (residueChar K).Prime :=
    CharP.prime_ringChar (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer)
  have hndvd : ¬ (residueChar K) ∣ ℓ ^ (N + 1) := fun h ↦
    (hpκ.coprime_iff_not_dvd.1 hℓ.symm) (hpκ.dvd_of_dvd_pow h)
  let m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar K)} :=
    ⟨ℓ ^ (N + 1), pow_ne_zero _ (NeZero.ne ℓ), hℓ.pow_left (N + 1)⟩
  -- `U := ker (proj m)` 是开正规子群（`proj m` 局部常值）
  have hker : IsOpen ((PrimeToPTateModule.proj (p := residueChar K)
      (E := AlgebraicClosure K) m).ker : Set (TameModel K)) :=
    PrimeToPTateModule.isLocallyConstant_proj m _
  let U : OpenNormalSubgroup (TameModel K) :=
    ⟨⟨(PrimeToPTateModule.proj (p := residueChar K) (E := AlgebraicClosure K) m).ker, hker⟩,
      MonoidHom.normal_ker _⟩
  letI : U.toSubgroup.Normal := U.isNormal'
  -- 商的阶 = `|μ_{ℓ^{N+1}}| = ℓ^{N+1}`
  have hcardU : Nat.card (TameModel K ⧸ U.toSubgroup) = ℓ ^ (N + 1) := by
    have hkerEq : U.toSubgroup = (PrimeToPTateModule.proj (p := residueChar K)
        (E := AlgebraicClosure K) m).ker := rfl
    rw [hkerEq]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (PrimeToPTateModule.proj (p := residueChar K) (E := AlgebraicClosure K) m)).toEquiv]
    have hrange : (PrimeToPTateModule.proj (p := residueChar K)
        (E := AlgebraicClosure K) m).range = ⊤ :=
      MonoidHom.range_eq_top.2 (proj_surjective_primeToPTateModule m)
    rw [hrange, Nat.card_congr (Subgroup.topEquiv (G := ↥(rootsOfUnity (↑m) (AlgebraicClosure K)))).toEquiv]
    have hs : NeZero ((↑m : ℕ) : K) :=
      ⟨natCast_ne_zero_of_isUnit (IsLocalRing.isUnit_natCast_iff_not_dvd.2 hndvd)⟩
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure K) (↑m)
  -- 像的阶 ≤ `N`
  have himg : Nat.card ↥(Subgroup.map (QuotientGroup.mk' U.toSubgroup) P) ≤ N := by
    rw [hN]
    refine Nat.card_le_card_of_surjective
      (fun x : ↥P => (⟨(QuotientGroup.mk' U.toSubgroup) (x : TameModel K), ?_⟩ :
        ↥(Subgroup.map (QuotientGroup.mk' U.toSubgroup) P))) ?_
    · exact ⟨(x : TameModel K), x.2, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
  -- 指数整除 `ℓ^{N+1}`，且 > 1
  have hdvd : (Subgroup.map (QuotientGroup.mk' U.toSubgroup) P).index ∣ ℓ ^ (N + 1) := by
    rw [← hcardU]
    exact ⟨Nat.card ↥(Subgroup.map (QuotientGroup.mk' U.toSubgroup) P),
      (Subgroup.index_mul_card _).symm⟩
  have hne1 : (Subgroup.map (QuotientGroup.mk' U.toSubgroup) P).index ≠ 1 := by
    intro h1
    have hcm := Subgroup.card_mul_index (Subgroup.map (QuotientGroup.mk' U.toSubgroup) P)
    rw [h1, hcardU, Nat.mul_one] at hcm
    rw [hcm] at himg
    exact absurd himg (not_le.mpr (lt_of_lt_of_le
      (Nat.lt_pow_self (n := N) (Fact.out : ℓ.Prime).one_lt)
      (Nat.pow_le_pow_right (Fact.out : ℓ.Prime).pos (Nat.le_succ N))))
  -- `ℓ ∣ index`
  obtain ⟨q, hq, hqidx⟩ := Nat.exists_prime_and_dvd hne1
  have hqℓ : q = ℓ := ((Nat.dvd_prime Fact.out).1
    (hq.dvd_of_dvd_pow (hqidx.trans hdvd))).resolve_left hq.ne_one
  have hdvdL : ℓ ∣ (Subgroup.map (QuotientGroup.mk' U.toSubgroup) P).index := hqℓ ▸ hqidx
  -- 与 `IsProPSylow.not_dvd_index` 矛盾
  exact (isProPSylow_closedZpowers_zpowHat_idem ℓ ζ hζ).not_dvd_index U hdvdL

/-- ★★★★★ **S3c 闭合**：模型的 `InertiaProPSylowData`（`Hyp513` ＋ 本件的无限性）。 -/
noncomputable def inertiaProPSylowData_tameModel {K : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime (residueChar K))
    (ζ : TameModel K) (hζ : closedZpowers ζ = ⊤) :
    InertiaProPSylowData (TameModel K) ℓ := by
  haveI : Infinite ↥(closedZpowers (ζ ^ᶻ zHat.idem.{0} ℓ)) :=
    infinite_tameModel_pPart ℓ hℓ ζ hζ
  exact inertiaProPSylowData_of_procyclic_group ℓ ζ hζ

end L20261018

#print axioms L20261018.proj_surjective_primeToPTateModule
#print axioms L20261018.infinite_tameModel_pPart
#print axioms L20261018.inertiaProPSylowData_tameModel
