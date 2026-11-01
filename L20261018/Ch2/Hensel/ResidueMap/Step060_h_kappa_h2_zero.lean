import L20261018.Ch2.Hensel.ResidueMap.Step058_residue_span_canonical_carrier

/-!
# S51 R5：**档 ⑥ 的最终形态** —— `hκ` 就是字面的 `H²(κ, μ_p) = 0`

## 0 为什么再改一次载体（这是最后一次）

| 版本 | 剩余侧载体 | `hκ` 的字面样子 | 问题 |
|---|---|---|---|
| `Hyp610` | `muPQuot (Γ⧸I) p`（自造） | `Subsingleton (H²(Γ⧸I, Z/p))` | 载体自造 |
| `Hyp612` | `continuounCohomology 2 ((muP F p).quotientToInvariants I)` | `Subsingleton (H²(Γ⧸I, μ_p))` | 载体是 `Γ⧸I`，**不是 `κ`** |
| **`Hyp614`（本件）** | **`GaloBase.H2 K p`（`K` ＝ 剩余域）** | **`Subsingleton (H²(K, μ_p))`** | **无**——这就是 Tsen 的字面陈述 |

本件把剩余侧换成**剩余域 `K` 的绝对 Galois 群**：给出
`φ : Γ_F →ₜ* Γ_K`（「Hensel 剩余 Galois 对应」，**具名假设**），则
```
infl₁ := map φ coeffId 1 : H¹(K, μ_p) →ₗ H¹(F, μ_p)
infl₂ := map φ coeffId 2 : H²(K, μ_p) →ₗ H²(F, μ_p)
```
**两端载体都是 `GaloBase` 自己的**，`hκ : Subsingleton (GaloBase.H2 K p)` **逐字**是
「`H²(K, μ_p) = 0`」——即 **Tsen 域**（`cd_p(K) ≤ 1`）的判据。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| `coeffIdHomK` | `res φ (muP K p) ⟶ muP F p` 的系数恒等（平凡作用 ⟹ `rfl` 级） |
| **`inflH1`／`inflH2`** | ★★★★★ `φ`-诱导的 inflation（`K` 侧 → `F` 侧） |
| `cupK` | `K` 侧杯积 |
| **`inflH2_cupK`** | ★★★★★ `infl₂(a⌣b) = infl₁a ⌣ infl₁b`（`TopPairing.cup_map`） |
| **`range_inflH2_eq_bot_of_subsingleton`** | ★★★★ `H²(K,μ_p)=0 ⟹ range infl₂ = ⊥` |
| **`residueSpan_le_range_inflH2`** | ★★★★★ `(CI) ⟹ residueSpan ≤ range infl₂` |
| **`ch4TameSymbolHyp_of_subsingleton_H2`** | ★★★★★★★ **档 ⑥ 最终版**：`(CI)` ＋ `H²(κ,μ_p)=0` ⟹ `Ch4TameSymbolHyp` |
| **`ch4TameSymbolHyp_of_subsingleton_H2_residueField`** | ★★★★★★★ 上一行取 `K := IsLocalRing.ResidueField ↥𝒪[F]` 的**具体形态** |
| `residueSpan_eq_bot_of_subsingleton_H2` | 接入 `Hyp611` 正规形 `residueSpan = ⊥` |

## 2 与 `Hyp612` 的关系

`Hyp612` 用 `ContinuousCohomology.infl`（`Γ⧸I` 商上的原生 inflation）；本件用
`ContinuousCohomology.map φ`（把 `Γ_K` 拉回 `Γ_F`）。**两者都不自造载体**，
但只有本件的 `hκ` 是「`κ` 上的」陈述。`Hyp612` 因此在档 ⑥ 的位置上记 `○-SUPERSEDED`
（其 `invPairing` 等仍作为 `Γ⧸I` 形态的备件保留）。

## 3 诚实边界（本件**不**宣称已证 `(CI)` 或 Tsen）

* `φ : Γ_F →ₜ* Γ_K`（Hensel 剩余 Galois 对应）是**具名假设**，见 `wiki/hyp-residue-galois.md`。
  它等价于「存在以 `I = inertia` 为核的满射」；对 `F` Hensel 这是标准事实，但**未形式化**。
* `hκ : Subsingleton (GaloBase.H2 K p)` 是**假设**：`K = ℂ(t)` 时由 Tsen 定理成立，
  而「Tsen ⟹ `cd ≤ 1`」**不在 mathlib**（见 `wiki/hyp-tsen.md` 待建）。
* `(CI)` 是**假设**（`wiki/hyp-ci-residue.md`；阻断 = `F̄` 的赋值延拓 ＋ 一般 Hensel 惯性子群）。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section ResidueGalois

variable {F K : Type} [Field F] [Field K]
variable (p : ℕ) [Fact p.Prime]
variable (φ : ContinuousMonoidHom (AbsoluteGaloisGroup F) (AbsoluteGaloisGroup K))

/-- 系数恒等：`res φ (muP K p) ⟶ muP F p`（两侧都是平凡作用 ⟹ `rfl` 级）。 -/
noncomputable def coeffIdHomK :
    TopRep.res (φ : AbsoluteGaloisGroup F →* AbsoluteGaloisGroup K) (GaloBase.muP K p)
      ⟶ GaloBase.muP F p :=
  TopRep.ofHom
    { toContinuousLinearMap := ContinuousLinearMap.id (ZMod p) (ZMod p)
      isIntertwining' _ := by ext; rfl }

/-- ★★★★★ **`K` 侧 → `F` 侧 inflation（1 次）**：`H¹(K, μ_p) →ₗ H¹(F, μ_p)`。 -/
noncomputable def inflH1 : GaloBase.V K p →ₗ[ZMod p] GaloBase.V F p :=
  (ContinuousCohomology.map φ (coeffIdHomK p φ) 1).hom.toLinearMap

/-- ★★★★★ **`K` 侧 → `F` 侧 inflation（2 次）**：`H²(K, μ_p) →ₗ H²(F, μ_p)`。 -/
noncomputable def inflH2 : GaloBase.H2 K p →ₗ[ZMod p] GaloBase.H2 F p :=
  (ContinuousCohomology.map φ (coeffIdHomK p φ) 2).hom.toLinearMap

/-- `K` 侧杯积 `H¹(K) × H¹(K) → H²(K)`。 -/
noncomputable def cupK :
    GaloBase.V K p →ₗ[ZMod p] GaloBase.V K p →ₗ[ZMod p] GaloBase.H2 K p :=
  (GaloBase.muPairing K p).cup 1 1

/-- ★★★★★ **inflation 保持 `(1,1)` 杯积**（`TopPairing.cup_map`，NSW (1.4.2)）。 -/
theorem inflH2_cupK (a b : GaloBase.V K p) :
    inflH2 p φ (cupK (K := K) p a b)
      = GaloBase.cup (K := F) (p := p) (inflH1 p φ a) (inflH1 p φ b) := by
  have h := (GaloBase.muPairing K p).cup_map
    (G := AbsoluteGaloisGroup K) (H := AbsoluteGaloisGroup F)
    (GaloBase.muPairing F p) φ (coeffIdHomK p φ) (coeffIdHomK p φ) (coeffIdHomK p φ)
    (fun x y => rfl) 1 1 a b
  show (ContinuousCohomology.map φ (coeffIdHomK p φ) (1 + 1)).hom
      ((GaloBase.muPairing K p).cup 1 1 a b) = _
  rw [h]
  rfl

/-- ★★★★ **`H²(K,μ_p) = 0 ⟹ range infl₂ = ⊥`**。 -/
theorem range_inflH2_eq_bot_of_subsingleton (h : Subsingleton (GaloBase.H2 K p)) :
    LinearMap.range (inflH2 p φ) = ⊥ := by
  rw [LinearMap.range_eq_bot]
  refine LinearMap.ext fun x => ?_
  have hx : x = 0 := @Subsingleton.elim (GaloBase.H2 K p) h x 0
  rw [hx]
  simp

end ResidueGalois

/-! ## 档 ⑥ 最终版 -/

section TameResidue

variable {F K : Type} [Field F] [Field K]
variable {F' : Type} [Field F'] [ValuativeRel F'] [TopologicalSpace F']
  [HenselianRing ↥𝒪[F'] (IsLocalRing.maximalIdeal ↥𝒪[F'])]

variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F' p]
variable {v : F'ˣ →* Multiplicative ℤ} {π : F'ˣ}
variable (K' : Type) [Field K']
variable (φ' : ContinuousMonoidHom (AbsoluteGaloisGroup F') (AbsoluteGaloisGroup K'))

/-- ★★★★★ **`(CI)` ⟹ `residueSpan ≤ range infl₂`**。 -/
theorem residueSpan_le_range_inflH2
    (hpF : IsUnit (p : F'))
    (hCI : ∀ y : VKG F' p v hpF,
      ∃ a : GaloBase.V K' p, inflH1 p φ' a = (y : GaloBase.V F' p)) :
    residueSpan (GaloBase.cup (K := F') (p := p)) (valLinOf (F := F') (p := p) v hpF)
      ≤ LinearMap.range (inflH2 p φ') := by
  rw [residueSpan, Submodule.span_le]
  rintro _ ⟨⟨y, z⟩, rfl⟩
  obtain ⟨a, ha⟩ := hCI y
  obtain ⟨b, hb⟩ := hCI z
  refine ⟨cupK (K := K') p a b, ?_⟩
  rw [inflH2_cupK, ha, hb]

/-- ★★★★★★★ **档 ⑥ 最终版**：`(CI)` ＋ **`H²(K, μ_p) = 0`** ⟹ `Ch4TameSymbolHyp`。

`hκ` 的**字面**就是 `H²(K, μ_p) = 0`——`K` 取剩余域时即 Tsen 条件 `cd_p(K) ≤ 1`。 -/
theorem ch4TameSymbolHyp_of_subsingleton_H2
    {ζ : F'} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : ↥𝒪[F'])) (hpF : IsUnit (p : F'))
    (hv : ValCompat (F := F') v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hCI : ∀ y : VKG F' p v hpF,
      ∃ a : GaloBase.V K' p, inflH1 p φ' a = (y : GaloBase.V F' p))
    (hκ : Subsingleton (GaloBase.H2 K' p)) :
    Ch4TameSymbolHyp (F := F') p (v := v) (π := π) hpF := by
  have hbot : LinearMap.range (inflH2 p φ') = ⊥ :=
    range_inflH2_eq_bot_of_subsingleton p φ' hκ
  have hspan : residueSpan (GaloBase.cup (K := F') (p := p))
      (valLinOf (F := F') (p := p) v hpF) ≤ LinearMap.range (inflH2 p φ') :=
    residueSpan_le_range_inflH2 (F' := F') (K' := K') p φ' hpF hCI
  refine (ch4TameSymbolHyp_iff_disjoint (F := F') (p := p) (v := v) (π := π)
    hζ hp hpF hv hπ hp2).mpr ?_
  rw [show residueSpan (GaloBase.cup (K := F') (p := p)) (valLinOf (F := F') (p := p) v hpF)
    = ⊥ from le_bot_iff.mp (hbot ▸ hspan)]
  exact disjoint_bot_right

/-- ★★★★★ **接入 `Hyp611` 的正规形**：档 ⑥ 最终版 ⟹ `residueSpan = ⊥`。 -/
theorem residueSpan_eq_bot_of_subsingleton_H2
    (hpF : IsUnit (p : F'))
    (hCI : ∀ y : VKG F' p v hpF,
      ∃ a : GaloBase.V K' p, inflH1 p φ' a = (y : GaloBase.V F' p))
    (hκ : Subsingleton (GaloBase.H2 K' p)) :
    residueSpan (GaloBase.cup (K := F') (p := p)) (valLinOf (F := F') (p := p) v hpF) = ⊥ :=
  le_bot_iff.mp <|
    (range_inflH2_eq_bot_of_subsingleton p φ' hκ) ▸
      residueSpan_le_range_inflH2 (F' := F') (K' := K') p φ' hpF hCI

/-- ★★★★★★★ **具体形态**：`K := IsLocalRing.ResidueField ↥𝒪[F]`。

`hκ : Subsingleton (H²(κ, μ_p))`，`φ : Γ_F →ₜ* Gal(κ̄/κ)` 为具名假设（Hensel 剩余 Galois 对应）。 -/
theorem ch4TameSymbolHyp_of_subsingleton_H2_residueField
    {ζ : F'} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : ↥𝒪[F'])) (hpF : IsUnit (p : F'))
    (hv : ValCompat (F := F') v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (φ : ContinuousMonoidHom (AbsoluteGaloisGroup F')
      (AbsoluteGaloisGroup (IsLocalRing.ResidueField ↥𝒪[F'])))
    (hCI : ∀ y : VKG F' p v hpF,
      ∃ a : GaloBase.V (IsLocalRing.ResidueField ↥𝒪[F']) p,
        inflH1 p φ a = (y : GaloBase.V F' p))
    (hκ : Subsingleton (GaloBase.H2 (IsLocalRing.ResidueField ↥𝒪[F']) p)) :
    Ch4TameSymbolHyp (F := F') p (v := v) (π := π) hpF :=
  ch4TameSymbolHyp_of_subsingleton_H2 (F' := F')
    (K' := IsLocalRing.ResidueField ↥𝒪[F']) p φ hζ hp hpF hv hπ hp2 hCI hκ

end TameResidue

end L20261018

#print axioms L20261018.coeffIdHomK
#print axioms L20261018.inflH1
#print axioms L20261018.inflH2
#print axioms L20261018.inflH2_cupK
#print axioms L20261018.range_inflH2_eq_bot_of_subsingleton
#print axioms L20261018.residueSpan_le_range_inflH2
#print axioms L20261018.ch4TameSymbolHyp_of_subsingleton_H2
#print axioms L20261018.residueSpan_eq_bot_of_subsingleton_H2
#print axioms L20261018.ch4TameSymbolHyp_of_subsingleton_H2_residueField
