import L20261018.Ch2.Hensel.TameSymbol.Step005_tame_symbol_hyp_iff_r1_r2
import L20261018.Ch2.Hensel.ResidueMap.Step031_r1_without_bridge_or_completeness

/-!
# S49 R14：**唯一缺口 `(R2)` 的精确边界** —— 残余恰为 `dim ker v̄ ≥ 2`

## 本轮做了什么（对唯一缺口的正面进攻）

`(R2)`（`TameResidueFacts.disjoint`，`Hyp161:96`）的一般情形是本战役**唯一**的数学缺口。
本轮先把它为什么不能一击即中钉死（见 §0），再给出**能证的精确边界**：

### §0 为什么 `(R2)` 不能由 `(R1)` 或任何已机检件直接推出

* **`(R2)` ⟺ `∃ d`**（`Hyp343.exists_residueMap_iff_tameResidueFacts` ＋
  `Hyp432.disjoint_iff_exists_residueMap`）—— 而 `d` 是**要构造的对象**（GS 6.8.5 的 `∂₂`）。
  于是「证 `disjoint`」与「造 `d`」是**同一个圈**，任何直接证法都会回到圈上。
* 破圈的两条路线都被**判死**（本会话 R11 复核）：
  `r_v`／`knumResidueMap` 路线 = **零映射**（`Hyp489`／`Hyp491`）；
  `K_nr` 模层路线 = **载体张冠李戴**（`GS68-LEDGER` §S40.1）。
* 忠实形态 `R2′`（`Hyp389`）**不构成弱化**：战役载体的 `infl` 就是 `(ker valLinOf).subtype`
  （`Hyp540`），故 `R2′` 的第一半 `residueSpan ≤ range infl₂` 平凡，第二半
  `Disjoint (range Φ) (range infl₂)` 与 `(R2)` **同一命题**。
* 因此 `(R2)` 的实质内容 = **载体识别** `H¹(Γ⧸I, H¹(I,μ_p)) ≅ ker v̄`（GS 6.8.9 的驯对偶），
  不是一条可以用 `(R1)` 或交错性挤出来的引理。

### §1 能证的精确边界：**`dim ker v̄ ≤ 1` 时 `(R2)` 是定理**（纯线性代数）

若 `ker v̄` 循环（由 `finrank ≤ 1` 给出），则 `residueSpan = ⊥`：任两元 `y = c•γ`、`z = d•γ`，
故 `cup y z = (cd) • cup γ γ`，而 `cup γ γ = 0`（交错性 ＋ `2 ≠ 0`）。

⟹ `Disjoint (range Φ) ⊥` 平凡 ⟹ 配 `(R1)`（`Hyp319.residuePhi_injective_t1`，**无条件**）
即得 `TameResidueFacts` ⟹ **`Ch4TameSymbolHyp`**。

**这一条不要求 `[Finite κ]`、不要求完备、不要求 `κˣ` 可除** —— 于是把唯一缺口
**精确划在 `dim ker v̄ ≥ 2`**（＝剩余域单位群足够大）上。

### §2 与库内既有件的关系（规则 24 ④ 已核）

`Hyp130.hUU_of_ker_le_one`／`Hyp134` 已给「`ker v̄` 内两元线性相关 ⟹ `UnitsCupVanish`」，
但走 **Kummer 载体**（`KummerBridge.kummerClass`、`unit_pow_dependence`）。
本件的 §1 是它的**纯线性代数重述**（不含 Kummer、不含 `hdep`），
故可用于**任意** `cup`／`val`，并直接喂 `TameResidueFacts`（跳过 `UnitsCupVanish`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

/-! ## §1 抽象层：交错 ＋ `ker` 循环 ⟹ `residueSpan = ⊥` -/

section Abstract

variable {k V H2 : Type*} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup H2] [Module k H2]
variable (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) (π : V)

/-- 交错性 ⟹ `cup γ γ = 0`（需 `2 ≠ 0`）。 -/
theorem cup_self_eq_zero (hskew : ∀ x y, cup x y = - cup y x) (h2 : (2 : k) ≠ 0)
    (γ : V) : cup γ γ = 0 := by
  have hs : cup γ γ = - cup γ γ := hskew γ γ
  have h2s : (2 : k) • cup γ γ = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hs
  exact (smul_eq_zero.mp h2s).resolve_left h2

/-- ★★★★ **`ker val` 循环 ⟹ `residueSpan = ⊥`**（纯线性代数，无 Kummer）。 -/
theorem residueSpan_eq_bot_of_isCyclic (hskew : ∀ x y, cup x y = - cup y x)
    (h2 : (2 : k) ≠ 0)
    {γ : ↥(LinearMap.ker val)} (hγ : ∀ y : ↥(LinearMap.ker val), ∃ c : k, c • γ = y) :
    residueSpan cup val = ⊥ := by
  rw [residueSpan, Submodule.span_eq_bot]
  rintro _ ⟨⟨y, z⟩, rfl⟩
  obtain ⟨c, hc⟩ := hγ y
  obtain ⟨d, hd⟩ := hγ z
  have hy : (y : V) = c • (γ : V) := by rw [← hc]; rfl
  have hz : (z : V) = d • (γ : V) := by rw [← hd]; rfl
  have hγγ : (cup (γ : V)) (γ : V) = 0 := cup_self_eq_zero cup hskew h2 γ
  have h1 : (cup (c • (γ : V))) = c • (cup (γ : V)) := map_smul cup c (γ : V)
  have h2' : (cup (γ : V)) (d • (γ : V)) = d • ((cup (γ : V)) (γ : V)) :=
    LinearMap.map_smul (cup (γ : V)) d (γ : V)
  have hsm : (c • (cup (γ : V))) (d • (γ : V))
      = c • ((cup (γ : V)) (d • (γ : V))) := rfl
  show (cup (y : V)) (z : V) = 0
  rw [hy, hz, h1, hsm, h2', hγγ, smul_zero, smul_zero]

/-- ★★★★★ **`residueSpan = ⊥` ⟹ `TameResidueFacts`**（另一半 `(R1)` 直接给）。 -/
theorem tameResidueFacts_of_residueSpan_eq_bot
    (hphi : Function.Injective (residuePhi cup val π))
    (hbot : residueSpan cup val = ⊥) : TameResidueFacts cup val π where
  phi_injective := hphi
  disjoint := by rw [hbot]; exact disjoint_bot_right

/-- ★★★★★ **`ker val` 循环 ⟹ `TameResidueFacts`**。 -/
theorem tameResidueFacts_of_isCyclic (hskew : ∀ x y, cup x y = - cup y x)
    (h2 : (2 : k) ≠ 0)
    {γ : ↥(LinearMap.ker val)} (hγ : ∀ y : ↥(LinearMap.ker val), ∃ c : k, c • γ = y)
    (hphi : Function.Injective (residuePhi cup val π)) : TameResidueFacts cup val π :=
  tameResidueFacts_of_residueSpan_eq_bot cup val π hphi
    (residueSpan_eq_bot_of_isCyclic cup val hskew h2 hγ)

/-- ★★★★ **`finrank (ker val) ≤ 1` ⟹ `residueSpan = ⊥`**（把循环性从维数取出）。 -/
theorem residueSpan_eq_bot_of_finrank_le_one [FiniteDimensional k ↥(LinearMap.ker val)]
    (hskew : ∀ x y, cup x y = - cup y x) (h2 : (2 : k) ≠ 0)
    (hfr : Module.finrank k ↥(LinearMap.ker val) ≤ 1) : residueSpan cup val = ⊥ := by
  by_cases htriv : Subsingleton ↥(LinearMap.ker val)
  · rw [residueSpan, Submodule.span_eq_bot]
    rintro _ ⟨⟨y, z⟩, rfl⟩
    have hy : y = 0 := Subsingleton.elim _ _
    have hz : z = 0 := Subsingleton.elim _ _
    simp [hy, hz]
  · rw [not_subsingleton_iff_nontrivial] at htriv
    haveI := htriv
    have hpos : 0 < Module.finrank k ↥(LinearMap.ker val) := Module.finrank_pos
    have h1 : Module.finrank k ↥(LinearMap.ker val) = 1 := by omega
    obtain ⟨γ, hγ0⟩ := exists_ne (0 : ↥(LinearMap.ker val))
    refine residueSpan_eq_bot_of_isCyclic cup val hskew h2 (γ := γ) ?_
    intro y
    have htop : k ∙ γ = ⊤ := (finrank_eq_one_iff_of_nonzero γ hγ0).mp h1
    have hy : y ∈ k ∙ γ := by rw [htop]; trivial
    exact Submodule.mem_span_singleton.mp hy

end Abstract

/-! ## §2 Galo 载体：`finrank (ker v̄) ≤ 1` ⟹ `TameResidueFacts` ⟹ `Ch4TameSymbolHyp` -/

section Galo

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **(R2) 在 `dim ker v̄ ≤ 1` 时是定理**（一般 Hensel DVR，无 `[Finite κ]`、无完备性）。 -/
theorem tameResidueFacts_Galo_of_finrank_ker_le_one
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hv : ValCompat (F := F) v)
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (h2 : NeZero (2 : ZMod p))
    [FiniteDimensional (ZMod p) ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit))]
    (hfr : Module.finrank (ZMod p)
      ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit)) ≤ 1) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit)
      (KummerBridge.kummerClass F p hζ.neZero'.out.isUnit π) :=
  tameResidueFacts_of_residueSpan_eq_bot
    (GaloBase.cup (K := F) (p := p))
    (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit) _
    (residuePhi_injective_t1 (F := F) (p := p) (v := v) (π := π) hp hζ hv hπ hp2)
    (residueSpan_eq_bot_of_finrank_le_one (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit)
      (GaloBase.cup_skew (K := F) (p := p)) (NeZero.ne (2 : ZMod p)) hfr)

/-- ★★★★★★ **`Ch4TameSymbolHyp` 在 `dim ker v̄ ≤ 1` 时成立**（一般 Hensel DVR）。

与既有口径**互不蕴含**：
* 不要求 `[Finite 𝓀[F]]`（对比 `Hyp525.ch4TameSymbolHyp_of_finite'`）；
* 不要求 `κˣ` `p`-可除（对比 `ch4TameSymbolHyp_of_divisibleResidue`）；
* 不要求完备性（对比 `Hyp290`／`Hyp606` 的 `[IsNonarchimedeanLocalField]`）；
* 也不经 `UnitsCupVanish`（对比 `Hyp383`／`Hyp385`）。

⟹ 唯一缺口 `(R2)` 被**精确划在 `dim ker v̄ ≥ 2`**。 -/
theorem ch4TameSymbolHyp_of_finrank_ker_le_one
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (h2 : NeZero (2 : ZMod p))
    [FiniteDimensional (ZMod p) ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hpF))]
    (hfr : Module.finrank (ZMod p)
      ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hpF)) ≤ 1) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF := by

  exact (ch4TameSymbolHyp_iff_tameResidueFacts (F := F) (p := p) (v := v) (π := π) hpF hπ).mpr
    (tameResidueFacts_Galo_of_finrank_ker_le_one (F := F) (p := p) (v := v) (π := π)
      hζ hp hv hπ hp2 h2 hfr)

end Galo

end L20261018

#print axioms L20261018.cup_self_eq_zero
#print axioms L20261018.residueSpan_eq_bot_of_isCyclic
#print axioms L20261018.tameResidueFacts_of_residueSpan_eq_bot
#print axioms L20261018.tameResidueFacts_of_isCyclic
#print axioms L20261018.residueSpan_eq_bot_of_finrank_le_one
#print axioms L20261018.tameResidueFacts_Galo_of_finrank_ker_le_one
#print axioms L20261018.ch4TameSymbolHyp_of_finrank_ker_le_one
