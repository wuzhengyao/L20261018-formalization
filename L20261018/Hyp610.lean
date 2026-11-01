import Hyp389
import Hyp449
import Hyp609
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality
import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialGroup

/-!
# S51 R1：**档 ⑥** 的载体 —— `(CI)` ⟹ `residueSpan ≤ range infl₂` ⟹ `(R2)`

## 0 本件推翻的 S50 读数（`PROMPT-S51` §2.4）

`PROMPT-S51-NEW-WORKSPACE.md` §2.4 写：

> `#check @ContinuousCohomology.inf` → **unknown identifier** ⟹ `continuousCohomology` 层无 inflation

**这是按名字搜的失败**（`CLAUDE.md` 规则 23／L46：禁按裸名字搜）。真名是 **`infl`**（带 `l`）：

```
@ContinuousCohomology.infl : (N : Subgroup G) → (X : TopRep R G) → (n : ℕ) →
  continuousCohomology n (X.quotientToInvariants N) ⟶ continuousCohomology n X
```

`Inflation/Comparison.lean` 的 `explicitIso_infl`／`explicitIso_infl2` 正是
「canonical `infl` = 显式 `explicitInfl1/2`」的运输方阵 ⟹ **S50 R2 的"只能在显式余圈层做"不成立**。
本件因此**不需要** `explicitCoeff1/2`＋`Hyp609` 的系数簿记链，直接在主层构造。

同理，杯积相容**不需要** `explicitInfl2_explicitCup11`：库内
`TauCeti.TopPairing.cup_map`（NSW (1.4.2)）与 `cup_infl`（NSW (1.5.3)(iii)）在主层已给。

## 1 路线（`PROMPT-S51` §④ 序 1–5 的合并版）

用 `ContinuousCohomology.map` 直接造 `Γ`-层 inflation：取
`φ := Γ ↠ Γ⧸I`（`Subgroup.quotientMkContinuousMonoidHom`）、系数取**平凡** `ZMod p` 表示
`muPQuot (Γ⧸I) p`，系数映射取恒等（平凡作用的固定点就是全体，故它是 `I`-不变点的自然同一）。

```
infl1Res : H¹(Γ⧸I, μ_p) →ₗ H¹(Γ, μ_p)          -- = map φ id 1
infl2Res : H²(Γ⧸I, μ_p) →ₗ H²(Γ, μ_p)          -- = map φ id 2
cupRes   : H¹(Γ⧸I) →ₗ H¹(Γ⧸I) →ₗ H²(Γ⧸I)      -- = trivialPairing.cup 1 1
```

`cup_map` 立刻给 **`infl2Res (cupRes a b) = cup (infl1Res a) (infl1Res b)`**（本件第 8 条）。

## 2 本件交付

| 声明 | 内容 |
|---|---|
| `muPQuot`／`muPQuot_ρ` | `Q` 上系数 `ZMod p` 的**平凡**表示（`GaloBase.muP` 的任意群版） |
| `trivialPairing` | 其乘法系数配对（`GaloBase.muPairing` 的 `Q` 版） |
| `ResH1Type`／`ResH2Type` | 剩余侧载体 `H¹(Γ⧸I, μ_p)`／`H²(Γ⧸I, μ_p)` |
| `infl1Res`／`infl2Res` | ★★★★★ 主层 inflation |
| `cupRes` | 剩余侧杯积 `H¹ × H¹ → H²` |
| **`infl2Res_cupRes`** | ★★★★★ **inflation 保持 `(1,1)` 杯积**（`cup_map` 直出） |
| **`range_infl2Res_eq_bot_of_subsingleton`** | ★★★★ `Subsingleton H²(Γ⧸I,μ_p) ⟹ range infl₂ = ⊥` |
| **`residueSpan_le_range_infl2Res`** | ★★★★★ `(CI) ⟹ residueSpan ≤ range infl₂` |
| **`ch4TameSymbolHyp_of_subsingleton_H2_residue`** | ★★★★★★ **档 ⑥**：`(CI)` ＋ `H²(κ,μ_p)=0` ⟹ `Ch4TameSymbolHyp` |
| `subsingleton_resH2Type_top` | 假设类的**非空见证**（L1＋L10①）：`I = ⊤` 时 `H²(Γ⧸⊤,μ_p) = 0` |

## 3 诚实边界（两面都写）

* **`(CI)` 本件只作假设**：`ker v̄ = range(infl₁)`（逐点形态 `hCI`）。它的 `⇒` 方向
  （`v x = 0 ⟹ x ∈ range infl₁`）就是「`F_nr` 上 Hensel ＋ `κ̄` 可分闭 ⟹ 单位类不分歧」，
  与 `H²(I,μ_p)=0`（G1 墙）同族，**不在库内**。S50 计划的「用 `Hyp608` 直接得 `⇒`」**低估**了：
  还需要 `H¹(Γ⧸I,μ_p) ≅ κ^×/κ^×p`（`κ` 上的 Kummer 理论 ＝ `Γ⧸I ≅ G_κ`），而后者**未形式化**。
* **`H²(κ,μ_p)=0` 本件作假设**（`hκ`）：档 ⑥ 的形态与 `Hyp302`（有限档）同层。
  `κ = ℂ(t)` 是 Tsen 域 ⟹ 它落在档 ⑥ 内，但「Tsen ⟹ `cd ≤ 1`」**不在 mathlib**，
  须另立具名假设（独立目标，`PROMPT-S51` §1.4 已如此登记）。
* **载体同一性**：本件的 `H²(Γ⧸I, μ_p)` 是 `continuousCohomology 2 (muPQuot (Γ⧸I) p)`。
  它与标准 `infl` 的载体 `continuousCohomology 2 ((muP F p).quotientToInvariants I)` 相差
  「`I`-不变点 ＝ 全体」，其同一性**尚未机检**（`Infl/Comparison` 的
  `coeffMap_ofDiscreteModuleQuotient_comp_infl` 是可能的桥），登记为后续轮。
  与 `GaloBase.H2 κ p` 的等同需要 `Γ⧸I ≅ Gal(κ̄/κ)`（Hensel 剩余 Galois 对应），同样未形式化。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

/-! ## 1 平凡表示的任意群版 -/

section TrivialRep

variable (Q : Type) [Group Q] [TopologicalSpace Q] (p : ℕ) [Fact p.Prime]

/-- `Q` 上系数 `ZMod p` 的**平凡**（拓扑）表示；`GaloBase.muP` 的任意群版。 -/
noncomputable def muPQuot : TopRep (ZMod p) Q :=
  letI : DiscreteTopology (ZMod p) := ZMod.instDiscreteTopology
  letI : ContinuousSMul (ZMod p) (ZMod p) := ⟨continuous_of_discreteTopology⟩
  TopRep.of (ContRepresentation.trivial (ZMod p) Q (ZMod p))

/-- 平凡作用：每个元素都是固定点。 -/
lemma muPQuot_ρ (g : Q) (x : (muPQuot Q p).V) : (muPQuot Q p).ρ g x = x := rfl

/-- 乘法系数配对（`GaloBase.muPairing` 的任意群版）。 -/
noncomputable def trivialPairing : TopPairing (muPQuot Q p) (muPQuot Q p) (muPQuot Q p) where
  bil := (LinearMap.mk₂ (ZMod p) (fun x y : ZMod p => x * y)
    (by intro x y z; ring)
    (by intro c x y; simp only [smul_eq_mul]; ring)
    (by intro x y z; ring)
    (by intro c x y; simp only [smul_eq_mul]; ring)
    : ZMod p →ₗ[ZMod p] ZMod p →ₗ[ZMod p] ZMod p)
  cont := by
    haveI : DiscreteTopology (muPQuot Q p).V := ZMod.instDiscreteTopology
    exact continuous_of_discreteTopology
  equivariant := by
    intro g x y
    rw [muPQuot_ρ, muPQuot_ρ, muPQuot_ρ]

end TrivialRep

/-! ## 2 剩余侧的载体与 inflation -/

section Residue

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-- 剩余侧 `H¹`：`H¹(Γ⧸I, μ_p)`（`μ_p` 平凡作用）。 -/
noncomputable abbrev ResH1Type : Type :=
  ↥(continuousCohomology 1 (muPQuot (AbsoluteGaloisGroup F ⧸ I) p)).toModuleCat

/-- 剩余侧 `H²`：`H²(Γ⧸I, μ_p)`。 -/
noncomputable abbrev ResH2Type : Type :=
  ↥(continuousCohomology 2 (muPQuot (AbsoluteGaloisGroup F ⧸ I) p)).toModuleCat

/-- 系数的恒等映射：`I`-不变点就是全体（平凡作用），故是 `Γ`-模射。 -/
noncomputable def coeffIdHom :
    TopRep.res (Subgroup.quotientMkContinuousMonoidHom I : AbsoluteGaloisGroup F →* _)
      (muPQuot (AbsoluteGaloisGroup F ⧸ I) p) ⟶ GaloBase.muP F p :=
  TopRep.ofHom
    { toContinuousLinearMap := ContinuousLinearMap.id (ZMod p) (ZMod p)
      isIntertwining' _ := by ext; rfl }

/-- ★★★★★ **`Γ`-层 inflation（1 次）**：`H¹(Γ⧸I, μ_p) →ₗ H¹(Γ, μ_p)`。 -/
noncomputable def infl1Res : ResH1Type (F := F) p I →ₗ[ZMod p] GaloBase.V F p :=
  (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I) (coeffIdHom (F := F) p I) 1).hom

/-- ★★★★★ **`Γ`-层 inflation（2 次）**：`H²(Γ⧸I, μ_p) →ₗ H²(Γ, μ_p)`。 -/
noncomputable def infl2Res : ResH2Type (F := F) p I →ₗ[ZMod p] GaloBase.H2 F p :=
  (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I) (coeffIdHom (F := F) p I) 2).hom

/-- 剩余侧杯积 `H¹(Γ⧸I) × H¹(Γ⧸I) → H²(Γ⧸I)`。 -/
noncomputable def cupRes :
    ResH1Type (F := F) p I →ₗ[ZMod p] ResH1Type (F := F) p I →ₗ[ZMod p] ResH2Type (F := F) p I :=
  (trivialPairing (AbsoluteGaloisGroup F ⧸ I) p).cup 1 1

/-- ★★★★★ **inflation 保持 `(1,1)` 杯积**（NSW (1.4.2)，`TopPairing.cup_map`
配 `coeffIdHom`）：`infl₂(a ⌣ b) = infl₁ a ⌣ infl₁ b`。

这一条**取代** S50 计划里的 `explicitInfl2_explicitCup11`（那条是显式余圈层版本）。 -/
theorem infl2Res_cupRes (a b : ResH1Type (F := F) p I) :
    infl2Res (F := F) p I (cupRes (F := F) p I a b)
      = GaloBase.cup (K := F) (p := p) (infl1Res (F := F) p I a) (infl1Res (F := F) p I b) := by
  have h := (trivialPairing (AbsoluteGaloisGroup F ⧸ I) p).cup_map
    (G := AbsoluteGaloisGroup F ⧸ I) (H := AbsoluteGaloisGroup F)
    (GaloBase.muPairing F p)
    (Subgroup.quotientMkContinuousMonoidHom I) (coeffIdHom (F := F) p I) (coeffIdHom (F := F) p I)
    (coeffIdHom (F := F) p I) (fun x y => rfl) 1 1 a b
  show (ContinuousCohomology.map _ (coeffIdHom (F := F) p I) (1 + 1)).hom
      ((trivialPairing (AbsoluteGaloisGroup F ⧸ I) p).cup 1 1 a b) = _
  rw [h]
  rfl

/-- ★★★★ **`Subsingleton` ⟹ `range infl₂ = ⊥`**（档 ⑥ 的引擎）。 -/
theorem range_infl2Res_eq_bot_of_subsingleton (h : Subsingleton (ResH2Type (F := F) p I)) :
    LinearMap.range (infl2Res (F := F) p I) = ⊥ := by
  rw [LinearMap.range_eq_bot]
  refine LinearMap.ext fun x => ?_
  have hx : x = 0 := @Subsingleton.elim (ResH2Type (F := F) p I) h x 0
  rw [hx]
  simp

/-- ★★★★★ **`(CI)` ⟹ `residueSpan ≤ range infl₂`**。

`(CI)` 取逐点形态：`ker v̄` 的每个元素都是 `infl₁` 的像。则单位杯积
`cup y z = infl₂(cupRes a b)`，故落在 `range infl₂` 里。 -/
theorem residueSpan_le_range_infl2Res [HasEnoughRootsOfUnity F p]
    {v : Fˣ →* Multiplicative ℤ} (hpF : IsUnit (p : F))
    (hCI : ∀ y : VKG F p v hpF,
      ∃ a : ResH1Type (F := F) p I, infl1Res (F := F) p I a = (y : GaloBase.V F p)) :
    residueSpan (GaloBase.cup (K := F) (p := p))
        (valLinOf (F := F) (p := p) v hpF)
      ≤ LinearMap.range (infl2Res (F := F) p I) := by
  rw [residueSpan, Submodule.span_le]
  rintro _ ⟨⟨y, z⟩, rfl⟩
  obtain ⟨a, ha⟩ := hCI y
  obtain ⟨b, hb⟩ := hCI z
  refine ⟨cupRes (F := F) p I a b, ?_⟩
  rw [infl2Res_cupRes, ha, hb]

end Residue

/-! ## 3 档 ⑥：`(CI)` ＋ `H²(κ,μ_p) = 0` ⟹ `(R2)` -/

section TameResidue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★★ **档 ⑥**（覆盖 Tsen 域，含论文主例 `κ = ℂ(t)`）：

若 **(CI)** `ker v̄ = range(infl₁ : H¹(Γ⧸I,μ_p) → H¹(Γ,μ_p))` 且 **`H²(Γ⧸I, μ_p) = 0`**，
则第 4 章的具名假设 `Ch4TameSymbolHyp` 成立。

**为什么值钱**：此前五档（有限 `Hyp302`／`p`-可除 `Hyp430`／循环 `Hyp430`／完备 `Hyp290`／
`dim ker v̄ ≤ 1` `Hyp607`）**都不覆盖 `κ = ℂ(t)`**；而 Tsen 域恰由 `H²(κ,μ_p) = 0` 刻画。 -/
theorem ch4TameSymbolHyp_of_subsingleton_H2_residue
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]
    (hCI : ∀ y : VKG F p v hpF,
      ∃ a : ResH1Type (F := F) p I, infl1Res (F := F) p I a = (y : GaloBase.V F p))
    (hκ : Subsingleton (ResH2Type (F := F) p I)) :
    Ch4TameSymbolHyp p (v := v) (π := π) hpF := by
  have hbot : LinearMap.range (infl2Res (F := F) p I) = ⊥ :=
    range_infl2Res_eq_bot_of_subsingleton (F := F) (p := p) (I := I) hκ
  have hspan : residueSpan (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) ≤ LinearMap.range (infl2Res (F := F) p I) :=
    residueSpan_le_range_infl2Res (F := F) (p := p) (v := v) (I := I) hpF hCI
  refine (ch4TameSymbolHyp_iff_disjoint (F := F) (p := p) (v := v) (π := π)
    hζ hp hpF hv hπ hp2).mpr ?_
  rw [show residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
    = ⊥ from le_bot_iff.mp (hbot ▸ hspan)]
  exact disjoint_bot_right

end TameResidue

/-! ## 4 假设类的非空见证（L1 ＋ L10①） -/

section Witness

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-- ★★★★ **`Subsingleton (H²(Γ⧸I,μ_p))` 不是空假设**：取 `I = ⊤`，`Γ⧸⊤` 平凡，
故 `H²(Γ⧸⊤, μ_p) = 0`（平凡群的连续上同调在正次数消失，`TrivialGroup`）。

⚠ **残余**：档 ⑥ 需要**两条**假设同时成立（`hCI` 与 `hκ`）。`I = ⊤` 时 `range infl₁ ⊆ range 0 = ⊥`
（因 `H¹(Γ⧸⊤,μ_p) = 0`），故 `hCI` 退化为 `ker v̄ = ⊥`。两条同时成立的一般见证
＝「Tsen 域 ＋ `(CI)`」，**未在本件给出**（Tsen 不在库内）。本件只机检 `hκ` 一侧非空。 -/
theorem subsingleton_resH2Type_top :
    Subsingleton (ResH2Type (F := F) p (⊤ : Subgroup (AbsoluteGaloisGroup F))) := by
  haveI : Subsingleton (AbsoluteGaloisGroup F ⧸ (⊤ : Subgroup (AbsoluteGaloisGroup F))) :=
    QuotientGroup.subsingleton_quotient_top
  exact ContinuousCohomology.subsingleton_continuousCohomology_succ_of_subsingleton
    (muPQuot (AbsoluteGaloisGroup F ⧸ ⊤) p) 1

end Witness

end L20261018

#print axioms L20261018.muPQuot
#print axioms L20261018.trivialPairing
#print axioms L20261018.coeffIdHom
#print axioms L20261018.infl1Res
#print axioms L20261018.infl2Res
#print axioms L20261018.cupRes
#print axioms L20261018.infl2Res_cupRes
#print axioms L20261018.range_infl2Res_eq_bot_of_subsingleton
#print axioms L20261018.residueSpan_le_range_infl2Res
#print axioms L20261018.ch4TameSymbolHyp_of_subsingleton_H2_residue
#print axioms L20261018.subsingleton_resH2Type_top
