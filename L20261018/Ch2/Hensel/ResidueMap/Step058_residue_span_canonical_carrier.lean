import L20261018.Ch4.Step038_ch4_proof_structure_index
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality

/-!
# S51 R3：**档 ⑥ 的规范载体版** —— 库内 `ContinuousCohomology.infl` ＋ `TopPairing.cup_infl`

## 0 为什么重做（`Hyp610` 的诚实边界 #3）

`Hyp610` 把剩余侧载体取成 `muPQuot (Γ⧸I) p`（平凡表示的**任意群版**），于是 `hκ` 落在
**自造载体**上；审计 §S51-R1 §四·3 登记了这条偏差。本件**消掉它**：直接在
`ContinuousCohomology.infl` 的**原生载体** `(GaloBase.muP F p).quotientToInvariants I` 上做，
杯积相容改用库内 **`TauCeti.TopPairing.cup_infl`**（NSW (1.5.3)(iii)，比 `Hyp610` 的 `cup_map` 更贴题）。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| `RInv`／`RInv_eq_top` | `μ_p` 的 `I`-不变点（平凡作用 ⟹ `= ⊤`） |
| `RInvEquiv`／`RInvEquiv_smul` | `↥RInv ≃ₗ ZMod p`；`Γ⧸I`-作用在其下不动 |
| `invMul`／**`invPairing`** | 不变点上的乘法**系数配对**（`TopPairing`） |
| `invPairing_comp` | 与 `GaloBase.muPairing` 相容（`cup_infl` 的 `hPinv`） |
| **`infl1Canon`／`infl2Canon`** | ★★★★★ 库内 `infl` 的原生形态 |
| **`infl2Canon_cup`** | ★★★★★ `infl₂(a⌣b) = infl₁a ⌣ infl₁b`（`cup_infl` 直出） |
| **`ch4TameSymbolHyp_of_subsingleton_H2canon`** | ★★★★★★ 档 ⑥（规范载体） |
| **`residueSpan_eq_bot_of_subsingleton_H2canon`** | ★★★★★ 接入 `Hyp611` 的正规形 |

## 2 与库内已有件的关系（L47 ④）

`TauCeti.trivialFpQuotientToInvariantsIso`（`TrivialFp.lean:206`）是**同一构造**的 `trivialFp` 版
（含 `DiscreteTopology`／`Finite` 实例）。本件**没有**复用它：`GaloBase.H2` 的载体是 `muP`
（`trivialFp` 带 `ULift`），换载体会把偏差挪到 `muP ↔ trivialFp` 上。
**净增量 = 在 `muP` 的载体上把同一构造做出来**（`invPairing`）；其余全部库内，零自建数学。

## 3 诚实边界

`(CI)` 与 `H²(Γ⧸I,μ_p) = 0` 仍是假设；与 `GaloBase.H2 κ p` 的等同需 `Γ⧸I ≅ Gal(κ̄/κ)`（未形式化）。
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

section CanonicalCarrier

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-- `μ_p = ZMod p`（`Γ`-平凡作用）的 `I`-不变点。 -/
noncomputable abbrev RInv : Submodule (ZMod p) (GaloBase.muP F p).V :=
  ((GaloBase.muP F p).ρ.restrict I.subtype).invariants

theorem RInv_eq_top : RInv (F := F) p I = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [ContRepresentation.mem_invariants_restrict]
  intro s _
  exact GaloBase.muP_ρ F p s x

/-- ★★★ 不变点到 `ZMod p` 的线性等价（`= ⊤` 故双射）。 -/
noncomputable def RInvEquiv : ↥(RInv (F := F) p I) ≃ₗ[ZMod p] ZMod p :=
  LinearEquiv.ofBijective (Submodule.subtype (RInv (F := F) p I))
    ⟨fun _ _ h => Subtype.ext h,
     fun w => ⟨⟨w, by rw [RInv_eq_top]; exact Submodule.mem_top⟩, rfl⟩⟩

/-- 平凡作用：`I`-不变点上的 `Γ⧸I`-作用恒等。 -/
theorem qti_smul_eq_self (g : AbsoluteGaloisGroup F ⧸ I) (x : ↥(RInv (F := F) p I)) :
    (((GaloBase.muP F p).quotientToInvariants I).ρ g x) = x := by
  induction g using QuotientGroup.induction_on with
  | _ g' =>
    apply Subtype.ext
    rw [ContRepresentation.coe_quotientToInvariants_mk_apply]
    show (GaloBase.muP F p).ρ g' (x : (GaloBase.muP F p).V) = (x : (GaloBase.muP F p).V)
    rw [GaloBase.muP_ρ]

/-- ★★★ **平凡作用**：不变点上的 `Γ⧸I`-作用在 `RInvEquiv` 下不动。 -/
theorem RInvEquiv_smul (g : AbsoluteGaloisGroup F ⧸ I) (x : ↥(RInv (F := F) p I)) :
    RInvEquiv (F := F) p I (((GaloBase.muP F p).quotientToInvariants I).ρ g x)
      = RInvEquiv (F := F) p I x := by
  rw [qti_smul_eq_self (F := F) (p := p) (I := I) g x]

/-- 不变点上的乘法（双线性）。 -/
noncomputable def invMul :
    ↥(RInv (F := F) p I) →ₗ[ZMod p] ↥(RInv (F := F) p I) →ₗ[ZMod p] ↥(RInv (F := F) p I) :=
  LinearMap.mk₂ (ZMod p)
    (fun x y => (RInvEquiv (F := F) p I).symm
      (RInvEquiv (F := F) p I x * RInvEquiv (F := F) p I y))
    (by intro x y z
        apply (RInvEquiv (F := F) p I).injective
        simp only [LinearEquiv.apply_symm_apply, map_add]
        ring)
    (by intro c x y
        apply (RInvEquiv (F := F) p I).injective
        simp only [LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul]
        ring)
    (by intro x y z
        apply (RInvEquiv (F := F) p I).injective
        simp only [LinearEquiv.apply_symm_apply, map_add]
        ring)
    (by intro c x y
        apply (RInvEquiv (F := F) p I).injective
        simp only [LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul]
        ring)

/-- `invMul` 的取值公式。 -/
@[simp]
theorem invMul_apply (x y : ↥(RInv (F := F) p I)) :
    invMul (F := F) p I x y
      = (RInvEquiv (F := F) p I).symm
          (RInvEquiv (F := F) p I x * RInvEquiv (F := F) p I y) := (rfl)

/-- ★★★★ **不变点上的乘法系数配对**。 -/
noncomputable def invPairing :
    TopPairing ((GaloBase.muP F p).quotientToInvariants I)
      ((GaloBase.muP F p).quotientToInvariants I)
      ((GaloBase.muP F p).quotientToInvariants I) where
  bil := invMul (F := F) p I
  cont := continuous_of_discreteTopology
  equivariant := by
    intro g x y
    rw [qti_smul_eq_self (F := F) (p := p) (I := I) g x,
      qti_smul_eq_self (F := F) (p := p) (I := I) g y,
      qti_smul_eq_self (F := F) (p := p) (I := I) g]

/-- ★★★ `invPairing` 经不变点包含后就是 `GaloBase.muPairing`（`cup_infl` 的相容条件）。 -/
theorem invPairing_comp (x y : ↥(RInv (F := F) p I)) :
    (TopRep.quotientToInvariantsι (GaloBase.muP F p) I) ((invPairing (F := F) p I).bil x y)
      = (GaloBase.muPairing F p).bil
          ((TopRep.quotientToInvariantsι (GaloBase.muP F p) I) x)
          ((TopRep.quotientToInvariantsι (GaloBase.muP F p) I) y) := by
  have h1 : ∀ z : ↥(RInv (F := F) p I),
      (TopRep.quotientToInvariantsι (GaloBase.muP F p) I) z = RInvEquiv (F := F) p I z :=
    fun _ => rfl
  rw [h1, h1, h1]
  simp only [invPairing, invMul_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- ★★★★★ **库内 `infl` 的原生 1 次形态**：`H¹(Γ⧸I, μ_p) → H¹(Γ, μ_p)`。 -/
noncomputable def infl1Canon :
    ↥(continuousCohomology 1 ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat
      →ₗ[ZMod p] GaloBase.V F p :=
  (ContinuousCohomology.infl I (GaloBase.muP F p) 1).hom

/-- ★★★★★ **库内 `infl` 的原生 2 次形态**：`H²(Γ⧸I, μ_p) → H²(Γ, μ_p)`。 -/
noncomputable def infl2Canon :
    ↥(continuousCohomology 2 ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat
      →ₗ[ZMod p] GaloBase.H2 F p :=
  (ContinuousCohomology.infl I (GaloBase.muP F p) 2).hom

/-- 剩余侧杯积（标准载体）。 -/
noncomputable def cupCanon :
    ↥(continuousCohomology 1 ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat
      →ₗ[ZMod p]
      ↥(continuousCohomology 1 ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat
      →ₗ[ZMod p]
      ↥(continuousCohomology 2 ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat :=
  (invPairing (F := F) p I).cup 1 1

/-- ★★★★★ **inflation 保持 `(1,1)` 杯积**（库内 `TopPairing.cup_infl`，NSW (1.5.3)(iii)）。 -/
theorem infl2Canon_cup (a b :
    ↥(continuousCohomology 1 ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat) :
    infl2Canon (F := F) p I (cupCanon (F := F) p I a b)
      = GaloBase.cup (K := F) (p := p) (infl1Canon (F := F) p I a) (infl1Canon (F := F) p I b) := by
  have h := (GaloBase.muPairing F p).cup_infl (X := GaloBase.muP F p) (Y := GaloBase.muP F p)
    (Z := GaloBase.muP F p) I (invPairing (F := F) p I)
    (fun x y => invPairing_comp (F := F) (p := p) (I := I) x y) 1 1 a b
  exact h

/-- ★★★★ **`Subsingleton H²(Γ⧸I,μ_p) ⟹ range infl₂ = ⊥`**（标准载体）。 -/
theorem range_infl2Canon_eq_bot_of_subsingleton
    (h : Subsingleton
      ↥(continuousCohomology 2 ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat) :
    LinearMap.range (infl2Canon (F := F) p I) = ⊥ := by
  rw [LinearMap.range_eq_bot]
  refine LinearMap.ext fun x => ?_
  have hx : x = 0 :=
    @Subsingleton.elim
      ↥(continuousCohomology 2 ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat h x 0
  rw [hx]
  simp

end CanonicalCarrier

section Valuative

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **`(CI)` ⟹ `residueSpan ≤ range infl₂`**（标准载体）。 -/
theorem residueSpan_le_range_infl2Canon (hpF : IsUnit (p : F))
    (hCI : ∀ y : VKG F p v hpF,
      ∃ a : ↥(continuousCohomology 1
        ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat,
        infl1Canon (F := F) p I a = (y : GaloBase.V F p)) :
    residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
      ≤ LinearMap.range (infl2Canon (F := F) p I) := by
  rw [residueSpan, Submodule.span_le]
  rintro _ ⟨⟨y, z⟩, rfl⟩
  obtain ⟨a, ha⟩ := hCI y
  obtain ⟨b, hb⟩ := hCI z
  refine ⟨cupCanon (F := F) p I a b, ?_⟩
  rw [infl2Canon_cup, ha, hb]

/-- ★★★★★★ **档 ⑥（规范载体）**：`(CI)` ＋ `H²(Γ⧸I, μ_p) = 0` ⟹ `Ch4TameSymbolHyp`。 -/
theorem ch4TameSymbolHyp_of_subsingleton_H2canon
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hCI : ∀ y : VKG F p v hpF,
      ∃ a : ↥(continuousCohomology 1
        ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat,
        infl1Canon (F := F) p I a = (y : GaloBase.V F p))
    (hκ : Subsingleton
      ↥(continuousCohomology 2 ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF := by
  have hbot : LinearMap.range (infl2Canon (F := F) p I) = ⊥ :=
    range_infl2Canon_eq_bot_of_subsingleton (F := F) (p := p) (I := I) hκ
  have hspan : residueSpan (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) ≤ LinearMap.range (infl2Canon (F := F) p I) :=
    residueSpan_le_range_infl2Canon (F := F) (p := p) (I := I) hpF hCI
  refine (ch4TameSymbolHyp_iff_disjoint (F := F) (p := p) (v := v) (π := π)
    hζ hp hpF hv hπ hp2).mpr ?_
  rw [show residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
    = ⊥ from le_bot_iff.mp (hbot ▸ hspan)]
  exact disjoint_bot_right

/-- ★★★★★ **接入 `Hyp611` 的正规形**：档 ⑥（规范载体）⟹ `residueSpan = ⊥`。 -/
theorem residueSpan_eq_bot_of_subsingleton_H2canon (hpF : IsUnit (p : F))
    (hCI : ∀ y : VKG F p v hpF,
      ∃ a : ↥(continuousCohomology 1
        ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat,
        infl1Canon (F := F) p I a = (y : GaloBase.V F p))
    (hκ : Subsingleton
      ↥(continuousCohomology 2 ((GaloBase.muP F p).quotientToInvariants I)).toModuleCat) :
    residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF) = ⊥ :=
  le_bot_iff.mp <|
    (range_infl2Canon_eq_bot_of_subsingleton (F := F) (p := p) (I := I) hκ) ▸
      residueSpan_le_range_infl2Canon (F := F) (p := p) (I := I) hpF hCI

end Valuative

end L20261018

#print axioms L20261018.RInv_eq_top
#print axioms L20261018.RInvEquiv
#print axioms L20261018.RInvEquiv_smul
#print axioms L20261018.invPairing
#print axioms L20261018.invPairing_comp
#print axioms L20261018.infl1Canon
#print axioms L20261018.infl2Canon
#print axioms L20261018.infl2Canon_cup
#print axioms L20261018.range_infl2Canon_eq_bot_of_subsingleton
#print axioms L20261018.residueSpan_le_range_infl2Canon
#print axioms L20261018.ch4TameSymbolHyp_of_subsingleton_H2canon
#print axioms L20261018.residueSpan_eq_bot_of_subsingleton_H2canon
