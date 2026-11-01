import L20261018.Hyp161
import L20261018.Hyp115
import L20261018.Hyp36
import L20261018.Hyp26

/-!
# R1014：§2.4 的**估值层脱离完备性** —— `\bar v` 由 ℤ-值离散赋值 `v` 直接给出

论文 `raw/L20261018.tex:978` 明写：「完备离散赋值域是 Hensel 的，**逆命题不假设**；本节不以完备性替代 Hensel 性」。
但战役此前的 §2.4 形式化（`Hyp114`／`Hyp115`）落在 `IsNonarchimedeanLocalField`（＝完备＋有限剩余）上，
原因**只有一个**：`\bar v` 的实现用了 TauCeti 的 `normalizedValuation`（它绑在
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` 上）。本轮实测（`#check`）：

* `KummerV.kummerClass_surjective`、`KummerBridge.kummerClass_mul/_inv/_eq_zero_iff` **全部类无关**
  （只要 `[Field F] [Fact p.Prime] [HasEnoughRootsOfUnity F p]`）⟹ Kummer 层**不需要**完备性；
* 故把 `v` 提成**数据**（`v : Fˣ →* Multiplicative ℤ`，就是论文的离散赋值取 ℤ-值）之后，
  `\bar v = v \bmod p` 的构造**逐字照搬** `Hyp115`，且**不再假设 `F` 完备**。

## 本文件给出

| 声明 | 内容 |
|---|---|
| `valOfUnitOf` | `v(a) mod p` |
| `valAddHomOf`／**`valLinOf`** | **`\bar v : H¹(F,μ_p) → 𝔽_p`（`ZMod p`-线性）**，只依赖 `v` |
| `valLinOf_kummerClass` | `\bar v((a)) = v(a) mod p`（论文 `\bar v = v \bmod p`，逐字） |
| `valLinOf_pi` | `v(π) = 1 ⟹ \bar v((π)) = 1`（分裂正合列右端满射的见证） |
| `valLin_eq_valLinOf_normalizedValuation` | **保守性**：`F` 完备时取 `v := normalizedValuation F` 即回落 `Hyp115.valLin`（`rfl`） |
| `henselResidueDataOfDiscreteValuation` | 两条剩余事实 ⟹ `HenselResidueData`（**Hensel 层级**，`VK := ker \bar v`） |
| **`orth_eq_bot_of_discrete_valuation`** | **4.2 在论文层级**（不完备；唯一缺口 = (R1)+(R2)） |
| **`thm_ramified_1_of_discrete_valuation`** | **4.3(1) 同上** |
| **`corollary_4_4_of_discrete_valuation`** | **4.4 同上**（`hK1` 即论文 `d_K = 1`） |

## 层级说明（诚实登记）

* 上下文里的 `[ValuativeRel F]` 只**标明**「`F` 是带赋值的域」；形式化本身不需要它。
* 论文的 **Hensel 性／`char F = 0`／`char K ≠ p`** 全部折进 **`TameResidueFacts`**（(R1)＋(R2) 的存在性）——
  这正是 `Hyp161` 已机检的等价性：`(∃ D, D.val = val) ↔ (R1) ∧ (R2)`。
* 残余域 `K` 已不出现：`VK := ker \bar v`（`Hyp139` 起的规范载体）。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel

namespace L20261018

/-! ## 1. 估值层：`v` 作数据 -/

section Val

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- `v(a) mod p`：任意 ℤ-值乘性函数（论文的离散赋值取 ℤ-值）的模 `p` 约化。 -/
noncomputable def valOfUnitOf (v : Fˣ →* Multiplicative ℤ) (a : Fˣ) : ZMod p :=
  ((Multiplicative.toAdd (v a) : ℤ) : ZMod p)

lemma valOfUnitOf_mul (v : Fˣ →* Multiplicative ℤ) (a b : Fˣ) :
    valOfUnitOf (p := p) v (a * b) = valOfUnitOf (p := p) v a + valOfUnitOf (p := p) v b := by
  rw [valOfUnitOf, valOfUnitOf, valOfUnitOf, map_mul, toAdd_mul']
  push_cast
  ring

lemma valOfUnitOf_one (v : Fˣ →* Multiplicative ℤ) : valOfUnitOf (p := p) v 1 = 0 := by
  simp [valOfUnitOf]

/-- **`v(a) ≡ v(b) (mod p)` 只要 `(a) = (b)`**（`v` 任意，不需要完备性）。 -/
theorem valOfUnitOf_eq_of_kummerClass_eq (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F))
    {a b : Fˣ} (h : KummerBridge.kummerClass F p hp a = KummerBridge.kummerClass F p hp b) :
    valOfUnitOf (p := p) v a = valOfUnitOf (p := p) v b := by
  have hd : KummerBridge.kummerClass F p hp (a * b⁻¹) = 0 := by
    rw [KummerV.kummerClass_mul (F := F) (p := p) hp,
      KummerV.kummerClass_inv (F := F) (p := p) hp, h, add_neg_cancel]
  rw [KummerBridge.kummerClass_eq_zero_iff (F := F) (p := p) hp] at hd
  obtain ⟨z, hz⟩ := hd
  have hv : Multiplicative.toAdd (v (a * b⁻¹)) = (p : ℤ) * Multiplicative.toAdd (v z) := by
    rw [← hz, show (powMonoidHom p : Fˣ →* Fˣ) z = z ^ p from rfl, map_pow, toAdd_pow']
  have hsplit : Multiplicative.toAdd (v a)
      = Multiplicative.toAdd (v b) + (p : ℤ) * Multiplicative.toAdd (v z) := by
    have h1 : v a = v (a * b⁻¹) * v b := by
      rw [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [h1, toAdd_mul', hv]
    ring_nf
  rw [valOfUnitOf, valOfUnitOf, hsplit]
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero]

/-- **`\bar v : H¹(F,μ_p) → 𝔽_p`**（`ZMod p`-线性），只由 `v` 决定。 -/
noncomputable def valAddHomOf (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) :
    GaloBase.V F p →+ ZMod p where
  toFun x := valOfUnitOf (p := p) v
    (Classical.choose (KummerV.kummerClass_surjective (F := F) (p := p) hp x))
  map_zero' := by
    have h0 : KummerBridge.kummerClass F p hp
        (Classical.choose (KummerV.kummerClass_surjective (F := F) (p := p) hp 0)) = 0 :=
      Classical.choose_spec (KummerV.kummerClass_surjective (F := F) (p := p) hp 0)
    have h1 : KummerBridge.kummerClass F p hp
        (Classical.choose (KummerV.kummerClass_surjective (F := F) (p := p) hp 0))
        = KummerBridge.kummerClass F p hp 1 := by
      rw [h0]
      exact ((KummerBridge.kummerClass_eq_zero_iff (F := F) (p := p) hp 1).mpr (one_mem _)).symm
    rw [valOfUnitOf_eq_of_kummerClass_eq (p := p) v hp h1]
    exact valOfUnitOf_one (p := p) v
  map_add' x y := by
    set ax := Classical.choose (KummerV.kummerClass_surjective (F := F) (p := p) hp x) with hax
    set ay := Classical.choose (KummerV.kummerClass_surjective (F := F) (p := p) hp y) with hay
    have hx : KummerBridge.kummerClass F p hp ax = x :=
      Classical.choose_spec (KummerV.kummerClass_surjective (F := F) (p := p) hp x)
    have hy : KummerBridge.kummerClass F p hp ay = y :=
      Classical.choose_spec (KummerV.kummerClass_surjective (F := F) (p := p) hp y)
    have hkey : KummerBridge.kummerClass F p hp
        (Classical.choose (KummerV.kummerClass_surjective (F := F) (p := p) hp (x + y)))
        = KummerBridge.kummerClass F p hp (ax * ay) := by
      rw [Classical.choose_spec (KummerV.kummerClass_surjective (F := F) (p := p) hp (x + y)),
        KummerV.kummerClass_mul (F := F) (p := p) hp, hx, hy]
    rw [valOfUnitOf_eq_of_kummerClass_eq (p := p) v hp hkey]
    exact valOfUnitOf_mul (p := p) v ax ay

/-- **`\bar v : H¹(F,μ_p) → 𝔽_p`**（`ZMod p`-线性）。 -/
noncomputable def valLinOf (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) :
    GaloBase.V F p →ₗ[ZMod p] ZMod p :=
  (valAddHomOf (F := F) (p := p) v hp).toZModLinearMap p

/-- **`\bar v((a)) = v(a) mod p`** —— 论文「`\bar v = v \bmod p`」逐字（`v` 任意，不完备亦可）。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-kummer-valuation quote="\xrightarrow{\bar v}\Fp\longrightarrow0,\bar v=v\bmod p,"
theorem valLinOf_kummerClass (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) (a : Fˣ) :
    valLinOf (F := F) (p := p) v hp (KummerBridge.kummerClass F p hp a)
      = valOfUnitOf (p := p) v a := by
  have : valLinOf (F := F) (p := p) v hp (KummerBridge.kummerClass F p hp a)
      = valAddHomOf (F := F) (p := p) v hp (KummerBridge.kummerClass F p hp a) := rfl
  rw [this]
  exact valOfUnitOf_eq_of_kummerClass_eq (p := p) v hp
    (Classical.choose_spec (KummerV.kummerClass_surjective (F := F) (p := p) hp
      (KummerBridge.kummerClass F p hp a)))

/-- **正合列右端满射的见证**：`v(π) = 1 ⟹ \bar v((π)) = 1`（`v` 任意）。 -/
theorem valLinOf_pi (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) :
    valLinOf (F := F) (p := p) v hp (KummerBridge.kummerClass F p hp π) = 1 := by
  rw [valLinOf_kummerClass, valOfUnitOf, hπ]
  simp

end Val

/-! ## 2. 保守性：完备情形取 `v := normalizedValuation F` 即回落 `Hyp115.valLin` -/

section Complete

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **保守性（`rfl`）**：完备情形取 `v := TauCeti.normalizedValuation F`，
新构造 `valLinOf` **就是** `Hyp115.valLin`（故 `Hyp135`／`Hyp138`／`Hyp161.tameResidueFacts_of_complete`
的读数仍是本层构造的实例）。 -/
theorem valLin_eq_valLinOf_normalizedValuation (hp : IsUnit (p : F)) :
    (valLinOf (F := F) (p := p) (TauCeti.normalizedValuation F) hp : GaloBase.V F p →ₗ[ZMod p] ZMod p)
      = valLin F p hp := rfl

end Complete

/-! ## 3. 论文层级（Hensel，不完备）：`D` 与 4.2／4.3(1)／4.4 -/

section PaperLevel

variable {F : Type} [Field F] [ValuativeRel F] (p : ℕ) [Fact p.Prime]
  [HasEnoughRootsOfUnity F p]

/-- **两条剩余事实 ⟹ `HenselResidueData`（论文层级）**：`v` 为 ℤ-值离散赋值，`π` 为一致化元。

`Hyp161.henselResidueDataOfFacts` 在此实例化：`val := valLinOf v`、`pi := (π)`、
`split := decomp_mem_ker`（纯线性代数）、`tame_pi_u := tame_pi_u_of`。 -/
noncomputable def henselResidueDataOfDiscreteValuation (hp : IsUnit (p : F))
    (v : Fˣ →* Multiplicative ℤ) {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (hfacts : TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hp) (KummerBridge.kummerClass F p hp π)) :
    HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p)
      ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hp)) (GaloBase.cup (K := F) (p := p)) :=
  henselResidueDataOfFacts (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hp)
    (KummerBridge.kummerClass F p hp π) (valLinOf_pi (F := F) (p := p) v hp hπ)
    (fun x y => GaloBase.cup_skew (K := F) (p := p) x y) hfacts

/-- **`lem:ramified-vanishing`（论文 4.2）在论文假设层级**（Hensel，**不假设完备性**）：
唯一缺口是两条剩余事实 (R1)＋(R2)。 -/
-- @source file=raw/L20261018.tex locator=line:1608 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem orth_eq_bot_of_discrete_valuation (hp : IsUnit (p : F))
    (v : Fˣ →* Multiplicative ℤ) {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (hp2 : NeZero (2 : ZMod p)) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2,
      valLinOf (F := F) (p := p) v hp u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)]
    (hfacts : TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hp) (KummerBridge.kummerClass F p hp π)) :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ :=
  orth_eq_bot_paper_route_hensel (F := F) (p := p)
    (D := henselResidueDataOfDiscreteValuation (F := F) (p := p) hp v hπ hfacts)
    hp2 hne hval

variable (Δ : Subgroup Fˣ)

/-- **4.3(1) 在论文假设层级**（Hensel，不完备）：`U^⊥ = N = 0`，唯一缺口 = (R1)＋(R2)。 -/
-- @source file=raw/L20261018.tex locator=line:1636 quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$；"
theorem thm_ramified_1_of_discrete_valuation (hp : IsUnit (p : F))
    (hp2 : p ≠ 2) [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (hU : IsOpen ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
      : Set (AbsoluteGaloisGroup F)))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p) Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p) Δ)]
    (v : Fˣ →* Multiplicative ℤ) {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (hfacts : TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hp) (KummerBridge.kummerClass F p hp π))
    {a1 a2 : Fˣ} (ha1 : a1 ∈ Δ) (ha2 : a2 ∈ Δ)
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2),
      valLinOf (F := F) (p := p) v hp u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    (Theo352.Bex (F := F) (p := p) hp hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ :=
  thm_ramified_1_of_D_free (F := F) (p := p)
    (D := henselResidueDataOfDiscreteValuation (F := F) (p := p) hp v hπ hfacts)
    hp hp2 Δ hroots hU ha1 ha2 hne hval

/-- **4.4 在论文假设层级**（Hensel，不完备）：`d_K = 1`（`hK1`）⟹ `rank Φ = 2 ∧ d_F = 2`。 -/
-- @source file=raw/L20261018.tex locator=line:1648 quote="特别地，若 $d_K=1$，则 $\rank(\Phi)=2$，这与 $\ind(D)=p^2$ 时的定理~\ref{thm:rank-barrier} 矛盾。"
theorem corollary_4_4_of_discrete_valuation (hp : IsUnit (p : F)) {a1 a2 : Fˣ}
    (v : Fˣ →* Multiplicative ℤ) {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (hfacts : TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hp) (KummerBridge.kummerClass F p hp π))
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2),
      valLinOf (F := F) (p := p) v hp (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    (hK1 : Module.finrank (ZMod p)
      ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hp)) = 1)
    [FiniteDimensional (ZMod p) (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))]
    [NeZero (2 : ZMod p)] :
    Module.finrank (ZMod p)
        ↥(ResidueCupData.commonCupMap (Theo352.cupLin (F := F) (p := p))
          (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
          (GaloCup.kummerExplicit (F := F) (p := p) hp a2)).range = 2
      ∧ Module.finrank (ZMod p) (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) = 2 :=
  corollary_4_4_of_D_free (F := F) (p := p)
    (D := henselResidueDataOfDiscreteValuation (F := F) (p := p) hp v hπ hfacts)
    hp hne hval hK1

end PaperLevel

end L20261018

#print axioms L20261018.valOfUnitOf_eq_of_kummerClass_eq
#print axioms L20261018.valLinOf_kummerClass
#print axioms L20261018.valLinOf_pi
#print axioms L20261018.valLin_eq_valLinOf_normalizedValuation
#print axioms L20261018.henselResidueDataOfDiscreteValuation
#print axioms L20261018.orth_eq_bot_of_discrete_valuation
#print axioms L20261018.thm_ramified_1_of_discrete_valuation
#print axioms L20261018.corollary_4_4_of_discrete_valuation
