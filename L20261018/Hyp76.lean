import L20261018.Hyp67
import L20261018.Hyp74
import L20261018.Hyp75
import TauCeti.NumberTheory.ClassFieldTheory.Local.CyclicClass

/-!
# `(3)(ii)` 第三步（WIP，第一步已机检）：把 `AdjoinRoot` 载体搬到 `IntermediateField`

`Hyp67`／`Hyp75` 落在 **`AdjoinRoot` 模型** `L K p a` 上；`Hyp74` 的
`brauerCohomologyEquiv_crossedProductClass` 要求 **`L : IntermediateField K (SeparableClosure K)`**。

**入口选择（关键，R889 实测有效）**：不用 `AdjoinRoot.liftAlgHom`（R871 已记录「`AdjoinRoot` 模型 ＋
依赖它的类型会破坏实例推断」），而用
`IsSepClosed.lift : L K p a →ₐ[K] SeparableClosure K` ＋ `AlgEquiv.ofInjective`。

**已机检**：`emb`（载体嵌入）、`e`（**载体桥 `L K p a ≃ₐ[K] ↥(emb).fieldRange`**）。

**已实测的陷阱（R889）**：`AlgEquiv.ofInjective` 给的是 `↥f.range`（`Subalgebra`，其 `Algebra` 实例叫
`range.algebra`），而 `Emb` 的 `IntermediateField` 版是 `↥f.fieldRange`（实例叫 `fieldRange.algebra'`）。
两个载体的**底集相同**（故 `(e : L ≃ₐ ↥(emb).fieldRange)` 能通过类型检查），但
**`Algebra` 实例项不同** ⟹ `AlgEquiv.autCongr` 在本处报 type mismatch。
**修法（下一步第一件）**：把 `e` 直接用 `AlgHom.codRestrict` ＋ `AlgEquiv.ofBijective` 构造到
`↥(emb).fieldRange`，使两侧实例身份一致。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial AdjoinRoot

namespace SymbolCupBridge

open SymbolKummerField SymbolCarryCocycle SymbolPres
open TauCeti

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {a : K} {ζ : K}

section

variable [NeZero p] [Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X]))]
  [IsSplittingField K (L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X])]
  [Fintype (L K p a ≃ₐ[K] L K p a)] [FiniteDimensional K (L K p a)] [IsGalois K (L K p a)]
  (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)

include hζ ha

/-- **载体嵌入** `L K p a →ₐ[K] SeparableClosure K`（`Kˢ` 可分闭；`L/K` 可分）。 -/
noncomputable def emb : L K p a →ₐ[K] SeparableClosure K := by
  haveI : IsGalois K (L K p a) := isGalois (p := p) (a := a) hζ ha
  haveI : Algebra.IsSeparable K (L K p a) := IsGalois.to_isSeparable
  exact IsSepClosed.lift

/-- **载体桥**：`AdjoinRoot` 模型 ≅ 它在 `Kˢ` 里的像（`IntermediateField` 版）。 -/
noncomputable def e : L K p a ≃ₐ[K] ↥(emb (p := p) (a := a) hζ ha).fieldRange := by
  have hmem : ∀ x : L K p a, emb (p := p) (a := a) hζ ha x
      ∈ (emb (p := p) (a := a) hζ ha).fieldRange := fun x => ⟨x, rfl⟩
  refine AlgEquiv.ofBijective
    ((emb (p := p) (a := a) hζ ha).codRestrict _ hmem) ⟨?_, ?_⟩
  · intro x y hxy
    exact (emb (p := p) (a := a) hζ ha).injective
      (congrArg (fun z : ↥(emb (p := p) (a := a) hζ ha).fieldRange =>
        ((z : SeparableClosure K))) hxy)
  · intro y
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.1 y.2
    exact ⟨x, Subtype.ext hx⟩

/-- `e` 与 `emb` 的相容：`e` 是 `emb` 的像内版本。 -/
theorem coe_e (x : L K p a) :
    ((e (p := p) (a := a) hζ ha x : ↥(emb (p := p) (a := a) hζ ha).fieldRange) :
      SeparableClosure K) = emb (p := p) (a := a) hζ ha x :=
  rfl

/-- **`e` 与 `autCongr` 的相容**：`e (τ x) = (e.autCongr τ) (e x)`。 -/
theorem e_autCongr_apply (τ : L K p a ≃ₐ[K] L K p a) (x : L K p a) :
    e (p := p) (a := a) hζ ha (τ x)
      = (e (p := p) (a := a) hζ ha).autCongr τ (e (p := p) (a := a) hζ ha x) := by
  rw [show (e (p := p) (a := a) hζ ha).autCongr τ
      = (e (p := p) (a := a) hζ ha).symm.trans
        (τ.trans (e (p := p) (a := a) hζ ha)) from rfl]
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

/-- **`comap` 的等变条件**：`e ((e.autCongr)⁻¹ g · x) = g (e x)`。 -/
theorem comap_hf (g : ↥(emb (p := p) (a := a) hζ ha).fieldRange ≃ₐ[K]
    ↥(emb (p := p) (a := a) hζ ha).fieldRange) (x : L K p a) :
    e (p := p) (a := a) hζ ha ((e (p := p) (a := a) hζ ha).autCongr.symm g x)
      = g (e (p := p) (a := a) hζ ha x) := by
  rw [e_autCongr_apply, MulEquiv.apply_symm_apply]

/-- **搬过去的 carry 余环** `cYC'`：`(σ,τ) ↦ e (c (e⁻¹σ, e⁻¹τ))`。 -/
noncomputable def cYC' (b : Kˣ) :
    TwoCocycle K ↥(emb (p := p) (a := a) hζ ha).fieldRange :=
  ((carryCocycle (p := p) (a := a) hζ ha b)).comap
    (e (p := p) (a := a) hζ ha).autCongr.symm
    (e (p := p) (a := a) hζ ha).toAlgHom
    (comap_hf (p := p) (a := a) hζ ha)

/-- `cYC'` 的取值公式。 -/
theorem cYC'_toFun (b : Kˣ)
    (γ δ : ↥(emb (p := p) (a := a) hζ ha).fieldRange ≃ₐ[K]
      ↥(emb (p := p) (a := a) hζ ha).fieldRange) :
    (cYC' (p := p) (a := a) hζ ha b).toFun γ δ
      = Units.map (e (p := p) (a := a) hζ ha).toMonoidHom
          ((carryCocycle (p := p) (a := a) hζ ha b).toFun
            ((e (p := p) (a := a) hζ ha).autCongr.symm γ)
            ((e (p := p) (a := a) hζ ha).autCongr.symm δ)) :=
  (rfl)

/-- **载体侧的 `FiniteDimensional`**（沿 `e` 搬）。 -/
theorem finiteDimensional_range :
    FiniteDimensional K ↥(emb (p := p) (a := a) hζ ha).fieldRange :=
  Module.Finite.equiv (e (p := p) (a := a) hζ ha).toLinearEquiv

/-- **载体侧的 `IsGalois`**（沿 `e` 搬）。 -/
theorem isGalois_range : IsGalois K ↥(emb (p := p) (a := a) hζ ha).fieldRange := by
  haveI : IsGalois K (L K p a) := isGalois (p := p) (a := a) hζ ha
  exact IsGalois.of_algEquiv (e (p := p) (a := a) hζ ha)

/-- **载体侧的维数**：`[K(α):K] = p`。 -/
theorem finrank_range : Module.finrank K ↥(emb (p := p) (a := a) hζ ha).fieldRange = p := by
  rw [← (e (p := p) (a := a) hζ ha).toLinearEquiv.finrank_eq,
    finrank_eq (p := p) (a := a) hζ ha]

/-- **生成元搬到载体侧**：`gen` 沿 `e` 的共轭。 -/
noncomputable def gen' :
    ↥(emb (p := p) (a := a) hζ ha).fieldRange ≃ₐ[K]
      ↥(emb (p := p) (a := a) hζ ha).fieldRange :=
  (e (p := p) (a := a) hζ ha).autCongr (gen hζ ha)

/-- `gen'` 生成载体侧的 `Gal`。 -/
theorem mem_zpowers_gen' (σ : ↥(emb (p := p) (a := a) hζ ha).fieldRange ≃ₐ[K]
    ↥(emb (p := p) (a := a) hζ ha).fieldRange) :
    σ ∈ Subgroup.zpowers (gen' (p := p) (a := a) hζ ha) := by
  obtain ⟨τ, rfl⟩ := (e (p := p) (a := a) hζ ha).autCongr.surjective σ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_gen (p := p) (a := a) hζ ha τ)
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  rw [← hk, map_zpow]
  rfl

/-- `gen'` 的阶是 `p`。 -/
theorem orderOf_gen' : orderOf (gen' (p := p) (a := a) hζ ha) = p := by
  haveI := finiteDimensional_range (p := p) (a := a) hζ ha
  haveI := isGalois_range (p := p) (a := a) hζ ha
  rw [orderOf_eq_card_of_forall_mem_zpowers (mem_zpowers_gen' (p := p) (a := a) hζ ha),
    IsGalois.card_aut_eq_finrank K ↥(emb hζ ha).fieldRange,
    finrank_range (p := p) (a := a) hζ ha]

/-- `(e.autCongr).symm (gen'^i) = gen^i`。 -/
theorem symm_gen'_pow (i : ℕ) :
    (e (p := p) (a := a) hζ ha).autCongr.symm (gen' (p := p) (a := a) hζ ha ^ i)
      = gen hζ ha ^ i := by
  rw [gen', map_pow, MulEquiv.symm_apply_apply]

/-- 载体侧的 `bL`。 -/
noncomputable def bL' (b : Kˣ) :
    Units ↥((emb (p := p) (a := a) hζ ha).fieldRange) :=
  Units.map (algebraMap K ↥((emb (p := p) (a := a) hζ ha).fieldRange)).toMonoidHom b

/-- `e` 把 `bL` 送到载体侧的 `bL'`。 -/
theorem map_e_bL (b : Kˣ) :
    Units.map (e (p := p) (a := a) hζ ha).toMonoidHom (bL (p := p) (a := a) b)
      = bL' (p := p) (a := a) hζ ha b := by
  refine Units.ext ?_
  simp only [bL, bL', Units.coe_map, MonoidHom.coe_comp, Function.comp_apply]
  exact AlgEquiv.commutes (e (p := p) (a := a) hζ ha) (b : K)

/-- **原始 carry 余环在 `(gen^i, gen^j)` 上的取值**：`bL ^ ((i+j)/p)`。 -/
theorem carryCocycle_toFun_gen_pow (b : Kˣ) {i j : ℕ} (hi : i < p) (hj : j < p) :
    (carryCocycle (p := p) (a := a) hζ ha b).toFun (gen hζ ha ^ i) (gen hζ ha ^ j)
      = bL (p := p) (a := a) b ^ ((i + j) / p) := by
  show bL (p := p) (a := a) b ^ ((carryExp (p := p) (a := a) hζ ha (gen hζ ha ^ i)
      + carryExp (p := p) (a := a) hζ ha (gen hζ ha ^ j)) / p) = _
  rw [carryExp_gen_pow_of_lt (p := p) (a := a) hζ ha i hi,
    carryExp_gen_pow_of_lt (p := p) (a := a) hζ ha j hj]

/-- **`cYC'` 在 `(gen'^i, gen'^j)` 上的取值**：`bL' ^ ((i+j)/p)`。 -/
theorem cYC'_toFun_gen'_pow (b : Kˣ) {i j : ℕ} (hi : i < p) (hj : j < p) :
    (cYC' (p := p) (a := a) hζ ha b).toFun
        (gen' (p := p) (a := a) hζ ha ^ i) (gen' (p := p) (a := a) hζ ha ^ j)
      = bL' (p := p) (a := a) hζ ha b ^ ((i + j) / p) := by
  rw [cYC'_toFun, symm_gen'_pow (p := p) (a := a) hζ ha,
    symm_gen'_pow (p := p) (a := a) hζ ha,
    carryCocycle_toFun_gen_pow (p := p) (a := a) hζ ha b hi hj, map_pow,
    map_e_bL (p := p) (a := a) hζ ha]

variable [FiniteDimensional K ↥((emb (p := p) (a := a) hζ ha).fieldRange)]
variable [IsGalois K ↥((emb (p := p) (a := a) hζ ha).fieldRange)]

/-- **载体搬运的核心结论：搬过去的 carry 余环的类 = 循环类。**

这是 `Hyp75.cohomologyClass_carryCocycle` 在 `IntermediateField` 载体上的对应物
（即 `Hyp74` 要求的那一侧）。证明仍走 `TauCeti.H2π_eq_cyclicClass`：只须核
`i,j < p` 时 `cYC'` 取 `bL' ^ ((i+j)/p)`（`cYC'_toFun_gen'_pow`），
再分成 `p ≤ i+j` 与 `i+j < p` 两支（`Nat.div_eq_of_lt_le`／`Nat.div_eq_of_lt`）。 -/
theorem cohomologyClass_cYC' (b : Kˣ) :
    (cYC' (p := p) (a := a) hζ ha b).cohomologyClass
      = cyclicClass (mem_zpowers_gen' (p := p) (a := a) hζ ha) (Additive.ofMul b) := by
  haveI := finiteDimensional_range (p := p) (a := a) hζ ha
  rw [TwoCocycle.cohomologyClass_def]
  refine H2π_eq_cyclicClass (mem_zpowers_gen' (p := p) (a := a) hζ ha) _ b fun i j hi hj => ?_
  rw [orderOf_gen' (p := p) (a := a) hζ ha] at hi hj ⊢
  rw [TwoCocycle.coe_toCocycles₂]
  simp only [Prod.fst, Prod.snd, toMul_ofMul]
  rw [cYC'_toFun_gen'_pow (p := p) (a := a) hζ ha b hi hj]
  by_cases h : p ≤ i + j
  · have h1 : (i + j) / p = 1 := Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)
    rw [if_pos h, h1, pow_one]
    rfl
  · have h0 : (i + j) / p = 0 := Nat.div_eq_of_lt (by omega)
    rw [if_neg h, h0, pow_zero]
    rfl

/-- **交叉积类沿载体搬运不变**：`carryCocycle b` 与 `cYC' b` 同 Brauer 类。 -/
theorem crossedProductClass_cYC' (b : Kˣ) :
    BrauerGroup.crossedProductClass (carryCocycle (p := p) (a := a) hζ ha b)
      = BrauerGroup.crossedProductClass (cYC' (p := p) (a := a) hζ ha b) := by
  haveI : IsGalois K (L K p a) := isGalois (p := p) (a := a) hζ ha
  haveI : IsGalois K ↥((emb (p := p) (a := a) hζ ha).fieldRange) :=
    isGalois_range (p := p) (a := a) hζ ha
  refine BrauerGroup.crossedProductClass_eq_of_algEquiv _ _
    (e (p := p) (a := a) hζ ha) fun σ τ => ?_
  rw [cYC'_toFun (p := p) (a := a) hζ ha b, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

/-- `e α` 是 `a` 在 `Kˢ` 里的 `p` 次根。 -/
theorem e_alpha_pow :
    (e (p := p) (a := a) hζ ha (α (K := K) (p := p) (a := a))) ^ p
      = algebraMap K ↥((emb (p := p) (a := a) hζ ha).fieldRange) a := by
  rw [← map_pow, α_pow, AlgEquiv.commutes]

/-- `gen'` 在 `e α` 上就是乘 `ζ`。 -/
theorem gen'_e_alpha :
    gen' (p := p) (a := a) hζ ha (e (p := p) (a := a) hζ ha (α (K := K) (p := p) (a := a)))
      = algebraMap K ↥((emb (p := p) (a := a) hζ ha).fieldRange) ζ
        * e (p := p) (a := a) hζ ha (α (K := K) (p := p) (a := a)) := by
  rw [gen',
    ← e_autCongr_apply (p := p) (a := a) hζ ha (gen hζ ha) (α (K := K) (p := p) (a := a)),
    gen_alpha, map_smul, ← Algebra.smul_def]

omit hζ ha in
/-- `a ≠ 0`（由 `hpa : ∀ b, b^p ≠ a`；取 `b = 0`）。 -/
theorem a_ne_zero (K : Type) [Field K] (p : ℕ) [Fact p.Prime] (a : K)
    (hpa : ∀ b : K, b ^ p ≠ a) : a ≠ 0 := by
  intro h
  exact hpa 0 (by rw [h]; exact zero_pow (Fact.out : p.Prime).ne_zero)

omit hζ ha in
/-- 把 `a : K` 看成单位 `Kˣ`（`hpa` 保证非零）。 -/
noncomputable def aUnit (K : Type) [Field K] (p : ℕ) [Fact p.Prime] (a : K)
    (hpa : ∀ b : K, b ^ p ≠ a) : Kˣ :=
  Units.mk0 a (a_ne_zero K p a hpa)

omit hζ ha in
/-- `aUnit` 的底元素就是 `a`。 -/
@[simp] theorem aUnit_val (K : Type) [Field K] (p : ℕ) [Fact p.Prime] (a : K)
    (hpa : ∀ b : K, b ^ p ≠ a) : ((aUnit K p a hpa : Kˣ) : K) = a := rfl

/-- **`(3)(ii)` 主定理（交叉积版）**：carry 余环的 Brauer 类 = 负的 Kummer 杯积类。

装配链：`crossedProductClass_cYC'`（载体搬运）→ `Hyp74`（(A) 桥，在 `↥(emb).fieldRange` 上）
→ `cohomologyClass_cYC'`（carry 类 = 循环类）→ TauCeti 一般 `n` 定理（`kummerBrauerClass` = 负的
`relBrInfl(cyclicClass)`）。**符号是约定**：TauCeti 的 `kummerBrauerClass ζ hζ b a` 是 `(b)∪(a)`，
按杯积的斜对称性 `(b)∪(a) = -(a)∪(b)`，故右端取负。 -/
theorem brauerGroupEquivBr_carryCocycle (b : Kˣ) :
    ClassFieldTheory.brauerGroupEquivBr K
        (Additive.ofMul (BrauerGroup.crossedProductClass
          (carryCocycle (p := p) (a := a) hζ ha b)))
      = - ClassFieldTheory.kummerBrauerClass ζ hζ b (aUnit K p a ha) := by
  haveI := isGalois_range (p := p) (a := a) hζ ha
  rw [crossedProductClass_cYC' (p := p) (a := a) hζ ha b]
  rw [brauerGroupEquivBr_crossedProductClass
    (L := (emb (p := p) (a := a) hζ ha).fieldRange)
    (cYC' (p := p) (a := a) hζ ha b)]
  rw [cohomologyClass_cYC' (p := p) (a := a) hζ ha b]
  have hdiv : p / Module.finrank K ↥((emb (p := p) (a := a) hζ ha).fieldRange) = 1 := by
    rw [finrank_range (p := p) (a := a) hζ ha, Nat.div_self (Fact.out : p.Prime).pos]
  have hT := ClassFieldTheory.kummerBrauerClass_eq_neg_relBrInfl_cyclicClass
    (K := K) (n := p) hζ (L := ↥((emb (p := p) (a := a) hζ ha).fieldRange))
    (a := b) (b := aUnit K p a ha) (s := e (p := p) (a := a) hζ ha (α (K := K) (p := p) (a := a)))
    (e_alpha_pow (p := p) (a := a) hζ ha)
    (g := gen' (p := p) (a := a) hζ ha) (mem_zpowers_gen' (p := p) (a := a) hζ ha)
    (by rw [finrank_range (p := p) (a := a) hζ ha])
    (by rw [hdiv, pow_one]; exact gen'_e_alpha (p := p) (a := a) hζ ha)
    (emb (p := p) (a := a) hζ ha).fieldRange.val
  rw [hT, neg_neg]

/-- **`cor:symbol-cup`（`(3)(ii)` 的数学内容，交叉积呈现版）**。

`SymbolAlg K p a b ζ`（`F⟨x,y⟩/(x^p−a, y^p−b, yx−ζxy)`）的 Brauer 类 = 负的 Kummer 杯积类。 -/
theorem symbolAlg_brauerClass_eq (b : Kˣ)
    [Algebra.IsCentral K (SymbolAlg K p a (b : K) ζ)]
    [IsSimpleRing (SymbolAlg K p a (b : K) ζ)]
    [FiniteDimensional K (SymbolAlg K p a (b : K) ζ)] :
    ClassFieldTheory.brauerGroupEquivBr K
        (Additive.ofMul (BrauerGroup.mk (CSA.of K (SymbolAlg K p a (b : K) ζ))))
      = - ClassFieldTheory.kummerBrauerClass ζ hζ b (aUnit K p a ha) := by
  obtain ⟨ee⟩ := nonempty_algEquiv_crossedProduct (p := p) (a := a) hζ ha b
  rw [← brauerGroupEquivBr_carryCocycle (p := p) (a := a) hζ ha b]
  congr 1
  exact TauCeti.BrauerGroup.mk_eq_mk_of_algEquiv ee

end

end SymbolCupBridge

#print axioms SymbolCupBridge.brauerGroupEquivBr_carryCocycle
#print axioms SymbolCupBridge.symbolAlg_brauerClass_eq

#print axioms SymbolCupBridge.crossedProductClass_cYC'
#print axioms SymbolCupBridge.e_alpha_pow
#print axioms SymbolCupBridge.gen'_e_alpha

#print axioms SymbolCupBridge.cohomologyClass_cYC'

#print axioms SymbolCupBridge.carryCocycle_toFun_gen_pow
#print axioms SymbolCupBridge.map_e_bL
#print axioms SymbolCupBridge.cYC'_toFun_gen'_pow

#print axioms SymbolCupBridge.e_autCongr_apply
#print axioms SymbolCupBridge.comap_hf
#print axioms SymbolCupBridge.cYC'
#print axioms SymbolCupBridge.finrank_range
#print axioms SymbolCupBridge.mem_zpowers_gen'
#print axioms SymbolCupBridge.orderOf_gen'
#print axioms SymbolCupBridge.symm_gen'_pow

#print axioms SymbolCupBridge.emb
#print axioms SymbolCupBridge.e
