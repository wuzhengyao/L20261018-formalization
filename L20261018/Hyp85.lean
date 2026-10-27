import L20261018.Hyp84
import L20261018.Hyp83
import L20261018.Hyp82
import L20261018.Hyp77
/-!
# `hind` 的机检（R900）：`3.2(1)(2)` 的最后一块

`indOfH2_le_of_class_eq`（`Hyp82`）把「指数 ≤ p」归约为「该类的类恰是某个 CSA 的类且其指数 ≤ p」。
本文件对论文的 `h = (a₁)∪(a₂)` 把这件事做完：

```
x = c • h
  ⟹ brOfH2 x = h2MuToBr (∪ (c • X) Y)          -- Hyp84.brOfH2_smul_cup
  ⟹ brOfH2 x = kummerBrauerClass a' b'          -- 两次 kummerClass_surjective ＋ kummerBrauerClass_def
  ⟹ 分支:
       a' ∈ (Kˣ)^p  ⟹ 类 = 0 ⟹ A := K  指数 1 ≤ p
       a' ∉ (Kˣ)^p  ⟹ A := SymbolAlg a' b' ζ，Hyp77 ＋ Hyp83 给指数 ≤ p
```

## 主结果

* `notMem_pow_of_notMem_powerSubgroup`：`a ∉ (Kˣ)^p` ⟹ `∀ b : K, b^p ≠ a`（Hyp55/68 的 `ha` 形式）。
* `index_self_le`：`index K K ≤ p`（平凡类的指数）。
* **`indOfH2_le_of_class_one`**：类为 `0` 时 `indOfH2 ≤ p`。
* **`hind_kummer`**：**论文 3.2(1)(2) 的 `hind`**——`span{h}` 上 `ind ≤ p`，只带论文自身的假设。
-/

open TauCeti
open Polynomial
open SymbolPres SymbolPres.SymbolAlg

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace H2Bridge

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K} [NeZero p]

/-! ### 平凡类的指数 -/

/-- **`index K K = 1`**（基域自身的指数；`M_1 ≅ K` ＋ `deg_self`）。 -/
theorem index_self_eq_one : TauCeti.Algebra.index K K = 1 := by
  rw [TauCeti.Algebra.index_eq_deg_of_algEquiv_matrix
    (SymbolWedderburn.matrixFinOneAlgEquiv (K := K) K).symm, TauCeti.Algebra.deg_self]

/-- **`index K K ≤ p`**（`p` 素）。 -/
theorem index_self_le : TauCeti.Algebra.index K K ≤ p := by
  rw [index_self_eq_one]
  exact (Fact.out : p.Prime).one_lt.le

/-- **`a ∉ (Kˣ)^p` 的域元素形式**：`∀ b : K, b^p ≠ a`（`Hyp55`／`Hyp68` 的 `ha`）。 -/
theorem notMem_pow_of_notMem_powerSubgroup {a : K} (ha0 : a ≠ 0)
    (h : (Units.mk0 a ha0 : Kˣ) ∉ powerSubgroup Kˣ p) : ∀ b : K, b ^ p ≠ a := by
  intro b hb
  apply h
  rw [powerSubgroup_eq_range_powMonoidHom, MonoidHom.mem_range]
  by_cases hb0 : b = 0
  · subst hb0
    rw [zero_pow (Fact.out : p.Prime).ne_zero] at hb
    exact absurd hb.symm ha0
  · exact ⟨Units.mk0 b hb0, by ext; simpa using hb⟩

/-- **平凡类分支**：`brOfH2` 的类为 `0` 时 `indOfH2 ≤ p`（取 `A := K`）。 -/
theorem indOfH2_le_of_class_one (hζ : IsPrimitiveRoot ζ p) {x : GaloBase.H2 K p}
    (hx : brOfH2 (p := p) (K := K) hζ x = 0) : indOfH2 (p := p) (K := K) hζ x ≤ p := by
  have h1 : brauerOfH2 (p := p) (K := K) hζ x = 1 := by
    rw [brauerOfH2, hx, map_zero]
    rfl
  refine indOfH2_le_of_class_eq (p := p) (K := K) hζ (A := K) ?_ index_self_le
  rw [h1]
  exact (BrauerGroup.mk_base (K := K)).symm

/-! ### `hind`：`span {h}` 上 `ind ≤ p` -/

/-- **3.2(1)(2) 的 `hind`**：论文的 `h = (a₁) ∪ (a₂)` 生成的直线上，`ind ≤ p`。

前提只有论文自身的假设：`ζ_p ∈ K`、`p` 在 `K` 中可逆、`a₁ a₂ : Kˣ` 以及非平凡性
`(a₁)∪(a₂) ≠ 0`（`hne` 只用于使 `span` 的定义合法，本证明不需要它的非零性——
但保留它以与论文陈述同形）。 -/
theorem hind_kummer [HasEnoughRootsOfUnity K p] (hp : IsUnit (p : K))
    (hζ : IsPrimitiveRoot ζ p) (a1 a2 : Kˣ)
    (hne : GaloBase.cup (K := K) (p := p) (KummerBridge.kummerClass K p hp a1)
      (KummerBridge.kummerClass K p hp a2) ≠ 0) :
    ∀ x ∈ Submodule.span (ZMod p) (Set.singleton (GaloBase.cup (K := K) (p := p)
      (KummerBridge.kummerClass K p hp a1) (KummerBridge.kummerClass K p hp a2))),
      indOfH2 (p := p) (K := K) hζ x ≤ p := by
  intro x hx
  -- 论文的类，缩写
  set cl1 : GaloBase.V K p := KummerBridge.kummerClass K p hp a1 with hcl1
  set cl2 : GaloBase.V K p := KummerBridge.kummerClass K p hp a2 with hcl2
  -- `hx : x ∈ span {cl1 ∪ cl2}`
  rw [show (GaloBase.cup (K := K) (p := p) (KummerBridge.kummerClass K p hp a1)
      (KummerBridge.kummerClass K p hp a2)) = GaloBase.cup (K := K) (p := p) cl1 cl2 from by
    rw [hcl1, hcl2]] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton (R := ZMod p) (x := x)
    (y := GaloBase.cup (K := K) (p := p) cl1 cl2)).mp hx
  rw [← hc]
  -- 两次满射（用与 `kummerBrauerClass_def` 相同的 `hn`）
  obtain ⟨a', ha'⟩ := ClassFieldTheory.kummerClass_surjective K hζ.neZero'.out.isUnit
    (c • redEquiv1 (p := p) (K := K) hζ cl1)
  obtain ⟨b', hb'⟩ := ClassFieldTheory.kummerClass_surjective K hζ.neZero'.out.isUnit
    (redEquiv1 (p := p) (K := K) hζ cl2)
  -- 类的表达式
  have key : brOfH2 (p := p) (K := K) hζ (c • GaloBase.cup (K := K) (p := p) cl1 cl2)
      = ClassFieldTheory.kummerBrauerClass ζ hζ a' b' := by
    rw [brOfH2_smul_cup (p := p) (K := K) hζ c cl1 cl2, ← ha', ← hb']
    exact (ClassFieldTheory.kummerBrauerClass_def ζ hζ a' b').symm
  by_cases hpow : a' ∈ powerSubgroup Kˣ p
  · -- 平凡支：类 = 0
    have hzero : brOfH2 (p := p) (K := K) hζ (c • GaloBase.cup (K := K) (p := p) cl1 cl2) = 0 := by
      rw [key, ClassFieldTheory.kummerBrauerClass_def]
      have h0 : ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit a' = 0 :=
        (ClassFieldTheory.kummerClass_eq_zero_iff K hζ.neZero'.out.isUnit).mpr hpow
      rw [h0, map_zero, LinearMap.zero_apply, map_zero]
    exact indOfH2_le_of_class_one (p := p) (K := K) hζ hzero
  · -- 非平凡支：符号代数
    have hne0 : (a' : K) ≠ 0 := Units.ne_zero a'
    have hpow' : Units.mk0 (a' : K) hne0 ∉ powerSubgroup Kˣ p := by simpa using hpow
    have ha'' : ∀ b : K, b ^ p ≠ (a' : K) :=
      notMem_pow_of_notMem_powerSubgroup hne0 hpow'
    -- `L` 侧的整套实例（Ha'' ＋ hζ 全推，见 Hyp83）
    haveI hFact : Fact (Irreducible (Polynomial.X ^ p - Polynomial.C (a' : K))) :=
      SymbolCarryCocycle.fact_irreducible_of_notMem_pow ha''
    haveI hSplit : IsSplittingField K (SymbolKummerField.L K p (a' : K))
        (Polynomial.X ^ p - Polynomial.C (a' : K)) :=
      SymbolKummerField.isSplittingField (p := p) (a := (a' : K)) hζ ha''
    haveI hFin : FiniteDimensional K (SymbolKummerField.L K p (a' : K)) :=
      IsSplittingField.finiteDimensional (L := SymbolKummerField.L K p (a' : K))
        (Polynomial.X ^ p - Polynomial.C (a' : K))
    haveI hGal : IsGalois K (SymbolKummerField.L K p (a' : K)) :=
      SymbolKummerField.isGalois (p := p) (a := (a' : K)) hζ ha''
    haveI hFint : Fintype (SymbolKummerField.L K p (a' : K) ≃ₐ[K]
        SymbolKummerField.L K p (a' : K)) := AlgEquiv.fintype K _
    -- `SymbolAlg` 的三条 CSA 实例 ＋ 指数界（Hyp83）
    haveI hC : Algebra.IsCentral K (SymbolAlg K p (a' : K) (b' : K) ζ) :=
      SymbolCarryCocycle.isCentral_symbolAlg (p := p) (a := (a' : K)) hζ ha'' b'
    haveI hS : IsSimpleRing (SymbolAlg K p (a' : K) (b' : K) ζ) :=
      SymbolCarryCocycle.isSimpleRing_symbolAlg (p := p) (a := (a' : K)) hζ ha'' b'
    haveI hF : FiniteDimensional K (SymbolAlg K p (a' : K) (b' : K) ζ) :=
      SymbolCarryCocycle.finiteDimensional_symbolAlg (p := p) (a := (a' : K)) (b := (b' : K)) (ζ := ζ)
    have hle : TauCeti.Algebra.index K (SymbolAlg K p (a' : K) (b' : K) ζ) ≤ p :=
      SymbolCarryCocycle.index_symbolAlg_le_of_notMem_pow (p := p) (a := (a' : K)) hζ ha'' b'
    -- `aUnit` 就是 `a'`
    have haUnit : SymbolCupBridge.aUnit K p (a' : K) ha'' = a' := by
      ext
      rw [SymbolCupBridge.aUnit_val]
    -- 类 = 符号代数的类（Hyp77 逐字形式）
    have hsym := SymbolCupBridge.symbolAlg_brauerClass_eq_verbatim
      (p := p) (a := (a' : K)) hζ ha'' b'
    have hA : brauerOfH2 (p := p) (K := K) hζ (c • GaloBase.cup (K := K) (p := p) cl1 cl2)
        = BrauerGroup.mk (CSA.of K (SymbolAlg K p (a' : K) (b' : K) ζ)) := by
      have hbr : ClassFieldTheory.brauerGroupEquivBr K
          (Additive.ofMul (brauerOfH2 (p := p) (K := K) hζ
            (c • GaloBase.cup (K := K) (p := p) cl1 cl2)))
          = brOfH2 (p := p) (K := K) hζ (c • GaloBase.cup (K := K) (p := p) cl1 cl2) := by
        show ClassFieldTheory.brauerGroupEquivBr K
          ((ClassFieldTheory.brauerGroupEquivBr K).symm
            (brOfH2 (p := p) (K := K) hζ (c • GaloBase.cup (K := K) (p := p) cl1 cl2)))
          = brOfH2 (p := p) (K := K) hζ (c • GaloBase.cup (K := K) (p := p) cl1 cl2)
        rw [AddEquiv.apply_symm_apply]
      have h2 : ClassFieldTheory.brauerGroupEquivBr K
          (Additive.ofMul (brauerOfH2 (p := p) (K := K) hζ
            (c • GaloBase.cup (K := K) (p := p) cl1 cl2)))
          = ClassFieldTheory.brauerGroupEquivBr K
              (Additive.ofMul (BrauerGroup.mk (CSA.of K (SymbolAlg K p (a' : K) (b' : K) ζ)))) := by
        rw [hbr, hsym, haUnit, ← key]
      exact Additive.ofMul.injective ((ClassFieldTheory.brauerGroupEquivBr K).injective h2)
    exact indOfH2_le_of_class_eq (p := p) (K := K) hζ
      (A := SymbolAlg K p (a' : K) (b' : K) ζ) hA hle

end H2Bridge

#print axioms H2Bridge.index_self_eq_one
#print axioms H2Bridge.index_self_le
#print axioms H2Bridge.notMem_pow_of_notMem_powerSubgroup
#print axioms H2Bridge.indOfH2_le_of_class_one
#print axioms H2Bridge.hind_kummer
