import L20261018.Ch2.Hensel.Valuation.Step002_principal_units_without_completeness
import L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier
import L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness
import TauCeti.NumberTheory.ClassFieldTheory.Local.CyclicClass

/-!
# R1016：**(R1) 归约到范数形态**（战役载体版符号–范数判据）

R1015 把 (R1) 化为 Kummer 类形态：`(u)∪(π) = 0 ⟹ (u) = 0`（`v`-整单位）。
本轮再走一步：把**战役载体**的杯积消失条件接到 TauCeti 的**符号–范数判据上**。

## 用到的现成件（**侦察更正：载体对齐早已完成**）

`RECON-D2.md` §8.4 曾把「载体对齐」记为「须做（1–3 轮）」—— **这是错的**（本轮的自我更正）：
`Hyp81`（R900 段）已给出三层载体链与**杯积相容**：

* `H2Bridge.redEquiv1 : GaloBase.V K p ≃+ H¹(μ_p 系数)`（`H¹` 侧），
* **`H2Bridge.redEquiv_cup`**：`redEquiv (GaloBase.cup A B) = kummerCupPairing.cup (r A) (r B)`，
* `H2Bridge.brOfH2_cup`／`brOfH2_injective`。

而 TauCeti 的 **`cup_kummerClass_eq_zero_iff_mem_normGroup`** 实测**不含 `tr` 参数**（`#check`：
`hζ`、`hn`、`[NeZero n]`、`L`、`a b`、`s`、`hs`、`hgen` 而已），且 docstring 明写
"`K` need not be a local field" ⟹ **判据本身在论文层级可用**。

## 余下的唯一载体身份问题（L12/L16）

判据是对 **`ClassFieldTheory.kummerClass F hn a`** 陈述的，而战役载体给的是
**`redEquiv1 (KummerBridge.kummerClass F p hp a)`**。两者相等**不是 `rfl`**（本轮实测）。
故本轮把结论写成**以该等式为唯一桥接假设**的形式：

```
hbridge : ∀ a : Fˣ, redEquiv1 (kc a) = ClassFieldTheory.kummerClass F hp a
```

⟹ 于是 **(R1) ⟺ 「`v`-整单位 `u`：`u ∈ N_{F(π^{1/p})/F}(L^×) ⟹ u ∈ F^{×p}`」**，
只余 (i) 载体桥 `hbridge`（一条自然性等式），(ii) 范数群刻画（数学）。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti
open IntermediateField

namespace L20261018

section Transport

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- **载体链把杯积的消失条件送到 `μ_p` 系数上**：由 `Hyp81.redEquiv_cup` ＋ `redEquiv` 是等价。 -/
theorem cup_eq_zero_iff_redequiv (hp : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (a b : Fˣ) :
    GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a)
        (KummerBridge.kummerClass F p hp b) = 0
      ↔ (ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1
          (H2Bridge.redEquiv1 (p := p) (K := F) hζ (KummerBridge.kummerClass F p hp a))
          (H2Bridge.redEquiv1 (p := p) (K := F) hζ (KummerBridge.kummerClass F p hp b)) = 0 := by
  have h := H2Bridge.redEquiv_cup (p := p) (K := F) hζ
    (KummerBridge.kummerClass F p hp a) (KummerBridge.kummerClass F p hp b)
  constructor
  · intro hz
    rw [← h, hz, map_zero]
  · intro hz
    rw [← h] at hz
    exact (H2Bridge.redEquiv (p := p) (K := F) hζ).map_eq_zero_iff.mp hz

/-- **符号–范数判据（战役载体版）**，以载体桥 `hbridge` 为唯一接口假设。 -/
theorem cup_eq_zero_iff_mem_normGroup_of_bridge (hp : IsUnit (p : F))
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 (p := p) (K := F) hζ
      (KummerBridge.kummerClass F p hp a) = ClassFieldTheory.kummerClass F hp a)
    {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] {s : L} {b : Fˣ}
    (hs : s ^ p = algebraMap F L b) (hgen : IntermediateField.adjoin F {s} = ⊤) (a : Fˣ) :
    GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a)
        (KummerBridge.kummerClass F p hp b) = 0 ↔ a ∈ normGroup F L := by
  rw [cup_eq_zero_iff_redequiv (F := F) (p := p) hp hζ a b, hbridge a, hbridge b]
  exact ClassFieldTheory.cup_kummerClass_eq_zero_iff_mem_normGroup (n := p) (K := F)
    hζ hp a b hs hgen

end Transport

/-! ## (R1) 的范数形态 -/

section NormForm

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- **(R1) ⟺ 范数形态**（以载体桥为唯一接口假设）：

`Φ := ∪(·,π)` 在 `ker \bar v` 上单射 **⟺** 每个 `v`-整单位 `u`，若它是 `F(π^{1/p})/F` 的范数，
则 `u` 是 `F` 中的 `p` 次幂。 -/
theorem residuePhi_injective_iff_norm_of_bridge (hp : IsUnit (p : F))
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (v : Fˣ →* Multiplicative ℤ) (π : Fˣ)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 (p := p) (K := F) hζ
      (KummerBridge.kummerClass F p hp a) = ClassFieldTheory.kummerClass F hp a)
    {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] {s : L}
    (hs : s ^ p = algebraMap F L π) (hgen : IntermediateField.adjoin F {s} = ⊤) :
    Function.Injective (residuePhi (GaloBase.cup (K := F) (p := p))
        (valLinOf (F := F) (p := p) v hp) (KummerBridge.kummerClass F p hp π)) ↔
      ∀ u : Fˣ, valOfUnitOf (p := p) v u = 0 → u ∈ normGroup F L →
        u ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
  rw [residuePhi_injective_iff_kummer (F := F) (p := p) hp v π]
  constructor
  · intro hk u hu hmem
    refine (KummerBridge.kummerClass_eq_zero_iff (F := F) (p := p) hp u).mp ?_
    refine hk u hu ?_
    exact (cup_eq_zero_iff_mem_normGroup_of_bridge (F := F) (p := p) hp hζ hbridge
      (b := π) hs hgen u).mpr hmem
  · intro hn u hu hcup
    refine (KummerBridge.kummerClass_eq_zero_iff (F := F) (p := p) hp u).mpr ?_
    refine hn u hu ?_
    exact (cup_eq_zero_iff_mem_normGroup_of_bridge (F := F) (p := p) hp hζ hbridge
      (b := π) hs hgen u).mp hcup

end NormForm

end L20261018

#print axioms L20261018.cup_eq_zero_iff_redequiv
#print axioms L20261018.cup_eq_zero_iff_mem_normGroup_of_bridge
#print axioms L20261018.residuePhi_injective_iff_norm_of_bridge
