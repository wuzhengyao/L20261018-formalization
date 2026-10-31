import Hyp207

/-!
# R1079（**T1 的第一个归约：把「任意选基」因子分离出来**）

T1（`∃ c ≠ 0, kc = c • bridgeKc`）的障碍在于 `KummerCoeff F p` 的**系数识别**：
战役侧用 `kummerCoeffLinearEquiv`（`LinearEquiv.ofFinrankEq`，**任意选基**），
TauCeti 侧用 `kummerCoeffEquivMuNRep`（其 docstring 明言 not canonical）。

本文件把那一步**具名分离**：定义残余系数映射

```
e''  :=  kummerCoeffEquivMuNRep ∘ (kummerCoeffLinearEquiv)⁻¹  :  ZMod p →+ muNRep.V
```

于是 `kummerCoeffEquivMuNRep = e'' ∘ kummerCoeffLinearEquiv` **逐点成立**——
即两条 Kummer 类路线的系数层部分**只差 `e''`，而 `e''` 是 `ZMod p`（一维）到 `muNRep.V` 的映射**唯一**要处理的对象**。

| 声明 | 内容 |
|---|---|
| **`eDouble`** | `ZMod p →+ muNRep.V`，`e'' := kce ∘ e_c⁻¹` |
| **`kce_eq_eDouble_comp`** | `kce x = e'' (e_c x)`（系数层因子分离） |

**下一步**：用 `ContCohomology.explicitMap1_comp`（`ExplicitFunctoriality.lean:394`：
`explicitMap1 (φ ∘ ψ) (q ∘ f) = explicitCoeff1 ψ q ∘ explicitMap1 φ f`）把
`muNRepH1Equiv = OfDiscrete ∘ explicitMap1 φ kce` 改写成
`OfDiscrete ∘ (explicitMap1 φ e'') ∘ explicitCoeff1(e_c)` —— 与战役侧 `kc = h1ToVEquiv ∘ explicitCoeff1(e_c)`
**共享最右端的 `explicitCoeff1(e_c)`**，从而 T1 化为「两个固定运输只差标量」（墙的最终形态）。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

section Factor

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **残余系数映射** `e'' := kce ∘ e_c⁻¹ : ZMod p →+ muNRep.V`。 -/
noncomputable def eDouble (hp : IsUnit (p : F)) : ZMod p →+ (ClassFieldTheory.muNRep p F).V :=
  (ClassFieldTheory.kummerCoeffEquivMuNRep (n := p) (F := F)).toAddMonoidHom.comp
    (KummerBridge.kummerCoeffLinearEquiv F p hp).symm.toAddMonoidHom

/-- **系数层因子分离**：`kce x = e'' (e_c x)`。 -/
theorem kce_eq_eDouble_comp (hp : IsUnit (p : F)) (x : KummerCoeff F p) :
    ClassFieldTheory.kummerCoeffEquivMuNRep (n := p) (F := F) x
      = eDouble (F := F) p hp (KummerBridge.kummerCoeffLinearEquiv F p hp x) := by
  simp [eDouble]

end Factor

end L20261018

#print axioms L20261018.kce_eq_eDouble_comp

/-! ## 追加（R1080）：两条 Kummer 类路线的**系数作用都是平凡的**

`TauCeti.smul_kummerCoeff_eq_self`（`FieldTheory/GaloisCohomology/Coefficients.lean:154`）：
对 `ζ ∈ K` 本原 `p` 次单位根、`g : G_K`、`x : KummerCoeff K p` 有 **`g • x = x`**。
于是 `kummerCoeffEquivMuNRep_smul` 给 `muNRep` 侧的 `G`-作用也**平凡**（`kce` 是等变双射）。
⟹ `explicitMap1_comp` 因子分解所需的**两条等变性条件全部空洞**（两边作用都平凡），
T1 的第一归约只剩**纯系数层**的 `e'' = kce ∘ e_c⁻¹`。 -/

namespace L20261018

section Trivial

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- **`KummerCoeff` 的 `G`-作用平凡**（TauCeti `smul_kummerCoeff_eq_self` 的包装）。 -/
theorem kummerCoeff_smul_trivial {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (g : AbsoluteGaloisGroup F) (x : KummerCoeff F p) : g • x = x :=
  TauCeti.smul_kummerCoeff_eq_self hζ g x

/-- **推论：`muNRep.V` 的 `G`-作用也平凡**（`kce` 满射 ＋ `KummerCoeff` 平凡）。 -/
theorem muNRep_smul_trivial {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (g : Field.absoluteGaloisGroup F) (x : (ClassFieldTheory.muNRep p F).V) :
    x = (ClassFieldTheory.muNRep p F).ρ g x := by
  obtain ⟨y, rfl⟩ := (ClassFieldTheory.kummerCoeffEquivMuNRep (n := p) (F := F)).surjective x
  rw [← ClassFieldTheory.kummerCoeffEquivMuNRep_smul (n := p) (F := F) g y,
    kummerCoeff_smul_trivial (F := F) (p := p) hζ
      ((absoluteGaloisGroupRestrictEquiv F) g) y]

end Trivial

end L20261018

#print axioms L20261018.kce_eq_eDouble_comp
#print axioms L20261018.kummerCoeff_smul_trivial
#print axioms L20261018.muNRep_smul_trivial
