import L20261018.Hyp311
import L20261018.Hyp290
import L20261018.Hyp207

/-!
# R1203（`hbridge` 归约为**不含 `redEquiv1` 的单一等式**）

`hbridge` 原形是
`redEquiv1 hζ (KummerBridge.kummerClass a) = ClassFieldTheory.kummerClass a`。
`Hyp207.redEquiv1_symm_kummerClass` 说 `(redEquiv1 hζ).symm (ckc a) = bridgeKc a`。
因 `redEquiv1 hζ` 是**加法等价**（故单射），两边作用 `redEquiv1 hζ` 后得

```
hbridge  ⟺  KummerBridge.kummerClass F p hp a = bridgeKc hζ a
```

⟹ `redEquiv1` 从目标中**消失**，剩下的是两条 **Kummer 载体链**的等式。

## 本轮
| 声明 | 内容 |
|---|---|
| **`hbridge_iff_eq_bridgeKc`** | ★★★★★ `redEquiv1 (kc a) = ckc a ↔ kc a = bridgeKc a` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section BridgeReduce

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ p)

/-- ★★★★★ **`hbridge` 归约为 `kc a = bridgeKc a`**（`redEquiv1` 消失）。

由 `Hyp207.redEquiv1_symm_kummerClass` ＋ `redEquiv1` 的单射性
＋ `Hyp290.kummerClass_isUnit_proof_irrel`（`IsUnit` 见证无关）。 -/
theorem hbridge_iff_eq_bridgeKc (hp : IsUnit (p : F)) (a : Fˣ) :
    H2Bridge.redEquiv1 (p := p) (K := F) hζ (KummerBridge.kummerClass F p hp a)
        = ClassFieldTheory.kummerClass F hp a
      ↔ KummerBridge.kummerClass F p hp a = bridgeKc (F := F) p hζ a := by
  have hckc : ClassFieldTheory.kummerClass F hp a
      = ClassFieldTheory.kummerClass F (hζ.neZero'.out.isUnit) a :=
    kummerClass_isUnit_proof_irrel hp hζ.neZero'.out.isUnit a
  have h1 : ClassFieldTheory.kummerClass F (hζ.neZero'.out.isUnit) a
      = H2Bridge.redEquiv1 (p := p) (K := F) hζ (bridgeKc (F := F) p hζ a) := by
    rw [← redEquiv1_symm_kummerClass (F := F) (p := p) hζ a]
    exact ((H2Bridge.redEquiv1 (p := p) (K := F) hζ).apply_symm_apply _).symm
  rw [hckc, h1]
  exact (H2Bridge.redEquiv1 (p := p) (K := F) hζ).injective.eq_iff

end BridgeReduce

end L20261018

#print axioms L20261018.hbridge_iff_eq_bridgeKc
