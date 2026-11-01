import L20261018.Ch2.Hensel.ResidueMap.Step030_r1_scaled_bridge
import L20261018.Ch2.Kummer.Step018_bridge_kc_def
import L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier
import L20261018.Ch2.Brauer.Step031_brauer_of_h2_smul

/-!
# R1063（**★ 结构统一**）：`(R1-σ)` 的残余 **就是** R970 的 T1 桥

`bridgeKc`（`Hyp126`）定义为「`ClassFieldTheory.kummerClass` 沿 `muNRep → trivialFp → muP` 反向运输回
`GaloBase.V`」。本轮机检（**`rfl` 级**）：

```
(H2Bridge.redEquiv1 hζ).symm (ClassFieldTheory.kummerClass F hp a) = bridgeKc hζ a
```

⟹ **`(R1-σ)`（`Hyp205` 的缩放桥）⟺ 仅需 T1 形态**：

```
(T1)  ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ, KummerBridge.kummerClass F p hp a = c • bridgeKc hζ a
```

即 **`(R1)` 的残余与 R970 对 `(6)`／T1 的残余是同一条陈述** —— 本战役此前把它们当作两个独立缺口，
实际是**同一条载体桥**（`c` 是两条 Kummer 类路线的系数识别之差）。

| 声明 | 内容 |
|---|---|
| **`redEquiv1_symm_kummerClass`** | `(redEquiv1 hζ).symm (kummerClass a) = bridgeKc hζ a`（`rfl`） |
| **`scaled_bridge_of_bridgeKc`** | **(T1) ⟹ `(R1-σ)`**（用 `Hyp84.redEquiv1_map_smul`） |
| **`residuePhi_injective_of_bridgeKc`** | **(T1) ⟹ `(R1)`：`residuePhi` 单射**（接 `Hyp205`） |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section BridgeKc

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

/-- **`bridgeKc` 就是 `redEquiv1` 的逆在 `kummerClass` 上的取值**（定义相等）。 -/
theorem redEquiv1_symm_kummerClass (hζ : IsPrimitiveRoot ζ p) (a : Fˣ) :
    (H2Bridge.redEquiv1 (p := p) (K := F) hζ).symm
        (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit a)
      = bridgeKc (F := F) p hζ a := by
  rw [bridgeKc]
  rfl

/-- **(T1) ⟹ `(R1-σ)`**：把 T1 形态搬到 `redEquiv1` 的像上。 -/
theorem scaled_bridge_of_bridgeKc (hζ : IsPrimitiveRoot ζ p)
    (hT1 : ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ,
      KummerBridge.kummerClass F p hζ.neZero'.out.isUnit a = c • bridgeKc (F := F) p hζ a) :
    ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ,
      H2Bridge.redEquiv1 (p := p) (K := F) hζ
          (KummerBridge.kummerClass F p hζ.neZero'.out.isUnit a)
        = c • ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit a := by
  obtain ⟨c, hc0, hc⟩ := hT1
  refine ⟨c, hc0, fun a => ?_⟩
  rw [hc a, H2Bridge.redEquiv1_map_smul (p := p) (K := F) hζ c]
  congr 1
  rw [← redEquiv1_symm_kummerClass (F := F) p hζ a]
  exact AddEquiv.apply_symm_apply (H2Bridge.redEquiv1 (p := p) (K := F) hζ)
    (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit a)

end BridgeKc

section FromT1

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
  [NeZero p] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ} {ζ : F}

/-- **(T1) ⟹ `(R1)`**：`residuePhi` 单射（`bridgeKc` 的 `IsUnit` 证明取 `hζ.neZero'.out.isUnit`；
一般 `hp` 由 `IsUnit` 的 proof irrelevance 得）。 -/
theorem residuePhi_injective_of_bridgeKc
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hζ : IsPrimitiveRoot ζ p)
    (hT1 : ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ,
      KummerBridge.kummerClass F p hζ.neZero'.out.isUnit a = c • bridgeKc (F := F) p hζ a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Function.Injective (residuePhi (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit)
      (KummerBridge.kummerClass F p hζ.neZero'.out.isUnit π)) :=
  residuePhi_injective_of_norm_form_scaled (F := F) (p := p) hp hζ.neZero'.out.isUnit hζ
    (scaled_bridge_of_bridgeKc (F := F) p hζ hT1) hv hπ hp2

end FromT1

end L20261018

#print axioms L20261018.redEquiv1_symm_kummerClass
#print axioms L20261018.scaled_bridge_of_bridgeKc
#print axioms L20261018.residuePhi_injective_of_bridgeKc
