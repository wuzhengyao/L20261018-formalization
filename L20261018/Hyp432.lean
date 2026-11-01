import L20261018.Hyp431
import L20261018.Hyp389

/-!
# S39 第 6 轮（B 第 2 步）：**把 B 钉成一条等价**（`Hyp432`）

## 本轮的三个机检结论

### 1. `Disjoint ⟺ ∃ d`（**双向**，B 的唯一残余就是这一条）

`Hyp431` 给了 `Disjoint ⟹ ∃d`；本轮补**逆方向** `∃d ⟹ Disjoint`（抽象引理，三行证明）：

> 设 `z ∈ im Φ ∩ residueSpan`。`z = Φ y = ∪(infl y) π` ⟹ `d z = y`；
> 而 `z ∈ residueSpan = span{∪(infl a)(infl b)}` ⟹ `d z = 0` ⟹ `y = 0` ⟹ `z = 0`。

⟹ B **不**是「造一个结构」的问题，而是「造一条线性映射」的问题 —— 两者等价，任选其一。

### 2. 完备情形（`Hyp139`／`Hyp162` 路线）是 **`residueSpan = ⊥` 的退化特例**

完备情形用的关键事实是 `ker_cup_eq_zero : ∀ y z ∈ ker v̄, y∪z = 0`
（即 `residueSpan = ⊥`）。本轮机检：`residueSpan = ⊥ ⟹ Disjoint (im Φ) residueSpan`
（`bot_disjoint` 一行）。**但 `residueSpan = ⊥` 只在有限剩余域成立**
（`UnitsCupVanish ⟺ H²(κ,μ_p)=0`）⟹ **完备情形对本问题不给模板**。

### 3. 因此 B 的精确残余（`∅-open`，理由已定位）

`Disjoint (residuePhi cup val π).range (residueSpan cup val)` 对一般 `κ` 需要
**GS 6.8.5／6.8.8 的 `∂₂`**（tame symbol）—— 其 `∂₂` 在库中**不存在**：
TauCeti 只到 HS 的前三项（`Inflation/Basic.explicitInfl1/2` ＋
`FiveTerm.explicitInfResConj_exact`），**缺 transgression**
`tg : H¹(N,M)^N → H²(G⧸N, M^N)`。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

/-! ## 1. 抽象层：`∃ d ⟹ Disjoint`（`Hyp431` 的逆方向） -/

section Abstract

variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]
  {H2 : Type*} [AddCommGroup H2] [Module k H2]
  {VK : Type*} [AddCommGroup VK] [Module k VK]

/-- **`∃ d ⟹ Disjoint`**：若 `d` 在「单位杯积块」上为 `0`、且在 `∪(·)π` 上还原 `η`，
则 `im Φ` 与单位杯积块不相交。

证明只用 `d` 的两条性质 ＋ 线性性（`residueSpan` 按定义是该块张成的子空间）。 -/
theorem disjoint_of_exists_residueMap (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) (π : V)
    (infl : VK →ₗ[k] V) (hinfl : ∀ y : VK, val (infl y) = 0)
    (hsurj : ∀ x : V, val x = 0 → ∃ y : VK, infl y = x)
    (d : H2 →ₗ[k] VK)
    (hd1 : ∀ y z : VK, d ((cup (infl y)) (infl z)) = 0)
    (hd2 : ∀ y : VK, d ((cup (infl y)) π) = y) :
    Disjoint (LinearMap.range (residuePhi cup val π)) (residueSpan cup val) := by
  rw [Submodule.disjoint_def]
  intro z hz hz'
  obtain ⟨y, rfl⟩ := hz
  obtain ⟨y₀, hy₀⟩ := hsurj (y : V) y.2
  -- `d` 在单位杯积块上为零
  have hker : residueSpan cup val ≤ LinearMap.ker d := by
    rw [residueSpan, Submodule.span_le]
    rintro _ ⟨⟨a, b⟩, rfl⟩
    show d ((cup (a : V)) (b : V)) = 0
    obtain ⟨a₀, ha₀⟩ := hsurj (a : V) a.2
    obtain ⟨b₀, hb₀⟩ := hsurj (b : V) b.2
    rw [← ha₀, ← hb₀]
    exact hd1 a₀ b₀
  have hΦ : (residuePhi cup val π) y = (cup (infl y₀)) π := by
    show (cup (y : V)) π = _
    rw [hy₀]
  have hmem : d ((residuePhi cup val π) y) = 0 := by
    have := hker hz'
    rwa [LinearMap.mem_ker] at this
  rw [hΦ, hd2 y₀] at hmem
  rw [hΦ, hmem, map_zero infl]
  simp

end Abstract

/-! ## 2. 完备情形的退化性：`residueSpan = ⊥ ⟹ Disjoint` -/

section Degenerate

variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]
  {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- ★★★ **完备情形（`ker_cup_eq_zero`）是 `residueSpan = ⊥` 的退化特例**：
`residueSpan = ⊥` 时 `Disjoint` 平凡（`bot_disjoint` 一行）。 -/
theorem disjoint_of_residueSpan_eq_bot (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) (π : V)
    (h : residueSpan cup val = ⊥) :
    Disjoint (LinearMap.range (residuePhi cup val π)) (residueSpan cup val) := by
  rw [h]
  exact disjoint_bot_right

end Degenerate

/-! ## 3. 具体层：**双向等价**（B 的唯一残余） -/

section Concrete

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★★★★ **B 的唯一残余，双向机检**：

```
Disjoint (im(∪·π)) (单位杯积块)   ⟺   ∃ d 满足 ∂₂ 的两条值性质
```

⟹ 「造 `∂₂`」与「证 `Disjoint`」**等价**，不能拿一个换另一个。
（`⟸` 由上节的抽象引理，`⟹` 由 `Hyp431.exists_residueMap_of_disjoint`。） -/
theorem disjoint_iff_exists_residueMap {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Disjoint
      (residuePhi (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
        (KummerBridge.kummerClass F p hpF π)).range
      (residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF))
    ↔ ∃ d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF,
        (∀ y z : VKG F p v hpF,
          d (((GaloBase.cup (K := F) (p := p)) (y : GaloBase.V F p)) (z : GaloBase.V F p)) = 0) ∧
        (∀ y : VKG F p v hpF,
          d (((GaloBase.cup (K := F) (p := p)) (y : GaloBase.V F p))
            (KummerBridge.kummerClass F p hpF π)) = y) := by
  constructor
  · exact exists_residueMap_of_disjoint (F := F) (p := p) (v := v) (π := π) hζ hp hpF hv hπ hp2
  · rintro ⟨d, hd1, hd2⟩
    exact disjoint_of_exists_residueMap (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π)
      (LinearMap.ker (valLinOf (F := F) (p := p) v hpF)).subtype
      (fun y => y.2)
      (fun x hx => ⟨⟨x, hx⟩, rfl⟩) d hd1 hd2

end Concrete

end L20261018

#print axioms L20261018.disjoint_of_exists_residueMap
#print axioms L20261018.disjoint_of_residueSpan_eq_bot
#print axioms L20261018.disjoint_iff_exists_residueMap
