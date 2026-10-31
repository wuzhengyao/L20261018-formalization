import Hyp129
import Hyp123

/-!
# R973：`hUU` 归约到**一条纯线性代数事实**（`\ker\bar v` 内任两元线性相关）

R972 的转向：`hUU` / `tame_uu` 的真正内容是
「`\ker\bar v` 是 1 维 ⟹ 其上的杯积由**交错性**恒为零」，
与「`bridgeKc` 与 `kummerClass` 的载体比较」无关。

本文件把归约**形式化**（四条机检）：

1. `cup_self`：`x ⌣ x = 0`（`p` 奇；由 `cup_skew` ＋ `2 • x⌣x = 0`）；
2. `cup_eq_zero_of_left_mem_span` / `_right_mem_span`：线性相关 ⟹ 杯积为零；
3. **`hUU_of_ker_le_one`**：**只要「`\ker\bar v` 内任两元线性相关」，`hUU` 即成立**
   （单位类的 `\bar v` 为零由 `valLin_kummerClass` ＋ `v(u)=1` 直接得到）。

⟹ 剩余缺口**只剩**：`hdep`（即 `\ker\bar v` 至多 1 维）。这是纯群论／维数事实，
已被 R972 定位为「`κˣ/(κˣ)^p` 的指数整除素数 `p`」。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- **交错性**：`p` 奇时 `x ⌣ x = 0`。由 `GaloBase.cup_skew`（`A.lean`）得 `x ⌣ x = -(x ⌣ x)`，
故 `2 • (x ⌣ x) = 0`，而 `2 ≠ 0`。 -/
theorem cup_self (hp2 : NeZero (2 : ZMod p)) (x : GaloBase.V F p) :
    GaloBase.cup (K := F) (p := p) x x = 0 := by
  have h : GaloBase.cup (K := F) (p := p) x x = -GaloBase.cup (K := F) (p := p) x x :=
    GaloBase.cup_skew (K := F) (p := p) x x
  have h2 : (2 : ZMod p) • GaloBase.cup (K := F) (p := p) x x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    abel
  exact (smul_eq_zero.mp h2).resolve_left (NeZero.ne (2 : ZMod p))

/-- 若 `x` 是 `y` 的倍数，则 `x ⌣ y = 0`。 -/
theorem cup_eq_zero_of_left_mem_span (hp2 : NeZero (2 : ZMod p)) {x y : GaloBase.V F p}
    (h : x ∈ Submodule.span (ZMod p) ({y} : Set (GaloBase.V F p))) :
    GaloBase.cup (K := F) (p := p) x y = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  rw [← hc, map_smul, LinearMap.smul_apply, cup_self (F := F) (p := p) hp2, smul_zero]

/-- 若 `y` 是 `x` 的倍数，则 `x ⌣ y = 0`。 -/
theorem cup_eq_zero_of_right_mem_span (hp2 : NeZero (2 : ZMod p)) {x y : GaloBase.V F p}
    (h : y ∈ Submodule.span (ZMod p) ({x} : Set (GaloBase.V F p))) :
    GaloBase.cup (K := F) (p := p) x y = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  rw [← hc, map_smul, cup_self (F := F) (p := p) hp2, smul_zero]

/-- **`hUU` 由「`\ker\bar v` 内任两元线性相关」推出**（本轮的关键归约）。

只用三件事：① 单位类的 `\bar v` 为零（`valLin_kummerClass` ＋ `v(u)=1`）；
② `\ker` 内任两元线性相关（**假设 `hdep`**）；③ 交错性（`cup_self`）。

**⟹ 从此 `hUU` 与载体比较无关**；唯一剩余缺口是 `hdep`（＝ `\ker\bar v` 至多 1 维）。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-residue quote="\partial_2((u)\cup(w))=0."
theorem hUU_of_ker_le_one (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p))
    (hdep : ∀ y z : GaloBase.V F p, valLin F p hp y = 0 → valLin F p hp z = 0 →
      y ∈ Submodule.span (ZMod p) ({z} : Set (GaloBase.V F p)) ∨
        z ∈ Submodule.span (ZMod p) ({y} : Set (GaloBase.V F p))) :
    ∀ u w : Fˣ, normalizedValuation F u = 1 → normalizedValuation F w = 1 →
      GaloBase.cup (K := F) (p := p)
        (KummerBridge.kummerClass F p hp u) (KummerBridge.kummerClass F p hp w) = 0 := by
  intro u w hu hw
  have hu0 : valLin F p hp (KummerBridge.kummerClass F p hp u) = 0 := by
    rw [valLin_kummerClass, valOfUnit, hu, toAdd_one', Int.cast_zero]
  have hw0 : valLin F p hp (KummerBridge.kummerClass F p hp w) = 0 := by
    rw [valLin_kummerClass, valOfUnit, hw, toAdd_one', Int.cast_zero]
  rcases hdep _ _ hu0 hw0 with h | h
  · exact cup_eq_zero_of_left_mem_span (F := F) (p := p) hp2 h
  · exact cup_eq_zero_of_right_mem_span (F := F) (p := p) hp2 h

end L20261018
#print axioms L20261018.cup_self
#print axioms L20261018.cup_eq_zero_of_left_mem_span
#print axioms L20261018.cup_eq_zero_of_right_mem_span
#print axioms L20261018.hUU_of_ker_le_one
