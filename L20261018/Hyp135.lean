import L20261018.Hyp134
import L20261018.Hyp123

/-!
# R977：**T3 的 `hUU` 假设解除** —— `\ker\bar v` 上的杯积直接为零

R976 已把 `hUU` 证成定理。本轮把它接到 T3 的消费链上，并给出**比 `tame_uu` 更强**的结论：

**`ker_cup_eq_zero`**：`y, z ∈ \ker\bar v` ⟹ **`y ⌣ z = 0`**（不只是 `res (y ⌣ z) = 0`）。
由 `Hyp134.ker_dependent` ＋ `Hyp130.cup_eq_zero_of_left/right_mem_span` 直接得。

**`ramified_vanishing_units'`**：T3（论文 `lem:ramified-vanishing`）的 `tame_uu` 假设**已解除**，
只剩 `res` 与 `tame_u_pi`。

## ★ 关于 `IsUnit (p : 𝒪[F])`（本轮的诚实结论）

原先打算把它从 `hp : IsUnit (p : F)` 推出 —— **做不到，而且不该做**：
在**域** `F` 中每个非零元都是单位，故 `IsUnit (p : F)` 只等价于 `p ≠ 0 in F`（Kummer 理论要的正是这条，
见 `KummerBridge.kummerClass` 的 `hp`）；它**不**约束 `p` 在赋值环中的地位。
`IsUnit (p : 𝒪[F])` 等价于「`p` 在 `𝒪[F]` 中可逆」⟺「`v(p) = 0`」⟺「剩余特征 `≠ p`」，
**正是论文的节首假设「`\operatorname{char}K\ne p`，且 `\mu_p\subset F`」**
（`raw/L20261018.tex:982` 逐字；`prop:prelim-kummer-valuation`／`prop:prelim-residue`／`prop:prelim-witt`
的假设句 `:989`／`:1016`／`:1062` 各自重申）。
⟹ 它是**论文自带的假设**，不是本战役额外引入的缩小。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- **`\ker\bar v` 上杯积直接为零**（比 `tame_uu` 强：不需要 `res`）。

由 `Hyp134.ker_dependent`（`\ker` 内任两元线性相关）＋ `Hyp130` 的两条 span 引理。 -/
theorem ker_cup_eq_zero (hp : IsUnit (p : F)) (hp2 : NeZero (2 : ZMod p)) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F])) (y z : ↥(LinearMap.ker (valLin F p hp))) :
    GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p) = 0 := by
  have hy : valLin F p hp (y : GaloBase.V F p) = 0 := LinearMap.mem_ker.mp y.2
  have hz : valLin F p hp (z : GaloBase.V F p) = 0 := LinearMap.mem_ker.mp z.2
  rcases ker_dependent (F := F) (p := p) hp hπ hpu (y : GaloBase.V F p) (z : GaloBase.V F p)
    hy hz with h | h
  · exact cup_eq_zero_of_left_mem_span (F := F) (p := p) hp2 h
  · exact cup_eq_zero_of_right_mem_span (F := F) (p := p) hp2 h

/-- **T3（论文 `lem:ramified-vanishing`）的 `tame_uu` 假设已解除**：
只剩 `res`（T2）与 `tame_u_pi`（T3 的研究级边界）。

`tame_uu` 由 `ker_cup_eq_zero` 得（`res 0 = 0`），比原路线（先证 `hUU` 再用 `exists_unit_rep`）更强。 -/
-- @source file=raw/L20261018.tex locator=label:lem:ramified-vanishing quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem ramified_vanishing_units' (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    (hpu : IsUnit (p : 𝒪[F]))
    (res : GaloBase.H2 F p →ₗ[ZMod p] ↥(LinearMap.ker (valLin F p hp)))
    (tame_u_pi : ∀ y : ↥(LinearMap.ker (valLin F p hp)),
      res (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
        (KummerBridge.kummerClass F p hp π)) = y)
    (a1 a2 : Fˣ)
    (hne : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2),
      (valLin F p hp) u ≠ 0) :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p))
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) = ⊥ :=
  ramified_vanishing_reduced3 (F := F) (p := p) hp hp2 (hπ := hπ) (res := res)
    (tame_uu := fun y z => by
      rw [ker_cup_eq_zero (F := F) (p := p) hp (Assemble36.neZero_two_zmod (p := p) hp2)
        (hπ := hπ) hpu y z, map_zero])
    (tame_u_pi := tame_u_pi) (a1 := a1) (a2 := a2) hne hval

end L20261018
#print axioms L20261018.ker_cup_eq_zero
#print axioms L20261018.ramified_vanishing_units'
