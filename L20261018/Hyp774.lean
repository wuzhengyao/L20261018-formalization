import Hyp773

/-!
# S73 R6：★★★★★ **`∂₂` 的机检定义 ＋ `prop:prelim-residue` 归约到「恰好一条方程」**

## 本轮做了什么

1. **`d_F5`**：把论文的 `∂₂` 建成 **`def`**——`d := F5_uncond ∘ ∂²`（`GaloBase.H2 F p →ₗ[ℤ/p] VKG`）。
   这是 `prop:prelim-residue`(1) 里那个 `∂₂` 的机检化身。
2. **`hd_infl_d_F5`**：`d (cup y z) = 0`（`y z ∈ VKG`）——`Hyp773` 的直接改写。
3. **`tameResidueFacts_of_hd_cup_pi`**：假设**唯一一条** `hcup : ∀ y, d (cup y (kummerClass π)) = y`，
   即得 `TameResidueFacts`（`Hyp342` 的引擎）。

**⟹ 至此 `prop:prelim-residue` 的无条件化归约为：**

```
一条方程  hcup : ∀ y : VKG, d (cup y (kummerClass π)) = y          ← GS 6.8.4（投影公式）＋ ∂¹((−π)) = 1
＋ 三条技术实例（DiscreteTopology / ContinuousSMul (H1 ↥I) / ContinuousSMul (TBI)）
```
**再没有具名数学假设**（`H-conj1` 已由 `Hyp771` 兑现；`F5` 已由 `Hyp772` 建成；`hd_infl` 已由 `Hyp773` 证明）。

## 这条方程是什么（GS 逐字）

`raw/GilleSzamuely2017.tex` 的 `lemma-residue-cup-product`（印版 6.8.4）：

> `\partial^{p+q}(a\cup\operatorname{Inf}(b))=\partial^{p}(a)\cup b.`

配 `prop-specialization-section` 的证明里的 `∂¹((−π)) = 1`（`:9647`）。
本战役的五步符号账见 `LESSONS` **D74**（① `y ∈ VKG ⟹ y = Inf a`；② 上式；③ `∂¹(π) = −1`；
④ `∂¹(π) ∪ a = −a`；⑤ `Inf a ∪ π = −π ∪ Inf a`）。

## 诚实边界

* `d_F5` 依赖 `Hyp772.F5_uncond` 的构造参数（`ζ hζ hgen x hx`）与技术实例——它们**不是**数学假设。
* `hcup` **未证**：它是缺口 ③ 的全部内容。本件的价值是把「缺口 ③」压成**一条可陈述的方程**，
  且其左右两端都已是机检对象。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
variable (hcop : p.Coprime q)

/-- ★★★★★ **论文的 `∂₂`（机检化）**：`d := F5_uncond ∘ ∂²`，`GaloBase.H2 F p →ₗ[ℤ/p] VKG`。

`v` 取 `TauCeti.normalizedValuation F`（`Hyp747` 文件头论证：这只是归约）。 -/
noncomputable def d_F5
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
    (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p) (hpq' : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hx : x ≠ 0) :
    GaloBase.H2 F p →ₗ[ZMod p] VKG F p (TauCeti.normalizedValuation F) hp :=
  (F5_uncond (F := F) (p := p) (q := q) hp hpq hpq' ζ hζ hgen x hx).comp
    (AddMonoidHom.toZModLinearMap p (deltaTwoGaloBase' (F := F) p q hcop))

/-- ★★★★ **`hd_infl`**：`d (cup y z) = 0`（`y z ∈ VKG`）——`Hyp773` 的改写。 -/
theorem hd_infl_d_F5
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
    (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p) (hpq' : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hx : x ≠ 0)
    (y z : VKG F p (TauCeti.normalizedValuation F) hp) :
    d_F5 (F := F) (p := p) (q := q) (hcop := hcop) hp hpq hpq' ζ hζ hgen x hx
      (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0 :=
  hd_infl_F5_uncond (F := F) (p := p) (q := q) (hcop := hcop) hp hpq hpq' ζ hζ hgen x hx y z

/-- ★★★★★ **`prop:prelim-residue` 归约到「恰好一条方程」**。

假设 `hcup : ∀ y ∈ VKG, d (cup y (kummerClass π)) = y`（＝ GS `lemma-residue-cup-product`（6.8.4）
＋ `∂¹((−π)) = 1` 的全部内容），则由 `Hyp342.tameResidueFacts_Galo_of_residueMap` 得
`TameResidueFacts`（论文 `prop:prelim-residue` 的两条值）。 -/
theorem tameResidueFacts_of_hd_cup_pi
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
    (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p) (hpq' : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hx : x ≠ 0)
    (π : Fˣ)
    (hcup : ∀ y : VKG F p (TauCeti.normalizedValuation F) hp,
      d_F5 (F := F) (p := p) (q := q) (hcop := hcop) hp hpq hpq' ζ hζ hgen x hx
        (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
          (KummerBridge.kummerClass F p hp π)) = y) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) (TauCeti.normalizedValuation F) hp)
      (KummerBridge.kummerClass F p hp π) :=
  tameResidueFacts_Galo_of_residueMap (F := F) (p := p) (v := TauCeti.normalizedValuation F)
    (π := π) hp (d_F5 (F := F) (p := p) (q := q) (hcop := hcop) hp hpq hpq' ζ hζ hgen x hx)
    (fun y z => hd_infl_d_F5 (F := F) (p := p) (q := q) (hcop := hcop) hp hpq hpq' ζ hζ hgen x hx y z)
    hcup

end L20261018

#print axioms L20261018.d_F5
#print axioms L20261018.hd_infl_d_F5
#print axioms L20261018.tameResidueFacts_of_hd_cup_pi
