import Hyp772

/-!
# S73 R5：★★★★★ **缺口 ② 收尾**——`hd_infl` 对本战役的 `F5` 成立

## 位置

```
F5_uncond（Hyp772）：H¹(Γ⧸I, H¹(I,ℤ/p)) →ₗ[ℤ/p] VKG
  ⟹ 本件：d := F5 ∘ ∂²  满足  d (cup y z) = 0          （= prop:prelim-residue(1) 的第一条，`hd_infl`）
  ⟹ 缺口 ③（`hd_cup_pi`：`d (cup (inf y) π) = y`）仍是唯一剩下的
```

## 做了什么（零新数学）

`Hyp757.hd_infl_of_linear` 说：**对任意线性 `F5`**，`d := F5 ∘ ∂²` 在 `cup y z`（`y z ∈ VKG`）上为 `0`。
本件把 `Hyp772.F5_uncond` 代进去，并把 `hd_infl_of_linear` 要的 `{v}`／`hv : ValCompat v`／
`hπ : v π = ofAdd 1` 与 `TauCeti.normalizedValuation F` 对齐：

* `L20261018.valCompat_normalizedValuation F : ValCompat (normalizedValuation F)`；
* `TauCeti.exists_isUniformizer F` 给 `π`，`TauCeti.isUniformizer_def π` 把它转成
  `(normalizedValuation F) π = Multiplicative.ofAdd 1`。

（`Hyp747` 文件头已论证：`ValCompat v` ＋ `v π = 1` 就刻画 `normalizedValuation`，故这不是限制。）

## 交付

| 声明 | 内容 |
|---|---|
| **`hd_infl_F5_uncond`** | ★★★★★ `(F5_uncond ∘ ∂²) (cup y z) = 0`（`y z ∈ VKG`） |

## 诚实边界

* 仍带三条**技术实例**（`ContinuousSMul (H1 ↥I)`／`ContinuousSMul (TBI …)`／`DiscreteTopology`），
  与 `Hyp743`／`Hyp755`／`Hyp757` 同一批（`STARTUP` §3）。
* 本件**不**含缺口 ③（`hd_cup_pi`）：那需要 GS 6.8.4（投影公式）＋ `∂¹(π) = −1`。
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

/-- ★★★★★ **`hd_infl` 对本战役的 `F5`**：`d := F5_uncond ∘ ∂²` 满足 `d (cup y z) = 0`。

`Hyp757.hd_infl_of_linear`（对任意线性 `F5`）＋ `Hyp772.F5_uncond`；`v` 取 `normalizedValuation`
（`valCompat_normalizedValuation`），`π` 取均匀化子（`exists_isUniformizer` ＋ `isUniformizer_def`）。 -/
theorem hd_infl_F5_uncond
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
    ((F5_uncond (F := F) (p := p) (q := q) hp hpq hpq' ζ hζ hgen x hx).comp
        (AddMonoidHom.toZModLinearMap p (deltaTwoGaloBase' (F := F) p q hcop)))
      (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0 := by
  obtain ⟨π, hπu⟩ := TauCeti.exists_isUniformizer F
  exact hd_infl_of_linear (F := F) (p := p) (q := q) (hcop := hcop)
    hp (valCompat_normalizedValuation F) ((TauCeti.isUniformizer_def π).mp hπu)
    (F5_uncond (F := F) (p := p) (q := q) hp hpq hpq' ζ hζ hgen x hx) y z

end L20261018

#print axioms L20261018.hd_infl_F5_uncond
