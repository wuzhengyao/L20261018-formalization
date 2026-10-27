import L20261018.Hyp85
import L20261018.Hyp20
import L20261018.Hyp22
/-!
# 3.2(1)(2) **消参升档**（R901）：`ind`／`hind` 不再是参数

`Hyp20.theorem_3_2_1_kummer` 与 `Hyp22.theorem_3_2_2_kummer` 此前把
`ind : GaloBase.H2 F p → ℕ` 与 `hind : ∀ x ∈ span{h}, ind x ≤ p` 作为**参数**
（B 档，`STATUS.md` §真实形式化度）。本文件用

* **`Hyp82.indOfH2`**：论文的 `ind`（`Br` 类里除代数的指数），与
* **`Hyp85.hind_kummer`**：`span{h}` 上 `ind ≤ p` 的**定理**

把它们**全部消掉**，得到只带论文自身假设的版本：

```lean
theorem theorem_3_2_1_kummer' (hp : IsUnit (p:F)) (hp2 : p ≠ 2) (a1 a2 : Fˣ)
    (hne : (a₁)∪(a₂) ≠ 0) (hrank : rank Φ = 2) (b1 b2 : V) :
    indOfH2 ζ (cup (a₁) b1 + cup (a₂) b2) ≤ p
```

`ind` 取 `Hyp82.indOfH2`、`ζ` 取 `KummerBridge.primitiveRoot`
（`HasEnoughRootsOfUnity F p` 供给，`primitiveRoot_spec` 给本原性）。

## 主结果

* **`theorem_3_2_1_kummer'`**、**`theorem_3_2_2_kummer'`**：3.2(1)(2) 的**无参数版**。
-/

open TauCeti

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace L20261018

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- 论文的类 `(a₁) ∪ (a₂)`。 -/
noncomputable def paperCup (hp : IsUnit (p : F)) (a1 a2 : Fˣ) : GaloBase.H2 F p :=
  GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1)
    (KummerBridge.kummerClass F p hp a2)

/-- **3.2(1) 无参数版**：`rank Φ = 2` ⟹ `ind ≤ p`，其中 `ind` 是 `Hyp82.indOfH2`
（`Br` 类里除代数的指数），`hind` 由 `Hyp85.hind_kummer` 供给。 -/
-- @source file=raw/L20261018.tex locator=label:thm:rank-barrier quote="若 $\rank(\Phi)=2$，则 $\ind(D)\le p$；"
theorem theorem_3_2_1_kummer' (hp : IsUnit (p : F)) (hp2 : p ≠ 2) (a1 a2 : Fˣ)
    (hne : paperCup F p hp a1 a2 ≠ 0)
    (hrank : Module.rank (ZMod p)
      ↥(biKummerDataKummer F p hp a1 a2 hne).Phi.range = (2 : Cardinal))
    (b1 b2 : GaloBase.V F p) :
    H2Bridge.indOfH2 (p := p) (K := F) (KummerBridge.primitiveRoot_spec F p)
      (GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1) b1
        + GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a2) b2) ≤ p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := neZero_two_zmod (p := p) hp2
  refine BiKummerData.theorem_3_2_1 (biKummerDataKummer F p hp a1 a2 hne) p
    (H2Bridge.indOfH2 (p := p) (K := F) (KummerBridge.primitiveRoot_spec F p)) ?_ hrank b1 b2
  intro x hx
  exact H2Bridge.hind_kummer hp (KummerBridge.primitiveRoot_spec F p) a1 a2 hne x hx

/-- **3.2(2) 无参数版**：`ind = p²` ⟹ `rank Φ ≥ 3`。 -/
-- @source file=raw/L20261018.tex locator=label:thm:rank-barrier quote="若 $\ind(D)=p^2$，则 $\rank(\Phi)\ge3$。"
theorem theorem_3_2_2_kummer' (hp : IsUnit (p : F)) (hp2 : p ≠ 2) (a1 a2 : Fˣ)
    (hne : paperCup F p hp a1 a2 ≠ 0)
    (b1 b2 : GaloBase.V F p)
    (hD : H2Bridge.indOfH2 (p := p) (K := F) (KummerBridge.primitiveRoot_spec F p)
      (GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1) b1
        + GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a2) b2) = p ^ 2) :
    (3 : Cardinal) ≤ Module.rank (ZMod p)
      ↥(biKummerDataKummer F p hp a1 a2 hne).Phi.range := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := neZero_two_zmod (p := p) hp2
  refine BiKummerData.theorem_3_2_2 (biKummerDataKummer F p hp a1 a2 hne) p
    (Fact.out : p.Prime).one_lt
    (H2Bridge.indOfH2 (p := p) (K := F) (KummerBridge.primitiveRoot_spec F p)) ?_ b1 b2 hD
  intro x hx
  exact H2Bridge.hind_kummer hp (KummerBridge.primitiveRoot_spec F p) a1 a2 hne x hx

end L20261018

#print axioms L20261018.theorem_3_2_1_kummer'
#print axioms L20261018.theorem_3_2_2_kummer'
