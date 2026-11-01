import L20261018.Hyp691
import L20261018.Hyp449

/-!
# S61 R5：**(G2) 字面闭合** —— `Ch4TameSymbolHyp` 由 `MerkurjevSuslin` 推出

## 这一步在做什么

`G2-PLAN.md` §0 的 `(G2)` 字面陈述是「**去掉 `Ch4TameSymbolHyp`**，即证 `TameSymbolFactors`」。
`Hyp691` 已把 `TameSymbolFactors` 由 `MerkurjevSuslin`（论文 `thm:prelim-ms`）推出。
本件再补两段**短桥**，使 `Ch4TameSymbolHyp` 这个**具名假设本身**也成为定理（条件于 MS）：

```
TameSymbolFactors  ⟹  Ch4TameSymbolHyp                       （本件 §1，≈10 行）
MerkurjevSuslin    ⟹  TameSymbolFactors ⟹ Ch4TameSymbolHyp    （本件 §2 ＝ (G2) 字面闭合）
```

⟹ 战役的**总具名假设** `Ch4TameSymbolHyp`（`Hyp449`）不再"无证明"：
它的**全部**非机检输入就是 `MerkurjevSuslin` 一条。

## §1 的证明（`∂₂` 的两条性质就是 `tame` 的两条值性质）

取 `res` 之于 `TameSymbolFactors` 作 `d`（两者载体逐字相同：`VKG F p v hpF = ↥(ker v̄)`）：

| `Ch4TameSymbolHyp` 要求 | 来源 |
|---|---|
| `d (∪ y z) = 0`（`y z ∈ ker v̄`） | `d ∘ ∪ = tame` ⟹ `tame(y,z) = v̄(z)y − v̄(y)z = 0`（`Hyp680.tameExpr_uu`） |
| `d (∪ y (π)) = y` | `tame(y, (π)) = v̄((π))y − v̄(y)(π) = 1·y − 0 = y`（`Hyp680.tameExpr_u_pi` ＋ `Hyp162.valLinOf_pi`） |

**这两条正好是论文 `raw/L20261018.tex:1050` 的逐字**：
`\partial_2((u)\cup(\pi))=(\bar u)`、`\partial_2((u)\cup(w))=0`。

## 机检件

| 声明 | 内容 |
|---|---|
| **`ch4TameSymbolHyp_of_tameSymbolFactors`** | ★★★★★ `TameSymbolFactors ⟹ Ch4TameSymbolHyp`（**无条件**，只要 `v π = 1`） |
| **`ch4TameSymbolHyp_of_merkurjevSuslin`** | ★★★★★ ★**(G2) 字面闭合** |
| **`nonempty_henselResidueData_of_merkurjevSuslin`** | `∃ D, D.val = valLinOf v hpF`（`(R2)` 形态，经 `Hyp680` 的 `⟺`） |

## 诚实边界

* 本件**不证** `MerkurjevSuslin`（＝论文 `thm:prelim-ms`，Merkurjev 1982）。
* 本件**不**依赖 `[Finite (ResidueField)]`；`nonempty_henselResidueData_of_merkurjevSuslin`
  需 `NeZero (2 : ZMod p)`（`Hyp680` 的 `⟺` 的既有前提，从 `p ≠ 2` 可得）。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section Closure

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ}

/-- ★★★★★ **`TameSymbolFactors ⟹ Ch4TameSymbolHyp`**（`∂₂` 的两条值性质由 `tame` 的
`(单位,单位)=0` 与 `(单位,π)=单位` 两条值性质给出；`d := res`）。 -/
-- @source file=raw/L20261018.tex locator=line:1050 quote="\partial_2((u)\cup(\pi))=(\bar u),\partial_2((\pi)\cup(u))=-(\bar u),\partial_2((u)\cup(w))=0."
theorem ch4TameSymbolHyp_of_tameSymbolFactors (hpF : IsUnit (p : F)) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (h : TameSymbolFactors (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF)) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF := by
  obtain ⟨res, hres⟩ := h
  have hval : valLinOf (F := F) (p := p) v hpF (KummerBridge.kummerClass F p hpF π) = 1 :=
    valLinOf_pi (F := F) (p := p) v hpF hπ
  refine ⟨res, ?_, ?_⟩
  · intro y z
    rw [hres]
    exact tameExpr_uu (valLinOf (F := F) (p := p) v hpF) y z
  · intro y
    rw [hres]
    exact tameExpr_u_pi (valLinOf (F := F) (p := p) v hpF)
      (KummerBridge.kummerClass F p hpF π) hval y

/-- ★★★★★ ★**(G2) 字面闭合**：`MerkurjevSuslin ⟹ Ch4TameSymbolHyp`。

即 `Hyp449` 的**总具名假设**成为定理，其**唯一**非机检输入 ＝ 论文 `thm:prelim-ms`。 -/
theorem ch4TameSymbolHyp_of_merkurjevSuslin (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hv : ValCompat (F := F) v) (hp2 : p ≠ 2) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (hMS : MerkurjevSuslin (F := F) (p := p) hpF) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF :=
  ch4TameSymbolHyp_of_tameSymbolFactors (F := F) (p := p) (v := v) hpF hπ
    (tameSymbolFactors_of_merkurjevSuslin (F := F) (p := p) (v := v) hp hpF hv hp2 hMS)

/-- **(R2) 形态**：`∃ D, D.val = valLinOf v hpF`（经 `Hyp680.nonempty_henselResidueData_iff_tameSymbolFactors`）。 -/
theorem nonempty_henselResidueData_of_merkurjevSuslin (hp : IsUnit (p : ↥𝒪[F]))
    (hpF : IsUnit (p : F)) (hv : ValCompat (F := F) v) (hp2 : p ≠ 2) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2' : NeZero (2 : ZMod p))
    (hMS : MerkurjevSuslin (F := F) (p := p) hpF) :
    ∃ D : HenselResidueData (ZMod p) (GaloBase.V F p) (GaloBase.H2 F p)
        (VKG F p v hpF) (GaloBase.cup (K := F) (p := p)),
      D.val = valLinOf (F := F) (p := p) v hpF := by
  have hval : valLinOf (F := F) (p := p) v hpF (KummerBridge.kummerClass F p hpF π) = 1 :=
    valLinOf_pi (F := F) (p := p) v hpF hπ
  have h2 : (2 : ZMod p) ≠ 0 := fun h0 => NeZero.ne (2 : ZMod p) h0
  exact (nonempty_henselResidueData_iff_tameSymbolFactors
    (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hpF)
    (KummerBridge.kummerClass F p hpF π) hval (fun x y => GaloBase.cup_skew (K := F) (p := p) x y) h2).mpr
    (tameSymbolFactors_of_merkurjevSuslin (F := F) (p := p) (v := v) hp hpF hv hp2 hMS)

end Closure

end L20261018

/-! ## 机检读数（`#print axioms`） -/

#print axioms L20261018.ch4TameSymbolHyp_of_tameSymbolFactors
#print axioms L20261018.ch4TameSymbolHyp_of_merkurjevSuslin
#print axioms L20261018.nonempty_henselResidueData_of_merkurjevSuslin
