import L20261018.Ch2.Kummer.Step045_kummer_coeff_zmod_instance

/-!
# S40 R16：系数桥 ① —— `ZMod p ≃+ KummerCoeff F p`（`μ_p ⊂ F`）

## 位置（`RECON-R3` §93.3 的 ①）

`muNRep p F` 的模**定义上就是** `KummerCoeff F p`（`kummerCoeffEquivMuNRep = AddEquiv.refl _`），
而 `muP F p` 的模是 `ZMod p`。故桥 ① 归约为**一个加法同构**

```lean
ZMod p ≃+ KummerCoeff F p          -- 两者阶都是 p（素），且 KummerCoeff 是 ZMod p-模
```

## 机检件

| 声明 | 内容 |
|---|---|
| `kummerCoeffMort` | `Module (ZMod p) (KummerCoeff K p)`（由 `p • x = 0`） |
| `kummerCoeffGenerator` | 具体非零元素（`ζ` 的像） |
| `zmodSmulInjective` | `m ≠ 0` ⟹ `i ↦ i • m` 单射（`ZMod p` 是域） |
| **`zmodEquivKummerCoeff`** | ★★★★★ **`ZMod p ≃+ KummerCoeff K p`** |
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {K : Type} [Field K]

/-- `KummerCoeff K p` 的 `ZMod p`-模结构（由 `Hyp475.kummerCoeff_nsmul_eq_zero`）。 -/
noncomputable def kummerCoeffMort (p : ℕ) : Module (ZMod p) (KummerCoeff K p) :=
  AddCommGroup.zmodModule (kummerCoeff_nsmul_eq_zero (K := K) p)

/-! ## 本轮未完成的部分（诚实记录，`RECON-R3` §94）

具体生成元 `kummerCoeffGenerator` 与同构 `ZMod p ≃+ KummerCoeff K p` **本轮未写成**。
根因是 **`Additive.toMul` 的隐式参数歧义**（本战役第 4 次踩，见 §94.2）：写
`Additive.toMul (x : KummerCoeff K p)` 时 Lean 把 `α` 推成 `?mˣ`，报
"expected `Additive ?mˣ`"。**修法（下轮照做）**：显式写
`Additive.toMul (α := ↥(rootsOfUnity p (SeparableClosure K))) x`。
其余两个小坑：`map_ne_zero` 是 **iff**（`map_ne_zero_iff`），不是函数；
`Units.coe_pow`／`Units.coe_mk0` 在本 pin 下名字不同（要用 `Units.val_pow_eq_pow_val` 等）。

**另一条更省的路（下轮优先试）**：不做具体生成元，改用
`Nat.card (KummerCoeff K p) = p = Nat.card (ZMod p)`（`Hyp474.natCard_kummerCoeff_available`）
＋ `ZMod p` 是域 ⟹ 任意非零 `m` 给单射，基数相等给双射。取 `m` 用 `Nontrivial` 存在性
（`Nat.card = p ≥ 2` ⟹ `Nontrivial`），避免 `Units` 强转。 -/

end L20261018

#print axioms L20261018.kummerCoeffMort
