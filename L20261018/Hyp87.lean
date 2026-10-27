import L20261018.Hyp82
import TauCeti.RingTheory.RootsOfUnity.ZMod

/-!
# 两个本原根下的 `zmodEquivRootsOfUnity` 相差一个纯量（R903）

`indOfH2` 对 ζ 的无关性分两块（见 `ASSUMPTIONS.md` 第 107 轮）：
**(a) 载体块**——两个本原 `p` 次单位根的系数同构相差一个单位纯量；**(b) 指数块**（基建任务）。

本文件做 (a) 的**核心群论事实**：若 `ζ' = ζ ^ n`（两者都是本原 `p` 次单位根），则

```lean
hζ'.zmodEquivRootsOfUnity i = hζ.zmodEquivRootsOfUnity ((n : ZMod p) * i)
```

即两个「把所选根送到 `1`」的等价**只差输入的纯量乘**。取 `.symm` 就得
「差一个**输出**纯量」，这正是 `muNRepEquivTrivialFp` 层面的所需关系。

（`muNRepEquivTrivialFp n F hζ = (kummerCoeffEquivMuNRep).symm.trans
(hζu.zmodEquivRootsOfUnity.symm.trans (trivialFpEquiv).symm.toAddEquiv)`，
故 ζ 只出现在这里。）

## 主结果

* `zmodEquivRootsOfUnity_eq_comp`：上式（`AddEquiv` 层的复合形式）。
* `zmodEquivRootsOfUnity_symm_eq_smul`：**取逆后的纯量形式**——存在非零 `c : ZMod p` 使
  `hζ'.zmodEquivRootsOfUnity.symm = c • hζ.zmodEquivRootsOfUnity.symm`。
-/

open TauCeti

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace PrimitiveRootScalar

variable {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [Fact p.Prime] [NeZero p]

/-- **两个本原根的等价只差输入的纯量乘**（`natCast` 形式）：`ζ' = ζ ^ n` ⟹
`hζ'.zmodEquivRootsOfUnity k = hζ.zmodEquivRootsOfUnity (n * k)`。 -/
theorem zmodEquivRootsOfUnity_eq_comp_natCast {ζ ζ' : Rˣ} (hζ : IsPrimitiveRoot ζ p)
    (hζ' : IsPrimitiveRoot ζ' p) {n : ℕ} (hn : ζ ^ n = ζ') (k : ℕ) :
    hζ'.zmodEquivRootsOfUnity (k : ZMod p) = hζ.zmodEquivRootsOfUnity ((n * k : ℕ) : ZMod p) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [IsPrimitiveRoot.coe_zmodEquivRootsOfUnity_apply_natCast,
    IsPrimitiveRoot.coe_zmodEquivRootsOfUnity_apply_natCast, ← hn, pow_mul]

/-- **两个本原根的等价只差输入的纯量乘**（任意 `ZMod p` 元素）。 -/
theorem zmodEquivRootsOfUnity_eq_comp {ζ ζ' : Rˣ} (hζ : IsPrimitiveRoot ζ p)
    (hζ' : IsPrimitiveRoot ζ' p) {n : ℕ} (hn : ζ ^ n = ζ') (i : ZMod p) :
    hζ'.zmodEquivRootsOfUnity i = hζ.zmodEquivRootsOfUnity ((n : ZMod p) * i) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [zmodEquivRootsOfUnity_eq_comp_natCast (p := p) hζ hζ' hn i.val]
  congr 1
  rw [Nat.cast_mul, ZMod.natCast_zmod_val]

/-- **取逆后的纯量形式**：`ζ' = ζ ^ n`（`n` 在 `ZMod p` 中非零）⟹
`hζ'.zmodEquivRootsOfUnity.symm = n⁻¹ • hζ.zmodEquivRootsOfUnity.symm`。

这是提到 `muNRepEquivTrivialFp` 层所需的形式（那里出现的是 `.symm`）。 -/
theorem zmodEquivRootsOfUnity_symm_eq_smul {ζ ζ' : Rˣ} (hζ : IsPrimitiveRoot ζ p)
    (hζ' : IsPrimitiveRoot ζ' p) {n : ℕ} (hn : ζ ^ n = ζ') (hn0 : (n : ZMod p) ≠ 0)
    (i : Additive (rootsOfUnity p R)) :
    hζ'.zmodEquivRootsOfUnity.symm i
      = (n : ZMod p)⁻¹ • hζ.zmodEquivRootsOfUnity.symm i := by
  -- `y := hζ'.f.symm i`，则 `i = hζ.f (n • y)`
  have h1 : hζ.zmodEquivRootsOfUnity ((n : ZMod p) * (hζ'.zmodEquivRootsOfUnity.symm i)) = i := by
    have hc := zmodEquivRootsOfUnity_eq_comp (p := p) hζ hζ' hn
      (hζ'.zmodEquivRootsOfUnity.symm i)
    rw [← hc, AddEquiv.apply_symm_apply]
  have h2 : hζ.zmodEquivRootsOfUnity.symm i
      = (n : ZMod p) • (hζ'.zmodEquivRootsOfUnity.symm i) := by
    rw [smul_eq_mul]
    exact (AddEquiv.symm_apply_eq (hζ.zmodEquivRootsOfUnity)).mpr h1.symm
  rw [h2, smul_smul, inv_mul_cancel₀ hn0, one_smul]

end PrimitiveRootScalar

#print axioms PrimitiveRootScalar.zmodEquivRootsOfUnity_symm_eq_smul
#print axioms PrimitiveRootScalar.zmodEquivRootsOfUnity_eq_comp_natCast
#print axioms PrimitiveRootScalar.zmodEquivRootsOfUnity_symm_eq_smul
#print axioms PrimitiveRootScalar.zmodEquivRootsOfUnity_eq_comp
