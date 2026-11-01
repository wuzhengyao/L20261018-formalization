import L20261018.Hyp281
import L20261018.Hyp161

/-!
# R1158（**第 5 项第四块：一般 Hensel 的缺口**精确归约**为 `TameResidueFacts`（类无关）**）

## 本轮做什么

初等块 7 字段已由 `Hyp279`／`Hyp280` 机检（零 `IsNonarchimedeanLocalField`）。
本轮把它与 `Hyp161.nonempty_henselResidueData_iff`（**全抽象**）接起来，给出**精确归约**：

```
(∃ D : HenselResidueData (ZMod p) V H² (ker v̄) cup, D.val = v̄)  ⟺  TameResidueFacts cup v̄ (π)
```

其中 `v̄ = valH1LinearGen v hp`、`(π) = kummerClass F hp π`，上下文只有
`[Field F]` ＋ `v : Fˣ →* Multiplicative ℤ` ＋ `IsUnit (p : F)` ＋ `hskew`。

⟹ **第 5 项的全部剩余 = 一般 Hensel 情形下的 `TameResidueFacts`（＝ (R1) ∧ (R2)）**。
配合 `Hyp281.tame_pi_u_redundant`（第 3 个驯符号冗余），实质内容只剩
**`res` ＋ `tame_u_pi`（(R1)）＋ `tame_uu`（(R2)）**。

## 本轮

| 声明 | 内容 |
|---|---|
| **`generalHensel_reduction`** | ★★★★★ **一般 Hensel 下 `D` 的存在 ⟺ `TameResidueFacts`（类无关）** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

/-- ★★★★★ **一般 Hensel 下 `D` 的存在 ⟺ `TameResidueFacts`**（**零完备性**）。

左边是论文的 `D`（`val = v̄`）；右边是两条剩余事实。初等块已由 `Hyp279`／`Hyp280` 供给，
故第 5 项的剩余**恰为** `TameResidueFacts`。 -/
theorem generalHensel_reduction {F : Type} [Field F] {p : ℕ} [NeZero p] [Fact p.Prime]
    (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (hskew : ∀ x y, ((TauCeti.ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) x y
      = -(((TauCeti.ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) y x)) :
    (∃ D : HenselResidueData (ZMod p)
        ↑(continuousCohomology 1 (TauCeti.ClassFieldTheory.muNRep p F)).toModuleCat
        ↑(continuousCohomology (1 + 1) (TauCeti.ClassFieldTheory.muNRep p F)).toModuleCat
        ↥(LinearMap.ker (valH1LinearGen (p := p) v hp))
        ((TauCeti.ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1),
      D.val = valH1LinearGen (p := p) v hp) ↔
    TameResidueFacts ((TauCeti.ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hp)
      (TauCeti.ClassFieldTheory.kummerClass F hp π) :=
  nonempty_henselResidueData_iff _ _ _ (valH1Gen_kummerClass_pi v hp hπ) hskew

end L20261018

#print axioms L20261018.generalHensel_reduction
