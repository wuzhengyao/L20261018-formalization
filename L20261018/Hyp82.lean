import L20261018.Hyp81
import L20261018.Hyp54
import TauCeti.Algebra.CentralSimple.Index
import TauCeti.Algebra.BrauerGroup.Division

/-!
# `ind` 的**定义**：`H²(G_F, μ_p)` 上的指数函数（R897 第二件）

`Hyp81` 打通了 `GaloBase.H2 F p →+ Br F`（`brOfH2`）。本文件把它变成论文的 `ind`：

```lean
indOfH2 x = index of (the central division algebra representing the class brOfH2 x)
```

即「该上同调类对应的 Brauer 类里那个除代数的指数」——这正是论文 `ind(D)` 的类层面形式
（论文的 `D` 只是该类的一个代表；`Hyp54.index_eq_of_mk_eq` 保证与代表选取无关）。

## 为什么这样定义是对的

* `BrauerGroup.exists_eq_mk_centralDivisionRing`：每个 Brauer 类有**有限维中心除代数**代表；
* `TauCeti.Algebra.index`：中心单代数的指数（Wedderburn 呈现里除代数的次数），
  且 `index_eq_of_algEquiv`／`index_matrix`／`index_eq_of_mk_eq` 使它**只依赖 Brauer 类**。

## 主结果

* `brauerOfH2`：`GaloBase.H2 F p → BrauerGroup F`（`brOfH2` 沿 `brauerGroupEquivBr` 回传）。
* `DivisionRep`／`divisionRep`：类里的除代数代表（选择）。
* **`indOfH2 : GaloBase.H2 F p → ℕ`**——论文的 `ind`。
* **`indOfH2_le_of_class_eq`**：若某类的像恰是某个 CSA `A` 的类且 `index A ≤ p`，
  则 `indOfH2 ≤ p`。**这是 `hind` 的模组化形式**：剩下的唯一缺口变成
  「`brOfH2 (A ∪ B)` 落在符号代数的类上」（即 `cor:symbol-cup` 的类形式 ＋ 纯量移动）。
-/

open TauCeti

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace H2Bridge

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K}

/-- **`H²` 类对应的 Brauer 类**（`Br F ≅ BrauerGroup F` 的回传）。 -/
noncomputable def brauerOfH2 (hζ : IsPrimitiveRoot ζ p) (x : GaloBase.H2 K p) :
    BrauerGroup K :=
  Additive.toMul ((ClassFieldTheory.brauerGroupEquivBr K).symm (brOfH2 hζ x))

/-! ### 类里的除代数代表 -/

/-- **Brauer 类的一个除代数代表**：有限维中心除代数 `D` ＋ 类等式。 -/
structure DivisionRep (K : Type) [Field K] (x : BrauerGroup K) where
  /-- 代表元 -/
  D : Type
  [instDR : DivisionRing D]
  [instAlg : Algebra K D]
  [instCentral : Algebra.IsCentral K D]
  [instFin : FiniteDimensional K D]
  /-- 类等式 -/
  mk_eq : BrauerGroup.mk (CSA.of K D) = x

/-- 每个 Brauer 类都有除代数代表（`exists_eq_mk_centralDivisionRing`）。 -/
theorem nonempty_divisionRep (x : BrauerGroup K) : Nonempty (DivisionRep K x) := by
  obtain ⟨D, hDR, hAlg, hCentral, hFin, hEq⟩ :=
    BrauerGroup.exists_eq_mk_centralDivisionRing K x
  let W : DivisionRep K x :=
    { D := D, instDR := hDR, instAlg := hAlg, instCentral := hCentral, instFin := hFin, mk_eq := hEq.symm }
  exact ⟨W⟩

/-- 取定一个代表。 -/
noncomputable def divisionRep (x : BrauerGroup K) : DivisionRep K x :=
  Classical.choice (nonempty_divisionRep x)

/-- 代表的指数（把 `letI` 包起来，便于对 `W` 做重写）。 -/
noncomputable def DivisionRep.index {x : BrauerGroup K} (W : DivisionRep K x) : ℕ :=
  letI := W.instDR
  letI := W.instAlg
  letI := W.instCentral
  letI := W.instFin
  Algebra.index K W.D

/-! ### 论文的 `ind` -/

/-- **论文的 `ind`**：`H²(G_F, μ_p)` 的一个类 ↦ 相应 Brauer 类里除代数的指数。

（论文里 `ind` 作用在类的一个代表 `D` 上；此处作用在类本身——`index` 对 Brauer 类良定，
`Hyp54.index_eq_of_mk_eq`。） -/
noncomputable def indOfH2 (hζ : IsPrimitiveRoot ζ p) (x : GaloBase.H2 K p) : ℕ :=
  (divisionRep (brauerOfH2 hζ x)).index

/-- `indOfH2` 的定义展开式。 -/
theorem indOfH2_def (hζ : IsPrimitiveRoot ζ p) (x : GaloBase.H2 K p) :
    indOfH2 hζ x = (divisionRep (brauerOfH2 hζ x)).index :=
  rfl

/-! ### `hind` 的模组化形式 -/

/-- **`hind` 的模组化形式**：若 `x` 的 Brauer 类恰是某个中心单代数 `A` 的类，且
`index K A ≤ p`，则 `indOfH2 hζ x ≤ p`。

**⟹ 剩下的唯一缺口**变成：「`brOfH2 hζ (A ∪ B)` 落在某个**符号代数**的类上」。
`symbolAlg_brauerClass_eq_verbatim`（`Hyp77`）给的是反方向（从符号代数到 `kummerBrauerClass`），
故下一步是把两者用一次 `brOfH2_cup` ＋ Kummer 类比较接起来。 -/
theorem indOfH2_le_of_class_eq (hζ : IsPrimitiveRoot ζ p) {x : GaloBase.H2 K p}
    {A : Type} [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A]
    (hA : brauerOfH2 hζ x = BrauerGroup.mk (CSA.of K A))
    (hle : Algebra.index K A ≤ p) :
    indOfH2 hζ x ≤ p := by
  set W := divisionRep (brauerOfH2 hζ x) with hW
  letI := W.instDR
  letI := W.instAlg
  letI := W.instCentral
  letI := W.instFin
  have hmk : BrauerGroup.mk (CSA.of K W.D) = BrauerGroup.mk (CSA.of K A) := by
    rw [W.mk_eq, hA]
  have hidx : W.index = Algebra.index K A := by
    simp only [DivisionRep.index]
    exact SymbolIndex.index_eq_of_mk_eq hmk
  exact hidx.trans_le hle

end H2Bridge

#print axioms H2Bridge.nonempty_divisionRep
#print axioms H2Bridge.indOfH2_def
#print axioms H2Bridge.indOfH2_le_of_class_eq
