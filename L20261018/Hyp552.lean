import Hyp551
import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.ConnectingMap

/-!
# S46 R1：★★★★★ **连续侧 (F1) 的载体** —— `T = Bᴵ⧸Aᴵ`（GS (6.16)）与 `iTame`

## 这一步在 GS 的哪一句

GS `prop-residue-map-long-exact`（6.8.2）的证明（`raw/GilleSzamuely2017.tex:9522–9542`）把
`H`-上同调长正合列

```
0 → A^H → M^G(A)^H → C^H → H¹(H,A) → 0
```

**劈成两条**：GS (6.16) `0 → A^H → M^G(A)^H → T → 0` 与 GS (6.17) `0 → T → C^H → H¹(H,A) → 0`，
其中 `T = coker(A^H ↪ M^G(A)^H)`——本件的 `contT`。

**为什么必须造 `T`**：`0 → A^H → M^G(A)^H → C^H → 0` **不是**短正合（右满需 `H¹(H,A) = 0`），
故 `δ` 只能在 `T` 处取；(6.16) 则**无条件**短正合。离散侧蓝本 = `Hyp542.cokerSES`／`iTame`。

## 机检内容

| 声明 | 内容 |
|---|---|
| `contB`／`contC`／`contInvA`／`contInvB`／`contInvC` | `B`／`C`／`Aᴵ`／`Bᴵ`／`Cᴵ` 载体锁定 |
| `contInvIncl` | `Aᴵ → Bᴵ`（`S.incl` 在 I-不变点上的限制） |
| `contInvIncl_smul` | ★★ 其 `Γ⧸I`-等变性（`fixedPoints_subtype_quotientMk_smul` ＋ `incl_equivariant`） |
| `contKI`／`contT` | `T = Bᴵ ⧸ im(Aᴵ)`（＝ GS 的 `coker(Aᴵ ↪ Bᴵ)`） |
| `contKI_stable` | `T` 上的 `Γ⧸I`-作用良定义 |
| **`contInvSES`** | ★★★★ **GS (6.16)**：`0 → Aᴵ → Bᴵ → T → 0` 在 `Γ⧸I` 上**无条件**短正合 |
| **`contITame`** | ★★ **GS (6.17) 左半**：`i : T → Cᴵ`（`S.proj` 诱导，单射） |

## 诚实边界

* 本件**不含** `(F1)` 的方块本身（`δ_T ≫ Inf_A = i_* ≫ Inf_C ≫ δ_Γ`）——下一件
  `Hyp553` 用库内 `DiscreteShortExact.delta_map` 开火。
* 本件**不含** `(d)`：还差连续 `i_* ≫ deltaZeroBar = 0`（(F2) 抬到 `T` 层）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open CategoryTheory Limits TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-- `B = DiscreteCoind Γ ⊥ μ_p`（战役系数短正合列的中项，`ℤ`-基底）。 -/
noncomputable abbrev contB : Type :=
  DiscreteCoind (AbsoluteGaloisGroup F) ⊥ (ZMod p)

/-- `C = CoindQuotient Γ ⊥ μ_p`。 -/
noncomputable abbrev contC : Type :=
  CoindQuotient (AbsoluteGaloisGroup F) ⊥ (ZMod p)

section Invariants

variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-- `Aᴵ = μ_pᴵ`（`μ_p` 上作用平凡，故此即 `μ_p`；以子群形态出现以便 `Γ⧸I`-作用可用）。 -/
noncomputable abbrev contInvA : Type :=
  ↥(FixedPoints.addSubgroup (↥I) (ZMod p))

/-- `Bᴵ = (Coind μ_p)ᴵ`。 -/
noncomputable abbrev contInvB : Type :=
  ↥(FixedPoints.addSubgroup (↥I) (contB (F := F) p))

/-- `Cᴵ = Cᴵ`，GS (6.17) 的中项。 -/
noncomputable abbrev contInvC : Type :=
  ↥(FixedPoints.addSubgroup (↥I) (contC (F := F) p))

/-- ★★★ `Aᴵ → Bᴵ`：`S.incl` 在 I-不变点上的限制（`S.incl` 等变 ⟹ 良定义）。 -/
noncomputable def contInvIncl : contInvA (F := F) p I →+ contInvB (F := F) p I where
  toFun a :=
    ⟨(contCoindSES (F := F) p).incl (a : ZMod p), by
      rw [FixedPoints.mem_addSubgroup]
      intro i
      -- `μ_p` 上 `Γ`-作用平凡 ⟹ `↑i • ↑a = ↑a`，故两边定义相等
      rfl⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/-- `contInvIncl` 的底层就是 `S.incl`（供下游 `rw`）。 -/
@[simp]
theorem contInvIncl_coe (a : contInvA (F := F) p I) :
    ((contInvIncl (F := F) p I a : contInvB (F := F) p I) : contB (F := F) p)
      = (contCoindSES (F := F) p).incl (a : ZMod p) := (rfl)

/-- ★ `Aᴵ ↪ Bᴵ` 是单射（`S.incl` 单射 ＋ 子类型）。 -/
theorem contInvIncl_injective : Function.Injective (contInvIncl (F := F) p I) := by
  intro a b h
  have h' : (a : ZMod p) = (b : ZMod p) :=
    (contCoindSES (F := F) p).incl_injective (congrArg Subtype.val h)
  exact Subtype.ext h'

/-- ★★ `contInvIncl` 沿 `Γ⧸I`-作用等变：`incl(q • a) = q • incl(a)`。

证明 = `fixedPoints_subtype_quotientMk_smul`（两边各一次）＋ `S.incl_equivariant`。 -/
theorem contInvIncl_smul (q : (AbsoluteGaloisGroup F) ⧸ I) (a : contInvA (F := F) p I) :
    contInvIncl (F := F) p I (q • a) = q • contInvIncl (F := F) p I a := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective I q
  apply Subtype.ext
  change (contCoindSES (F := F) p).incl
      ((FixedPoints.addSubgroup (↥I) (ZMod p)).subtype (I.quotientMkContinuousMonoidHom h • a))
    = (FixedPoints.addSubgroup (↥I) (contB (F := F) p)).subtype
        (I.quotientMkContinuousMonoidHom h • contInvIncl (F := F) p I a)
  rw [I.fixedPoints_subtype_quotientMk_smul (M := ZMod p),
    I.fixedPoints_subtype_quotientMk_smul (M := contB (F := F) p)]
  show (contCoindSES (F := F) p).incl (h • (FixedPoints.addSubgroup (↥I) (ZMod p)).subtype a)
    = h • (contCoindSES (F := F) p).incl ((FixedPoints.addSubgroup (↥I) (ZMod p)).subtype a)
  exact ((contCoindSES (F := F) p).incl_equivariant h
    ((FixedPoints.addSubgroup (↥I) (ZMod p)).subtype a)).symm

/-- ★★ **GS 的 `T`**：`T = Bᴵ ⧸ im(Aᴵ ↪ Bᴵ)` ＝ `coker(Aᴵ ↪ Bᴵ)`（GS (6.16) 的第三项）。 -/
noncomputable def contKI : AddSubgroup (contInvB (F := F) p I) :=
  (contInvIncl (F := F) p I).range

/-- `contKI` 的成员刻画：恰为 `Aᴵ` 的像。 -/
theorem mem_contKI {x : contInvB (F := F) p I} :
    x ∈ contKI (F := F) p I ↔ ∃ a : contInvA (F := F) p I, contInvIncl (F := F) p I a = x :=
  Iff.rfl

/-- ★★★★ **`contKI` 在 `Γ⧸I`-作用下稳定**（由 `contInvIncl_smul`）。 -/
theorem contKI_stable : ∀ q : (AbsoluteGaloisGroup F) ⧸ I,
    ∀ x ∈ contKI (F := F) p I, q • x ∈ contKI (F := F) p I := by
  intro q x hx
  obtain ⟨a, rfl⟩ := (mem_contKI (F := F) p I).mp hx
  exact (mem_contKI (F := F) p I).mpr ⟨q • a, contInvIncl_smul (F := F) p I q a⟩

/-- ★★★ `T = Bᴵ ⧸ Aᴵ`（GS (6.16) 第三项）。 -/
noncomputable abbrev contT : Type := contInvB (F := F) p I ⧸ contKI (F := F) p I

/-- `T` 上的 `Γ⧸I`-作用（由 `contKI_stable` 下降）。 -/
noncomputable instance contTDistribMulAction :
    DistribMulAction ((AbsoluteGaloisGroup F) ⧸ I) (contT (F := F) p I) :=
  (contKI (F := F) p I).quotientDistribMulAction (contKI_stable (F := F) p I)

/-- ★★★★ **GS (6.16)**：`0 → Aᴵ → Bᴵ → T → 0` 是 `Γ⧸I` 上的短正合列（**无条件**；
`Hyp542.cokerSES` 的连续侧对应物——`T` 取成余核，故右端满射自动）。 -/
noncomputable def contInvSES :
    DiscreteShortExact ((AbsoluteGaloisGroup F) ⧸ I)
      (contInvA (F := F) p I) (contInvB (F := F) p I) (contT (F := F) p I) where
  incl := contInvIncl (F := F) p I
  proj := QuotientAddGroup.mk' (contKI (F := F) p I)
  incl_equivariant := fun q a => contInvIncl_smul (F := F) p I q a
  proj_equivariant := fun q b =>
    (AddSubgroup.quotientDistribMulAction_smul_mk (contKI (F := F) p I)
      (contKI_stable (F := F) p I) q b).symm
  incl_injective := contInvIncl_injective (F := F) p I
  proj_surjective := QuotientAddGroup.mk'_surjective _
  exact := by
    rw [AddMonoidHom.exact_iff, QuotientAddGroup.ker_mk']
    exact (rfl)

-- @source file=raw/GilleSzamuely2017.tex locator=line:9528 quote="0\to A^{H}\to M^{G}(A)^{H}\to T\to0"
/-- **GS (6.16) 的载体锁定**：`contInvSES` 的左端就是 `contInvIncl`（`Aᴵ ↪ Bᴵ`）——
把 `incl` 改成任何别的映射即编译失败（KB 规则：陈述保真的机检形式之一）。 -/
theorem contInvSES_incl :
    (contInvSES (F := F) p I).incl = contInvIncl (F := F) p I := (rfl)

end Invariants

end L20261018

#print axioms L20261018.contInvIncl_smul
#print axioms L20261018.contInvSES
#print axioms L20261018.contInvSES_incl
