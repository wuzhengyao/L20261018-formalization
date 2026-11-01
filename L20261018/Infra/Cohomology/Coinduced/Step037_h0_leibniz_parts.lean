import L20261018.Ch2.Hensel.ResidueMap.Step073_delta_two_injective_reduction
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.ConnectingMap
import TauCeti.RepresentationTheory.Homological.ContCohomology.ConnectingMapComparison
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Comparison

/-!
# S75 R1：**连续模型的 `H⁰`-Leibniz**（GS 6.8.4 的 `p = 0` 支）—— 部件与显式侧机检

## 这一件在 GS 的哪一句

`raw/GilleSzamuely2017.tex:9569–9596`（`lemma-residue-cup-product`，印版 6.8.4）的证明用四步，其
**第四步**是"cup 与边界（连接映射）的相容性"。本战役需要的特化是 `PROMPT-S75` §1.1 的

```
δ₁ (Inf z₀ ⌣ Inf a) = δ₀ (Inf z₀) ⌣ Inf a          （z₀ ∈ H⁰(Γ⧸I, Cᴵ),  a ∈ H¹(Γ, μ_p)）
```

即**带 `H⁰`-类的 Leibniz**：`z₀` 在 `H⁰` ⟹ `⌣ Inf z₀` 是**沿 `G`-不变元素的系数映射**。

## 侦察读数（本轮最值钱的东西，`L46` 内容式检索）

`D94` 判「连续 `S.delta` ↔ 显式 `explicitDelta1` 的桥**不必建**」。**该判决所依赖的前提已过时**：
库内**已有**那条桥，也有 Leibniz 本体（`raw/TauCeti`，本轮已补编 `.olean`）：

| 需要的件 | 库内名称 | 位置 |
|---|---|---|
| 桥（`δ⁰`） | `DiscreteShortExact.explicitIso_delta0` | `ConnectingMapComparison.lean:79` |
| 桥（`δ¹`） | `DiscreteShortExact.explicitIso_delta1` | `ConnectingMapComparison.lean:126` |
| **`H⁰`-Leibniz（第一变量）** | **`TauCeti.ContCohomology.explicitDelta1_explicitCup01_left`** | `Cup/ConnectingMap.lean:137` |
| cup 显式↔连续（`(0,1)`） | `explicitAddEquiv_cup01` | `Cup/Comparison.lean:261` |
| cup 显式↔连续（`(1,1)`） | `explicitAddEquiv_cup11` | `Cup/Comparison.lean:317` |

## 本件交付

| 声明 | 内容 |
|---|---|
| `contC_nsmul_eq_zero` | ★ `C = CoindQuotient Γ ⊥ μ_p` 的指数整除 `p`（`zmodModule` 的输入） |
| `contC_smul_eq_nsmul_val` | ★ `a • c = a.val • c`（`zmodModule` 的标量由 `nsmul` 决定） |
| `smulPairingC`／`smulPairingB`／`mulPairing` | 三个配对：`C ⊗ A → C`（标量）、`B ⊗ A → B`（标量）、`A ⊗ A → A`（乘法） |
| `smulPairingC_equivariant`／`smulPairingB_equivariant`／`mulPairing_equivariant` | 三者的 `G`-等变性 |
| `incl_smul`／`proj_smul` | `S.incl`／`S.proj` 与标量作用的相容（`hincl`／`hproj` 的原料） |
| **`explicitLeibniz_cup01`** | ★★★★ **显式模型的 `H⁰`-Leibniz**：`S.explicitDelta1 (z₀ ⌣ y) = (S.explicitDelta0 z₀) ⌣ y` |

## 诚实边界

* 本件**不含**连续模型的那条等式（要用 `explicitIso_delta0/1` 把两侧搬过去）——下一件。
* `S = contCoindSES p`（`0 → μ_p → Coind Γ ⊥ μ_p → C → 0`），`A = ZMod p` 上 `Γ` **平凡**作用
  （`rfl` 级，见 `smulPairing*_equivariant` 的证明）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-! ### 1. `C = CoindQuotient Γ ⊥ μ_p` 的指数与标量作用 -/

/-- ★ **`C = Coind Γ ⊥ μ_p ⧸ μ_p` 被 `p` 杀死**：中项 `Coind Γ ⊥ μ_p` 是 `ZMod p`-模，商承之。 -/
theorem contC_nsmul_eq_zero (x : contC (F := F) p) : p • x = 0 := by
  induction x using CoindQuotient.induction_on with
  | _ f =>
    rw [← map_nsmul (CoindQuotient.mk (AbsoluteGaloisGroup F) ⊥ (ZMod p)) p f]
    rw [DiscreteCoind.nsmul_eq_zero (fun a : ZMod p => ?_)]
    exact map_zero _
    rw [nsmul_eq_mul, CharP.cast_eq_zero (ZMod p) p, zero_mul]

/-- ★★ **`C = Coind Γ ⊥ μ_p` 的 `ZMod p`-模结构**（由指数整除 `p` 唯一确定；库内 `CoindQuotient`
无此实例，故显式给出：`AddCommGroup.zmodModule`）。 -/
noncomputable instance contCModule : Module (ZMod p) (contC (F := F) p) :=
  AddCommGroup.zmodModule (contC_nsmul_eq_zero (F := F) p)

/-- ★ **`zmodModule` 给出的标量由 `nsmul` 决定**：`a • c = a.val • c`。

（`AddCommGroup.zmodModule` 的标量按定义就是 `nsmul`，但 `n` 是变量时不展开；
用 `ZMod.natCast_zmod_val` ＋ `Nat.cast_smul_eq_nsmul` 绕开。） -/
theorem contC_smul_eq_nsmul_val (a : ZMod p) (c : contC (F := F) p) :
    a • c = a.val • c := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [Nat.cast_smul_eq_nsmul]

/-- ★ **标量作用与 `Γ`-作用交换**（`zmodModule` 结构只有 `nsmul`，故 `Γ`-作用与它交换）。 -/
theorem contC_smul_comm_G (g : AbsoluteGaloisGroup F) (a : ZMod p) (c : contC (F := F) p) :
    a • (g • c) = g • (a • c) := by
  rw [contC_smul_eq_nsmul_val (p := p) a (g • c), contC_smul_eq_nsmul_val (p := p) a c]
  exact (map_nsmul (DistribSMul.toAddMonoidHom (contC (F := F) p) g) a.val c).symm

/-- ★ 配对 `C × μ_p → C`：**标量作用**（`μ_p`-模 `C` 上的作用）。 -/
noncomputable def smulPairingC :
    contC (F := F) p →+ (ZMod p →+ contC (F := F) p) where
  toFun c :=
    { toFun := fun a => a • c
      map_zero' := zero_smul (ZMod p) c
      map_add' := fun a b => add_smul a b c }
  map_zero' := by
    refine AddMonoidHom.ext fun a => ?_
    exact smul_zero a
  map_add' := fun c c' => by
    refine AddMonoidHom.ext fun a => ?_
    exact smul_add a c c'

/-- 配对 `C × μ_p → C` 的取值：`smulPairingC c a = a • c`。 -/
theorem smulPairingC_apply (c : contC (F := F) p) (a : ZMod p) :
    smulPairingC (F := F) p c a = a • c := (rfl)

/-- ★ 配对 `B × μ_p → B`：`B = Coind Γ ⊥ μ_p` 上的标量作用（库内 `instModuleScalar`）。 -/
noncomputable def smulPairingB :
    contB (F := F) p →+ (ZMod p →+ contB (F := F) p) where
  toFun f :=
    { toFun := fun a => a • f
      map_zero' := zero_smul (ZMod p) f
      map_add' := fun a b => add_smul a b f }
  map_zero' := by
    refine AddMonoidHom.ext fun a => ?_
    exact smul_zero a
  map_add' := fun f f' => by
    refine AddMonoidHom.ext fun a => ?_
    exact smul_add a f f'

/-- ★ 配对 `μ_p × μ_p → μ_p`：乘法。 -/
noncomputable def mulPairing : ZMod p →+ (ZMod p →+ ZMod p) := AddMonoidHom.mul

/-! ### 2. 三个配对的 `G`-等变性 -/

/-- ★ `C` 侧：`a • (g • c) = g • (a • c)`。 -/
theorem smulPairingC_equivariant (g : AbsoluteGaloisGroup F) (c : contC (F := F) p)
    (a : ZMod p) : smulPairingC (F := F) p (g • c) (g • a) = g • smulPairingC (F := F) p c a := by
  show (g • a) • (g • c) = g • (a • c)
  rw [show g • a = a from rfl]
  exact contC_smul_comm_G (F := F) p g a c

/-- ★ `B` 侧：`instSMulCommClass`. -/
theorem smulPairingB_equivariant (g : AbsoluteGaloisGroup F) (f : contB (F := F) p)
    (a : ZMod p) : smulPairingB (F := F) p (g • f) (g • a) = g • smulPairingB (F := F) p f a := by
  show (g • a) • (g • f) = g • (a • f)
  rw [show g • a = a from rfl]
  exact (SMulCommClass.smul_comm g a f).symm

/-- ★ `μ_p` 侧：作用平凡 ⟹ 乘法等变。 -/
theorem mulPairing_equivariant (g : AbsoluteGaloisGroup F) (a b : ZMod p) :
    mulPairing (p := p) (g • a) (g • b) = g • mulPairing (p := p) a b := by
  rfl

/-! ### 3. `S.incl`／`S.proj` 与标量作用的相容（`hincl`／`hproj` 的原料） -/

/-- ★ `incl` 与标量相容：`a • incl x = incl (a * x)`（`unit` 的点值线性性）。 -/
theorem coindSES_incl_smul (a x : ZMod p) :
    a • (contCoindSES (F := F) p).incl x
      = (contCoindSES (F := F) p).incl (a * x) := by
  show a • DiscreteCoind.unit (AbsoluteGaloisGroup F) ⊥ (ZMod p) x
      = DiscreteCoind.unit (AbsoluteGaloisGroup F) ⊥ (ZMod p) (a * x)
  refine DiscreteCoind.ext fun g => ?_
  rw [DiscreteCoind.coe_smul_scalar, DiscreteCoind.unit_apply, DiscreteCoind.unit_apply]
  show a • (g • x) = g • (a * x)
  rw [show g • x = x from rfl, show g • (a * x) = a * x from rfl, smul_eq_mul]

/-- ★ `proj` 与标量相容：`a • proj f = proj (a • f)`。 -/
theorem coindSES_proj_smul (a : ZMod p) (f : contB (F := F) p) :
    a • ((contCoindSES (F := F) p).proj f) = (contCoindSES (F := F) p).proj (a • f) := by
  have hB : a • f = a.val • f := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    rw [Nat.cast_smul_eq_nsmul]
  show a • CoindQuotient.mk (AbsoluteGaloisGroup F) ⊥ (ZMod p) f
      = CoindQuotient.mk (AbsoluteGaloisGroup F) ⊥ (ZMod p) (a • f)
  rw [contC_smul_eq_nsmul_val (p := p) a (CoindQuotient.mk (AbsoluteGaloisGroup F) ⊥ (ZMod p) f),
    hB, ← map_nsmul (CoindQuotient.mk (AbsoluteGaloisGroup F) ⊥ (ZMod p)) a.val f]

/-! ### 4. **显式模型的 `H⁰`-Leibniz**（本件的靶子） -/

/-- ★★★★ **`H⁰`-Leibniz（显式模型，本战役特化）**：

```
δ¹ (z₀ ⌣ y) = δ⁰ (z₀) ⌣ y          z₀ ∈ H⁰(Γ, C),  y ∈ H¹(Γ, μ_p)
```

`S = contCoindSES p`（`0 → μ_p → Coind Γ ⊥ μ_p → C → 0`），三个配对取
`μ = B × μ_p → B`（标量）、`μ' = μ_p × μ_p → μ_p`（乘法）、`μ'' = C × μ_p → C`（标量）。
这是 GS `lemma-residue-cup-product`（印版 6.8.4）在 `p = 0` 处的支，库内本体 =
`TauCeti.ContCohomology.explicitDelta1_explicitCup01_left`。 -/
theorem explicitLeibniz_cup01
    (z₀ : ↥(H0 (AbsoluteGaloisGroup F) (contC (F := F) p)))
    (y : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    (contCoindSES (F := F) p).explicitDelta1
        (explicitCup01 (AbsoluteGaloisGroup F) (contC (F := F) p) (ZMod p) (contC (F := F) p)
          (smulPairingC (F := F) p) continuous_of_discreteTopology
          (smulPairingC_equivariant (F := F) p) z₀ y)
      = explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p) (mulPairing (p := p))
          continuous_of_discreteTopology (mulPairing_equivariant (F := F) p)
          ((contCoindSES (F := F) p).explicitDelta0 z₀) y :=
  explicitDelta1_explicitCup01_left
    (SA := contCoindSES (F := F) p) (SC := contCoindSES (F := F) p)
    (μ := smulPairingB (F := F) p) (μ' := mulPairing (p := p)) (μ'' := smulPairingC (F := F) p)
    continuous_of_discreteTopology continuous_of_discreteTopology continuous_of_discreteTopology
    (smulPairingB_equivariant (F := F) p) (mulPairing_equivariant (F := F) p)
    (smulPairingC_equivariant (F := F) p)
    (fun a b => by
      show smulPairingB (F := F) p ((contCoindSES (F := F) p).incl a) b
        = (contCoindSES (F := F) p).incl (mulPairing (p := p) a b)
      show b • (contCoindSES (F := F) p).incl a = (contCoindSES (F := F) p).incl (a * b)
      rw [mul_comm]
      exact coindSES_incl_smul (F := F) p b a)
    (fun a b => by
      show smulPairingC (F := F) p ((contCoindSES (F := F) p).proj a) b
        = (contCoindSES (F := F) p).proj (smulPairingB (F := F) p a b)
      show b • (contCoindSES (F := F) p).proj a = (contCoindSES (F := F) p).proj (b • a)
      exact coindSES_proj_smul (F := F) p b a)
    z₀ y


end L20261018

#print axioms L20261018.contC_nsmul_eq_zero
#print axioms L20261018.contC_smul_eq_nsmul_val
#print axioms L20261018.contC_smul_comm_G
#print axioms L20261018.smulPairingC
#print axioms L20261018.smulPairingB
#print axioms L20261018.mulPairing
#print axioms L20261018.smulPairingC_equivariant
#print axioms L20261018.smulPairingB_equivariant
#print axioms L20261018.mulPairing_equivariant
#print axioms L20261018.coindSES_incl_smul
#print axioms L20261018.coindSES_proj_smul
#print axioms L20261018.explicitLeibniz_cup01
