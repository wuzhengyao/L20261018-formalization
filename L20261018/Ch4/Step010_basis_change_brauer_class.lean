import L20261018.Ch4.Step009_dk_eq_one_is_a_theorem
import L20261018.Ch4.Step001_basis_change_first_slot
import L20261018.Ch2.Brauer.Step028_h2_to_brauer_carrier

/-!
# R995：**`lem:basis-change` 的第二句** —— 变换不改变 `D` 的 Brauer 类

论文 `raw/L20261018.tex:1569–1599`（`\label{lem:basis-change}`）的结论**有两句**：

1. （恒等式）`α₁∪β₁+α₂∪β₂ = α'₁∪β'₁+α'₂∪β'₂` —— `Hyp108.basis_change_kummer` **已机检**；
2. （推论）「**因此**，对第一槽平面 `U` 的基作变换，并对第二槽作相应对偶变换，
   **不改变 `D` 的 Brauer 类**」—— 本文件补上。

论文的 `D = (a₁,b₁)_F ⊗_F (a₂,b₂)_F` 在本战役的**载体链**里由
`H2Bridge.brOfH2 (Σ_i (aᵢ)∪(bᵢ))` 承担（`Hyp81`：`D ↦ Σ(aᵢ)∪(bᵢ)` 的上同调模型，
`brOfH2` 的 `Br F` 值；`D` 的指数由 `H2Bridge.indOfH2` 在其上读出）。
⟹ 第二句 = 第一句的 `brOfH2`-像，**一行**（`rw [basis_change_kummer …]`）。

## 载体身份（置此备查）

`D` 的**张量积对象本身**（两个符号代数之张量）**没有**在 Lean 里作为代数对象建模；
`D` 的一切（Brauer 类、指数 `p²`）都经上述载体链表达。故本定理的"Brauer 类不变"
= `brOfH2 (Σ…)` 不变，**不是**"某个 `Algebra` 结构同构"。（与 `STATUS.md` 的载体身份口径一致。）
-/

set_option maxHeartbeats 2000000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

/-- **`lem:basis-change` 第二句（论文 `:1598`）**：第一槽作 `A`、第二槽作 `(A⁻¹)ᵀ`
（`A ∈ GL₂(F_p)`）不改变 `D` 的 **Brauer 类**（`brOfH2` 口径）。

由 `Hyp108.basis_change_kummer` 的恒等式直接取 `brOfH2` 像。 -/
-- @source file=raw/L20261018.tex locator=label:lem:basis-change quote="因此，对第一槽平面 $U$ 的基作变换，并对第二槽作相应对偶变换，不改变 $D$ 的 Brauer 类。"
theorem basis_change_brauer {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
    [HasEnoughRootsOfUnity F p] {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp : IsUnit (p : F))
    (a b : Fin 2 → Fˣ) (A : Matrix (Fin 2) (Fin 2) (ZMod p)) (hA : IsUnit A.det) :
    H2Bridge.brOfH2 (p := p) (K := F) hζ
        (∑ i, GaloBase.cup (K := F) (p := p)
          (∑ j, A i j • KummerBridge.kummerClass F p hp (a j))
          (∑ l, A⁻¹ l i • KummerBridge.kummerClass F p hp (b l)))
      = H2Bridge.brOfH2 (p := p) (K := F) hζ
          (∑ j, GaloBase.cup (K := F) (p := p)
            (KummerBridge.kummerClass F p hp (a j)) (KummerBridge.kummerClass F p hp (b j))) := by
  rw [basis_change_kummer (F := F) (p := p) hp a b A hA]

end L20261018
#print axioms L20261018.basis_change_brauer
