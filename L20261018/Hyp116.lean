import L20261018.Hyp115

/-!
# R946：`prop:prelim-kummer-valuation`(2) 的**分解式** `x = x₀ + m·(π)`（分解 ＋ 唯一性）

论文 `raw/L20261018.tex:1005`（`label:prop:prelim-kummer-valuation`）(2) 末句：

> 特别地，每个一次上同调类唯一写成 $x=\mathrm{inf}(x_0)+m(\pi)$，
> $x_0\in H^1(K,\mu_p)$，$m\in\Fp$。

## 分层（本轮的教训：把线性代数与 `ZMod` 噪声**分开**）

* **抽象层**（`exists_decomp_linear`／`val_eq_of_decomp_linear`／`unique_decomp_linear`）：
  纯线性代数 —— 对任意域 `k` 与 `k`-模 `V`、任意 `val : V →ₗ[k] k`、`hπ : val π = 1`，
  分解 `x = x₀ + m·π` 无条件成立（`x₀ := x - val x • π`）且唯一。
* **论文层**（`exists_unique_decomp` 等）：把抽象层**实例化**到 `valLin`（`Hyp115`）与
  素元类 `(π) = kummerClass π`，用 `Hyp115.valLin_pi` 供给 `hπ`。

## 记法层（L49 家族第 15–18 次，本轮全部定位）

1. **`smul_one` 不是 `a • 1 = a`** —— 它是 `MulDistribMulAction` 的 `r • 1 = 1`（把 `1` 送到 `1`），
   用了会报 pattern 找不到。正解是 **`smul_eq_mul` ＋ `mul_one`**（或直接 `simp`）。
2. **`m • (1 : k)` 不能手工 `rw` 掉**：`simp` 知道，`rw` 链容易被抢 ⟹ **优先 `simp`**。
3. 收尾 `abel_nf` 不闭合 `x₀' = (x₀' + c) - c` ⟹ 用 **`add_sub_cancel_right`**。
4. `LinearMap.map_smul` 之后的 `• 1` 是 **`k` 在自身上**的作用（不是 `V` 上的），
   故必须按上一条处理 —— 这是本文件此前 4 次失败的**唯一**根因。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

/-! ## 1. 抽象层：赋值分解是纯线性代数 -/

section Abstract

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- **抽象分解**：`val π = 1` ⟹ 任意 `x` 写成 `x = x₀ + m·π` 且 `val x₀ = 0`、`m = val x`。 -/
theorem exists_decomp_linear (val : V →ₗ[k] k) (π : V) (hπ : val π = 1) (x : V) :
    ∃ (x₀ : V) (m : k), val x₀ = 0 ∧ x = x₀ + m • π := by
  refine ⟨x - val x • π, val x, ?_, ?_⟩
  · simp [map_sub, hπ]
  · abel

/-- 分解里的 `m` **就是** `val x`（论文「`\bar v(x) = m`」的用法）。 -/
theorem val_eq_of_decomp_linear (val : V →ₗ[k] k) (π : V) (hπ : val π = 1)
    {x x₀ : V} {m : k} (hx₀ : val x₀ = 0) (hx : x = x₀ + m • π) : val x = m := by
  rw [hx, map_add, LinearMap.map_smul, hπ, hx₀]
  simp

/-- **抽象唯一性**：满足 `val x₀ = 0` 且 `x = x₀ + m·π` 的 `(x₀, m)` 唯一。 -/
theorem unique_decomp_linear (val : V →ₗ[k] k) (π : V) (hπ : val π = 1) (x : V) :
    ∃ (x₀ : V) (m : k), val x₀ = 0 ∧ x = x₀ + m • π ∧
      ∀ (x₀' : V) (m' : k), val x₀' = 0 → x = x₀' + m' • π → x₀' = x₀ ∧ m' = m := by
  refine ⟨x - val x • π, val x, ?_, ?_, ?_⟩
  · simp [map_sub, hπ]
  · abel
  · intro x₀' m' _ hx'
    have hm' : val x = m' := val_eq_of_decomp_linear val π hπ ‹val x₀' = 0› hx'
    refine ⟨?_, hm'.symm⟩
    rw [hm', hx', add_sub_cancel_right]

end Abstract

/-! ## 2. 论文层：实例化到 `\bar v`（`Hyp115`）与素元类 -/

section Paper

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **论文 `prop:prelim-kummer-valuation`(2) 的分解式**（存在形式 ＝ 论文证明使用的形状）：
`v(π)=1` 时每个 `x` 写成 `x = x₀ + m·(π)`，`\bar v(x₀) = 0`。

**唯一性**（论文「唯一写成」）本轮未落成 —— 余一处纯记法目标，已登记为下一轮单入口。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-kummer-valuation quote="特别地，每个一次上同调类唯一写成 $x=\mathrm{inf}(x_0)+m(\pi),x_0\in H^1(K,\mu_p),m\in\Fp$。"
theorem exists_decomp (hp : IsUnit (p : F)) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ)) (x : GaloBase.V F p) :
    ∃ (x₀ : GaloBase.V F p) (m : ZMod p),
      (valLin F p hp) x₀ = 0 ∧ x = x₀ + m • (KummerBridge.kummerClass F p hp π) :=
  exists_decomp_linear (valLin F p hp) (KummerBridge.kummerClass F p hp π)
    (valLin_pi (F := F) (p := p) hp hπ) x


/-- **论文 `prop:prelim-kummer-valuation`(2) 的唯一性**：分解 `x = x₀ + m·(π)`（`\bar v(x₀)=0`）
里的 `(x₀, m)` 唯一。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-kummer-valuation quote="特别地，每个一次上同调类唯一写成 $x=\mathrm{inf}(x_0)+m(\pi),x_0\in H^1(K,\mu_p),m\in\Fp$。"
theorem exists_unique_decomp (hp : IsUnit (p : F)) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ)) (x : GaloBase.V F p) :
    ∃ (x₀ : GaloBase.V F p) (m : ZMod p),
      (valLin F p hp) x₀ = 0 ∧ x = x₀ + m • (KummerBridge.kummerClass F p hp π) ∧
        ∀ (x₀' : GaloBase.V F p) (m' : ZMod p),
          (valLin F p hp) x₀' = 0 →
            x = x₀' + m' • (KummerBridge.kummerClass F p hp π) → x₀' = x₀ ∧ m' = m :=
  unique_decomp_linear (valLin F p hp) (KummerBridge.kummerClass F p hp π)
    (valLin_pi (F := F) (p := p) hp hπ) x

/-- **`m` 可读出**：分解 `x = x₀ + m·(π)` 里的 `m` **就是** `\bar v(x)`。 -/
theorem val_eq_of_decomp (hp : IsUnit (p : F)) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ))
    {x x₀ : GaloBase.V F p} {m : ZMod p}
    (hx₀ : (valLin F p hp) x₀ = 0)
    (hx : x = x₀ + m • (KummerBridge.kummerClass F p hp π)) :
    (valLin F p hp) x = m :=
  val_eq_of_decomp_linear (valLin F p hp) (KummerBridge.kummerClass F p hp π)
    (valLin_pi (F := F) (p := p) hp hπ) hx₀ hx

end Paper

end L20261018

#print axioms L20261018.exists_decomp_linear
#print axioms L20261018.unique_decomp_linear
#print axioms L20261018.exists_unique_decomp
#print axioms L20261018.exists_decomp
#print axioms L20261018.val_eq_of_decomp
