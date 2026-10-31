import Hyp110
import Hyp86

/-!
# 第 4 章 T4：`thm:ramified`（4.3）—— 纯装配

论文 `raw/L20261018.tex:1629`（`\label{thm:ramified}`），`(1)`／`(2)` 的证明各两行：

> **(1)** 引理~\ref{lem:ramified-vanishing} 给出 $U^\perp=0$，再由引理~\ref{lem:basic-inclusions}(2)
> 的 $N\subseteq U^\perp$ 得到 $N=0$。
> **(2)** 将 $\ind(D)=p^2$ 代入定理~\ref{thm:rank-barrier}(2)，得到 $\rank(\Phi)\ge3$。

**⟹ 零新数学**：
* **(1)** = `Hyp110.ramified_vanishing_explicit`（T3）＋ `Hyp101.Nsub_le_Uperp`（$N\subseteq U^\perp$）；
* **(2)** = `Hyp86.theorem_3_2_2_kummer'`（$3.2(2)$）**逐字直接调用** —— 论文自己就是这么写的。

## 载体身份说明（L12／L32，第 3 章已登记的偏离）

论文里 $U^\perp$ 与 $N$ 都在**同一个** $V=H^1(F,\mu_p)$ 里。第 3 章的 Lean 形式化有两个载体
（`GaloBase.V` 与显式 `H1 (AbsoluteGaloisGroup F) (ZMod p)`，见 `Hyp110` 文件头），
因此：

* **(1)**（`U^⊥ = N = 0`）落在**显式载体**上（`Nsub` 与 `Hyp101` 在那里）；
* **(2)**（`rank Φ ≥ 3`）落在 **`GaloBase` 载体**上（`Hyp86` 在那里）。

故本文件给出**两条**定理 `thm_ramified_1`／`thm_ramified_2`，合起来即论文的 `thm:ramified`。
这是**载体偏离**（不是数学偏离），登记于 `STATUS.md`。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000

namespace L20261018

/-! ## (1) `U^⊥ = N = 0`（显式载体） -/

section Part1

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **`thm:ramified`(1)：`U^⊥ = N = 0`**。

论文假设：`p` 奇素、`F` 特征 `0` 含 `μ_p`、`(F,v)` 为 Hensel 离散赋值域、`D` 指数 `p²`
（经 `ind`）、`(a₁)∪(a₂) ≠ 0`、`v|_U ≠ 0`。结论：共同正交空间与范数像**同时消失**。

`E = F(a₁^{1/p},a₂^{1/p})` 以 Kummer 子群 `Δ` 编码（`Theo352.Efield Δ`）；
`N = cor_{E/F}H¹(E,μ_p)` 即 `Theo352.Nsub Δ`；`U^⊥ = Theo352.Bex … .Uperp`。 -/
-- @source file=raw/L20261018.tex locator=label:thm:ramified quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$"
theorem thm_ramified_1 (hp : IsUnit (p : F)) (hp2 : p ≠ 2) (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (hU : IsOpen ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
      : Set (AbsoluteGaloisGroup F)))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p) Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p) Δ)]
    {a1 a2 : Fˣ} (ha1 : a1 ∈ Δ) (ha2 : a2 ∈ Δ)
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0)
    (VK : Type) [AddCommGroup VK] [Module (ZMod p) VK]
    (D : HenselResidueData (ZMod p)
      (H1 (AbsoluteGaloisGroup F) (ZMod p)) (H2 (AbsoluteGaloisGroup F) (ZMod p)) VK
      (Theo352.cupLin (F := F) (p := p)))
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2), D.val u ≠ 0) :
    (Theo352.Bex (F := F) (p := p) hp hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ := by
  have hU0 : (Theo352.Bex (F := F) (p := p) hp hne).Uperp = ⊥ :=
    ramified_vanishing_explicit (F := F) (p := p) hp hp2 VK D a1 a2 hne hval
  refine ⟨hU0, ?_⟩
  have hle := Assemble36.Nsub_le_Uperp (F := F) (p := p) hp hp2 Δ hroots hU ha1 ha2 hne
  rw [hU0] at hle
  exact eq_bot_iff.mpr hle

end Part1

/-! ## (2) `rank(Φ) ≥ 3`（`GaloBase` 载体，直接引用 3.2(2)） -/

section Part2

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]
  {a1 a2 : Fˣ}

/-- **`thm:ramified`(2)：`rank(Φ) ≥ 3`** —— 论文 `:1640` 明写「将 `ind(D)=p²` 代入
定理 `thm:rank-barrier`(2)」，故本定理**就是** `Hyp86.theorem_3_2_2_kummer'`，零新数学。 -/
-- @source file=raw/L20261018.tex locator=label:thm:ramified quote="将 $\ind(D)=p^2$ 代入定理~\ref{thm:rank-barrier}\textnormal{(2)}，得到 $\rank(\Phi)\ge3$。"
theorem thm_ramified_2 (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {a1 a2 : Fˣ}
    (hne : paperCup F p hp a1 a2 ≠ 0)
    (b1 b2 : GaloBase.V F p)
    (hD : H2Bridge.indOfH2 (p := p) (K := F) (KummerBridge.primitiveRoot_spec F p)
      (GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a1) b1
        + GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a2) b2) = p ^ 2) :
    (3 : Cardinal) ≤ Module.rank (ZMod p)
      ↥(biKummerDataKummer F p hp a1 a2 hne).Phi.range :=
  theorem_3_2_2_kummer' (F := F) (p := p) hp hp2 a1 a2 hne b1 b2 hD

end Part2

end L20261018

#print axioms L20261018.thm_ramified_1
#print axioms L20261018.thm_ramified_2
