import L20261018.Hyp214

/-!
# R1083（**T1 归约：系数同构的复合恒等**）

T1 第一归约的因子分解 `explicitMap1 φ kce = (explicitMap1 φ e'') ∘ explicitCoeff1(e_c)` 需要
**系数同构层的复合恒等** `e'' ∘ e_c = kce`。本文件给出该恒等的 `AddMonoidHom` 形式（机检）。

| 声明 | 内容 |
|---|---|
| **`eDouble_comp_eq_kce`** | `e''.comp e_c = kce`（`AddMonoidHom` 层） |

**下一轮（`Hyp216`）的四个具体卡点**（本轮已定位）：
1. `explicitCoeff1` 要的是 **`→+[G]`**（`DistribMulActionHom`），不是 `→+` ⟹ 须先用
   `kummerCoeffLinearEquiv` 的 `map_smul'` 造出 `DistribMulActionHom`（两侧作用都平凡，故 `map_smul'` 空洞）；
2. `explicitMap1_comp` 的 `φ.comp ψ` 中 `id.comp ψ` 须 `rw [ContinuousMonoidHom.comp_id]`，
   但等变性证明里的 `(ContinuousMonoidHom.id G) g • m` 需 `show`/`simp` 化到 `g • m`；
3. `N := ZMod p` 作为 `AbsoluteGaloisGroup F`-模的实例须与 `muNRep` 侧 `Field.absoluteGaloisGroup F`-模区分，
   后者需 `attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass`；
4. `rw [muNRep_smul_trivial …]` 报「pattern is a metavariable」（`x = ρ g x` 的 `x` 未定）⟹ 须 `exact` 而非 `rw`。
-/

set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

section Comp

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **系数同构层的复合恒等**：`e'' ∘ e_c = kce`（`AddMonoidHom` 形式）。 -/
theorem eDouble_comp_eq_kce (hp : IsUnit (p : F)) :
    (eDouble (F := F) p hp).comp (KummerBridge.kummerCoeffLinearEquiv F p hp).toAddMonoidHom
      = (ClassFieldTheory.kummerCoeffEquivMuNRep (n := p) (F := F)).toAddMonoidHom := by
  ext x
  exact (kce_eq_eDouble_comp (F := F) (p := p) hp x).symm

end Comp

end L20261018

#print axioms L20261018.eDouble_comp_eq_kce
