import L20261018.Ch4.Step030_unramified_decomposition_algebraic
import TauCeti.NumberTheory.ClassFieldTheory.Brauer.RootsOfUnity

/-!
# R1173（**完备档的 `UnitsCupVanish` —— 无条件机检**）

## 本轮做什么

R1171 把 (R2) 压成单条具名假设 `UnitsCupVanish`（[[hyp-units-cup-vanish]]）：

```
∀ u w : Fˣ, v u = 1 → v w = 1 →
  ((kummerCupPairing ζ hζ).cup 1 1) (kummerClass F hp u) (kummerClass F hp w) = 0
```

它在一般 Hensel 下 `∅-open`（缺不去完备的不分歧范数论）。**本轮机检它在完备档成立**，
且**不再以 `tr` 为假设**：

## 关键：`tr` 可以**造出来**（不再只是输入）

`Hyp124.cup_unit_unit_eq_zero` 把单位×单位杯积零点归约到 `localSymbol` 的值公式，其
`tr : H²(μ_p) ≃+ ZMod p` 原为**输入**。本轮发现库内
**`ClassFieldTheory.h2MuEquivZMod`**（`Brauer/RootsOfUnity.lean:89`，"normalized local invariant"，
引 NSW 6.2.1）**正是这个 `tr`，且只需 `[IsNonarchimedeanLocalField F]` ＋ `IsUnit (p : F)`**：

```lean
h2MuEquivZMod (F) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n} (hn : IsUnit ↑n) : continuousCohomology 2 (muNRep n F) ≃+ ZMod n
```

⟹ `UnitsCupVanish` 在完备档**无条件**成立（条件只剩论文自身的
`¬ ringChar 𝓀[F] ∣ p`，即 `\char K \ne p`）。

## 意义（`L1`／`L10①`）

`wiki/hyp-units-cup-vanish.md` §3.2 的非空见证由「条件性（`tr` 作输入）」升级为
**「完备档无条件机检」** ⟹ `UnitsCupVanish` 的**全部剩余内容 = 去掉完备性这一步**，
不再是「连完备情形都没证」。

## 本轮

| 声明 | 内容 |
|---|---|
| **`kummerClass_isUnit_proof_irrel`** | `IsUnit` 证明无关（`kummerClass` 的两个 `IsUnit` 见证可互换） |
| **`unitsCupVanish_complete`** | ★★★★★ **完备档 `UnitsCupVanish`（无条件，`tr` 已由 `h2MuEquivZMod` 造出）** |
| **`unitsCupVanish_of_residueSpan_eq_bot`** | ★★★★★ **反向**：`residueSpan = ⊥ ⟹ UnitsCupVanish`（⟹ 归约**精确**，既不减弱也不加强） |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField Polynomial

namespace L20261018

variable {F : Type} [Field F] {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- `IsUnit (p : F)` 的两个见证给出**同一个** `kummerClass`（`IsUnit` 是 subsingleton）。 -/
theorem kummerClass_isUnit_proof_irrel (h1 h2 : IsUnit (p : F)) (a : Fˣ) :
    ClassFieldTheory.kummerClass F h1 a = ClassFieldTheory.kummerClass F h2 a := by
  have hp_eq : h1 = h2 := Subsingleton.elim _ _
  rw [hp_eq]

/-- ★★★★★ **完备档的 `UnitsCupVanish` —— 无条件成立**。

条件只有论文自身的 `¬ ringChar 𝓀[F] ∣ p`（即 `\char K \ne p`）；`tr` 不再作输入，
而是由库内 `ClassFieldTheory.h2MuEquivZMod`（`Brauer/RootsOfUnity.lean:89`，
"normalized local invariant"，引 NSW 6.2.1）**造出**。

⟹ `UnitsCupVanish` 的全部剩余内容 = **去掉完备性**这一步。 -/
theorem unitsCupVanish_complete [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : F)) (hres : ¬ ringChar 𝓀[F] ∣ p) :
    ∀ u w : Fˣ, (TauCeti.normalizedValuation F) u = 1 →
      (TauCeti.normalizedValuation F) w = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hp u) (ClassFieldTheory.kummerClass F hp w) = 0 := by
  intro u w hu hw
  have huU : u ∈ unitFiltration F 0 :=
    (mem_unitFiltration_zero u).2 ((normalizedValuation_eq_one_iff u).1 hu)
  have hwU : w ∈ unitFiltration F 0 :=
    (mem_unitFiltration_zero w).2 ((normalizedValuation_eq_one_iff w).1 hw)
  have h := cup_unit_unit_eq_zero (K := F) (n := p) (ζ := ζ) hζ
    (ClassFieldTheory.h2MuEquivZMod F (hζ.neZero'.out.isUnit)) hres huU hwU
  rwa [kummerClass_isUnit_proof_irrel (hζ.neZero'.out.isUnit) hp u,
    kummerClass_isUnit_proof_irrel (hζ.neZero'.out.isUnit) hp w] at h

/-! ## 3. 归约是**精确的**：(R2) ⟺ `UnitsCupVanish` -/

/-- ★★★★★ **反向**：`residueSpan = ⊥` ⟹ `UnitsCupVanish`。

`cup (u) (w)` 是 `residueSpan` 的生成元（`cup_mem_residueSpan`，取 `u`／`w` 作为 `ker v̄` 的元素），
故 `residueSpan = ⊥` 时它必为 `0`。

配合 `Hyp288.residueSpan_eq_bot_of_units`（正向）⟹ **归约既不减弱也不加强**：
`UnitsCupVanish` 与 (R2) 等价。 -/
theorem unitsCupVanish_of_residueSpan_eq_bot {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F))
    (hspan : residueSpan ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hp) = ⊥) :
    ∀ u w : Fˣ, v u = 1 → v w = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hp u) (ClassFieldTheory.kummerClass F hp w) = 0 := by
  intro u w hu hw
  have hu0 : valH1LinearGen (p := p) v hp (ClassFieldTheory.kummerClass F hp u) = 0 := by
    show valH1Gen (p := p) v hp (ClassFieldTheory.kummerClass F hp u) = 0
    rw [valH1Gen_kummerClass]
    have : (v u).toAdd = 0 := by rw [hu]; rfl
    rw [this]
    simp
  have hw0 : valH1LinearGen (p := p) v hp (ClassFieldTheory.kummerClass F hp w) = 0 := by
    show valH1Gen (p := p) v hp (ClassFieldTheory.kummerClass F hp w) = 0
    rw [valH1Gen_kummerClass]
    have : (v w).toAdd = 0 := by rw [hw]; rfl
    rw [this]
    simp
  have hmem := cup_mem_residueSpan ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
    (valH1LinearGen (p := p) v hp)
    (⟨_, by rw [LinearMap.mem_ker]; exact hu0⟩ : ↥(LinearMap.ker (valH1LinearGen (p := p) v hp)))
    (⟨_, by rw [LinearMap.mem_ker]; exact hw0⟩ : ↥(LinearMap.ker (valH1LinearGen (p := p) v hp)))
  rw [hspan, Submodule.mem_bot] at hmem
  exact hmem


end L20261018

#print axioms L20261018.kummerClass_isUnit_proof_irrel
#print axioms L20261018.unitsCupVanish_complete
#print axioms L20261018.unitsCupVanish_of_residueSpan_eq_bot
