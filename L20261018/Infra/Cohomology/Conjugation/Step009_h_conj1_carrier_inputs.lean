import L20261018.Ch2.Hensel.Inertia.Step039_h1_inertia_zmod

/-!
# S72 R7：`H-conj1` 的两个**载体侧**输入（`RECON-tauceti-lcft.md` §5 路线 (c) 的前置）

## 收获：**载体桥不需要**

`RECON` §6 曾判「TauCeti `inertiaSubgroup` 在 `AlgebraicClosure` 载体、本战役 `inertiaLoc` 在
`SeparableClosure` 载体 ⟹ 跨载体引用前须先建桥」。本轮实测**该桥不必建**：

```
TauCeti.mem_maximalUnramifiedExtension_of_pow_eq_one :
  ∀ {K} [..] {Ω} [Field Ω] [Algebra K Ω] {n}, ¬ringChar κ ∣ n → ∀ {ζ : Ω}, ζ ^ n = 1
    → ζ ∈ TauCeti.maximalUnramifiedExtension K Ω        -- ★ 对任意 Ω 泛型
TauCeti.maximalUnramifiedExtension K Ω                   -- ★ 对任意 Ω 泛型
```

而本战役 `inertiaLoc F = (KnrLoc F).fixingSubgroup`，`KnrLoc F =
TauCeti.maximalUnramifiedExtension F (SeparableClosure F)`（`Hyp380:75–79`）
—— **正是上式的 `Ω := SeparableClosure F` 特化**。故 TauCeti 的 `Ω`-泛型件**可直接用**，
不需要 `SeparableClosure F ≃ₐ[F] AlgebraicClosure F`（该等价本身也确不存在于 mathlib：
`#check @SeparableClosure.equivAlgebraicClosure` 报 Unknown）。

## 本件交付（两件，都是 `H-conj1` 所需的「平凡性」输入）

| 声明 | 内容 |
|---|---|
| **`galois_fixes_rootsOfUnity_of_hasEnough`** | ★★★★ **`Γ` 在 `μ_p` 上平凡**：`ζ^p = 1 ⟹ g ζ = ζ`（`HasEnoughRootsOfUnity F p` ⟹ `μ_p ⊆ F`） |
| **`inertiaLoc_fixes_pow_eq_one`** | ★★★ **`I` 在 `μ_m` 上平凡**（`m` 与 `residueChar F` 互素）——`Ω`-泛型件的战役特化 |

**为什么这两件是 `H-conj1` 的关键**（`RECON` §8 缺环 (iv)）：
库内唯一的"共轭 vs 系数"定理是 `TauCeti.inertiaTameCharacter_conj`，
给出的是**带 twist `(1)` 的等变律** `χ_tame(gσg⁻¹) = g • χ_tame(σ)`。
把它特化到 `μ_p` 值域时，需要 **`g • ζ = ζ`（`ζ ∈ μ_p`）** 才能抹平 twist——
那正是 `galois_fixes_rootsOfUnity_of_hasEnough`。
（`inertiaTameCharacter_conj` 自身在 `AlgebraicClosure` 载体；本件先把**不含载体的那一半**做完。）
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-! ## ① `Γ` 在 `μ_p` 上平凡（`μ_p ⊆ F` 的直接后果） -/

/-- ★★★★ **`Γ` 逐点固定 `μ_p`**：`HasEnoughRootsOfUnity F p` ⟹ 每个 `p` 次单位根都在 `F` 里，
故被 `Γ = Gal(SeparableClosure F / F)` 固定。

这是 `H-conj1` 的「twist 抹平」那一步所需的唯一输入（`RECON` §8 缺环 (iv)）。 -/
theorem galois_fixes_rootsOfUnity_of_hasEnough (g : AbsoluteGaloisGroup F)
    {ζ : SeparableClosure F} (hζ : ζ ^ p = 1) : g ζ = ζ := by
  obtain ⟨m, hm⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot F p
  have hmap : IsPrimitiveRoot (algebraMap F (SeparableClosure F) m) p :=
    hm.map_of_injective (algebraMap F (SeparableClosure F)).injective
  obtain ⟨k, -, hk⟩ := hmap.eq_pow_of_pow_eq_one hζ
  rw [← hk, map_pow, AlgEquiv.commutes]

/-! ## ② `I` 在 `μ_m` 上平凡（`Ω`-泛型件的战役特化） -/

variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-- ★★★ **惯性固定 `μ_m`**（`m` 与 `residueChar F` 互素），在**本战役载体**
`SeparableClosure F` 上。

直接由 `TauCeti.mem_maximalUnramifiedExtension_of_pow_eq_one`（**`Ω`-泛型**）＋
`inertiaLoc` 的定义（`= K_nr 的固定子群`）得到——**不需要载体桥**（见文件头）。 -/
theorem inertiaLoc_fixes_pow_eq_one {m : ℕ}
    (hm : m.Coprime (residueChar F))
    {σ : AbsoluteGaloisGroup F} (hσ : σ ∈ inertiaLoc F)
    {ζ : SeparableClosure F} (hζ : ζ ^ m = 1) : σ ζ = ζ := by
  have hnd : ¬ residueChar F ∣ m :=
    (CharP.prime_ringChar (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer)).coprime_iff_not_dvd.1
      hm.symm
  have hmem : ζ ∈ TauCeti.maximalUnramifiedExtension F (SeparableClosure F) :=
    TauCeti.mem_maximalUnramifiedExtension_of_pow_eq_one hnd hζ
  simpa using hσ ⟨ζ, hmem⟩

end L20261018

#print axioms L20261018.galois_fixes_rootsOfUnity_of_hasEnough
#print axioms L20261018.inertiaLoc_fixes_pow_eq_one
