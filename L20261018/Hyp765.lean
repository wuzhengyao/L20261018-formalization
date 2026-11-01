import L20261018.Hyp762
-- 只为让 `routes_check.py` 的「最新模块」能解析 R4（`Hyp763`／`Hyp764`）的 evidence；
-- 本件数学上不依赖它们。
import L20261018.Hyp764

/-!
# S72 R5：`F5` 的第一步 —— **`H¹(I,ℤ/p) ≅ ℤ/p` 作为 `ℤ/p`-模**

## 位置

`prop:prelim-residue` 无条件化的链条（`Hyp764` 文件头）：

```
H-conj1（Hyp762，具名假设）
  ⟹ H¹(I,ℤ/p) 的 Γ⧸I-作用平凡
  ⟹ H¹(I,ℤ/p) ≅ ℤ/p  作为 Γ⧸I-模            ★本件（模同构的部分）
  ⟹ explicitCoeff1Equiv ⟹ F5 第一半
  ⟹ F5 = infl1EquivVKG ∘ (第一半) ⟹ hd_cup_pi ⟹ prop:prelim-residue(1)
```

## 本件的数学（零新数学）

`A := H1 ↥I (ZMod p)` 是 `ZMod p`-模，`Nat.card A = p`（`Hyp759`），`p` 素。
取 `x ≠ 0`，则 `zmultiples x = ⊤`（`Hyp761.zmultiples_eq_top_of_natCard_prime`）。于是

* **满**：`y = n • x`（`mem_zmultiples_iff`），且 `n • x = (n : ZMod p) • x`（`zsmul_eq_smul_cast`）；
* **单**：`c • x = 0` 且 `c ≠ 0` ⟹ `c` 是域 `ZMod p` 的单位 ⟹ `x = c⁻¹ • (c • x) = 0` 矛盾。

⟹ `ZMod p ≃ₗ[ZMod p] A`，`c ↦ c • x`。

## 交付

| 声明 | 内容 |
|---|---|
| **`zmodLinearEquivOfCardPrime`** | ★★★★ 一般形：`ZMod p`-模 ＋ `Nat.card = p`（`p` 素）＋ 非零元 ⟹ `ZMod p ≃ₗ A` |
| **`h1InertiaLinearEquiv`** | ★★★★ 战役载体：`ZMod p ≃ₗ[ZMod p] H1 ↥I (ZMod p)`（由 `Hyp759` 的 `Nat.card = p`） |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

/-! ## ① 一般形：素数阶 `ZMod p`-模 ≅ `ZMod p` -/

/-- ★★★★ **素数阶 `ZMod p`-模 ≅ `ZMod p`**（`c ↦ c • x`，`x ≠ 0`）。

满射用 `zmultiples x = ⊤`（`Hyp761`）＋ `zsmul_eq_smul_cast`；单射用 `ZMod p` 是域。 -/
noncomputable def zmodLinearEquivOfCardPrime (p : ℕ) [hp : Fact p.Prime]
    {A : Type*} [AddCommGroup A] [Module (ZMod p) A]
    (hcard : Nat.card A = p) (x : A) (hx : x ≠ 0) :
    ZMod p ≃ₗ[ZMod p] A := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have htop : AddSubgroup.zmultiples x = ⊤ :=
    zmultiples_eq_top_of_natCard_prime p x hx hcard
  let f : ZMod p →ₗ[ZMod p] A :=
    { toFun := fun c => c • x
      map_add' := fun a b => add_smul a b x
      map_smul' := fun a b => mul_smul a b x }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · -- 单射
    intro a b hab
    change a • x = b • x at hab
    by_contra hne
    have h0 : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hzero : (a - b) • x = 0 := by
      rw [sub_smul, hab, sub_self]
    -- 用域性：`(a-b)⁻¹ • ((a-b) • x) = x`
    have : x = 0 := by
      have h1 : (a - b)⁻¹ • ((a - b) • x) = x := by
        rw [← mul_smul, inv_mul_cancel₀ h0, one_smul]
      rw [hzero, smul_zero] at h1
      exact h1.symm
    exact hx this
  · -- 满射
    intro y
    have hy : y ∈ AddSubgroup.zmultiples x := by rw [htop]; exact AddSubgroup.mem_top y
    rw [AddSubgroup.mem_zmultiples_iff] at hy
    obtain ⟨n, rfl⟩ := hy
    refine ⟨(n : ZMod p), ?_⟩
    show (n : ZMod p) • x = n • x
    exact Int.cast_smul_eq_zsmul (ZMod p) n x

/-! ## ② 战役载体：`H1 ↥I (ZMod p) ≅ ZMod p` -/

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-- ★★★★ **`ZMod p ≃ₗ[ZMod p] H¹(I,ℤ/p)`**（`c ↦ c • x`，`x ≠ 0`）。

由 `Hyp759.natCard_h1Inertia_eq`（`Nat.card = p`）＋ `zmodLinearEquivOfCardPrime`。
这是 `F5` 第一半的**模同构**部分（还差「与 `Γ⧸I`-作用交换」，那一步要用 `H-conj1`）。 -/
noncomputable def h1InertiaLinearEquiv (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hx : x ≠ 0) :
    ZMod p ≃ₗ[ZMod p] H1 ↥(inertiaLoc F) (ZMod p) :=
  zmodLinearEquivOfCardPrime p
    (natCard_h1Inertia_eq (F := F) (p := p) (q := q) hpq ζ hζ hgen) x hx

end L20261018
