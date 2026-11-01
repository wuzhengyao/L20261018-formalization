import L20261018.Ch2.Hensel.Inertia.Step023_b1_hom_inertia_mu_p
import L20261018.Ch2.Hensel.Inertia.Step022_cd_p_inertia_unconditional

/-!
# S43 R24（**B1 的第二步**）：`Hom(I, μ_p) ≅ Hom(I_t, μ_p)` —— GMS (7.3) 的第一等号

## 源的逐字（`raw/gms.tex:400`–`402`）

> The above description of \(I\) and \(I_{t}\) gives canonical isomorphisms:
> \[
> \operatorname{Hom}(I,\mu_{n}) = \operatorname{Hom}(I_{t},\mu_{n}) = \mathbf{Z}/n\mathbf{Z}. \tag{7.3}
> \]

**本件机检第一个等号**（第二个 —— `Hom(I_t, μ_n) = ℤ/nℤ` —— 未做）。

## 数学

`P_K = I_wild` 是 pro-`q`（`q = char κ`），`μ_p` 是 `p`-群（`p ≠ q`）⟹ **任何连续同态
`P_K → μ_p` 平凡**（`Hyp518` 已机检）。于是任何连续 `p`-特征 `f` **杀掉 `P_K`**，
故经 `I ↠ I/P_K = I_t`（`Hyp515` 的 `toTameInertia`）分解：

```
Hom_cont(I_t, μ_p) ⟶ Hom_cont(I, μ_p),  χ ↦ χ ∘ π     -- 单射（π 满射）
                     满射（每个 f 都杀 P_K ⟹ 可分解）
```

分解出的 `χ` 的**连续性**：`χ ⁻¹' {b} = π '' (f ⁻¹' {b})`，而其补是 `π '' (f ⁻¹' {b})ᶜ` ——
闭集（`f ⁻¹' {b}` 在离散靶下是**闭**的）沿**闭映射** `π`（紧 → T2）的像。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`wildInertia_le_ker_zmodDual`** | `P_K ≤ ker f`（连续 `p`-特征杀野惯性） |
| **`restrictTameInertia`**／`_injective`／`_surjective`／**`_bijective`** | ★★★★★ **GMS (7.3) 第一等号** |
| **`equivTameInertia`** | 由双射得到的 `Equiv`（`Finite`／`Nat.card` 搬运） |
| **`finite_zmodDual_inertia_iff`**／**`..._inertiaLoc_iff`** | `Finite (H¹(I,μ_p)) ↔ Finite (H¹(I_t,μ_p))`（战役载体亦通） |

## 诚实边界

* **第二个等号 `Hom(I_t, μ_n) = ℤ/nℤ` 未做** —— B1 的最后一格。见 `S43-STATUS.md` §5。
* B1 **未闭合**：本件只把问题从 `I` 降到 `I_t`。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti
open scoped TauCeti.zHat

namespace L20261018

/-- ★★★★ **连续 `p`-特征都杀野惯性**：`P_K ≤ ker f`。

机制：把 `f` 限制到 `P_K` 得 `↥P_K →ₜ* Multiplicative (ZMod p)`，由 `Hyp518` 它是 `1`。 -/
theorem wildInertia_le_ker_zmodDual {K : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) q] (hpq : p ≠ q)
    (f : ↥(inertiaSubgroup K) →ₜ* Multiplicative (ZMod p)) :
    (wildInertiaSubgroup K).subgroupOf (inertiaSubgroup K) ≤
      (f : ↥(inertiaSubgroup K) →* Multiplicative (ZMod p)).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have hcont : Continuous (fun y : ↥(wildInertiaSubgroup K) =>
      (f : ↥(inertiaSubgroup K) →* Multiplicative (ZMod p))
        ⟨y.1, wildInertiaSubgroup_le_inertiaSubgroup K y.2⟩) :=
    f.continuous_toFun.comp (Continuous.subtype_mk continuous_subtype_val _)
  let ψ : ↥(wildInertiaSubgroup K) →ₜ* Multiplicative (ZMod p) :=
    { toMonoidHom :=
        { toFun := fun y => (f : ↥(inertiaSubgroup K) →* Multiplicative (ZMod p))
            ⟨y.1, wildInertiaSubgroup_le_inertiaSubgroup K y.2⟩
          map_one' := map_one _
          map_mul' := fun a b =>
            map_mul (f : ↥(inertiaSubgroup K) →* Multiplicative (ZMod p))
              ⟨a.1, wildInertiaSubgroup_le_inertiaSubgroup K a.2⟩
              ⟨b.1, wildInertiaSubgroup_le_inertiaSubgroup K b.2⟩ }
      continuous_toFun := hcont }
  have hsub : Subsingleton (↥(wildInertiaSubgroup K) →ₜ* Multiplicative (ZMod p)) := by
    refine ⟨fun a b => ?_⟩
    haveI := continuousZModDual_wildInertia_subsingleton (K := K) p q hpq
    have h : Additive.ofMul a = Additive.ofMul b := Subsingleton.elim _ _
    simpa using congrArg Additive.toMul h
  have hψ1 : ψ = 1 := Subsingleton.elim ψ 1
  have key : ψ ⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩ = 1 := by
    rw [hψ1]
    rfl
  have hx' : (⟨x.1, wildInertiaSubgroup_le_inertiaSubgroup K
      (Subgroup.mem_subgroupOf.mp hx)⟩ : ↥(inertiaSubgroup K)) = x := Subtype.ext rfl
  rw [← hx']
  exact key

namespace InertiaTame

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime]

/-- **前推**：`χ ↦ χ ∘ toTameInertia`，即 `Hom_cont(I_t, μ_p) → Hom_cont(I, μ_p)`。 -/
noncomputable def restrictTameInertia :
    (↥(tameInertia F) →ₜ* Multiplicative (ZMod p)) →
      (↥(inertiaSubgroup F) →ₜ* Multiplicative (ZMod p)) :=
  fun χ => χ.comp (toTameInertia (K := F))

/-- **前推是单射**（`toTameInertia` 满射）。 -/
theorem restrictTameInertia_injective :
    Function.Injective (restrictTameInertia (F := F) p) := by
  intro χ₁ χ₂ h
  refine ContinuousMonoidHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := toTameInertia_surjective (K := F) y
  have h' := congrArg (fun g : ↥(inertiaSubgroup F) →ₜ* Multiplicative (ZMod p) => g x) h
  simpa [restrictTameInertia] using h'

/-- **前推是满射**：每个连续 `p`-特征杀 `P_K`，故经 `I ↠ I_t` 分解；
分解出的映射连续（补集沿闭映射的像）。 -/
theorem restrictTameInertia_surjective (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q] (hpq : p ≠ q) :
    Function.Surjective (restrictTameInertia (F := F) p) := by
  intro f
  have hker : (toTameInertia (K := F)).toMonoidHom.ker ≤
      (f : ↥(inertiaSubgroup F) →* Multiplicative (ZMod p)).ker := by
    rw [ker_toTameInertia]
    exact wildInertia_le_ker_zmodDual p q hpq f
  -- 抽象分解（`MonoidHom.liftOfSurjective`）
  set f' : ↥(inertiaSubgroup F) →* Multiplicative (ZMod p) :=
    (f : ↥(inertiaSubgroup F) →* Multiplicative (ZMod p)) with hf'
  obtain ⟨χ, hcomp⟩ : ∃ χ : ↥(tameInertia F) →* Multiplicative (ZMod p),
      χ.comp (toTameInertia (K := F)).toMonoidHom = f' := by
    refine ⟨((toTameInertia (K := F)).toMonoidHom.liftOfSurjective
      toTameInertia_surjective) ⟨f', hker⟩, ?_⟩
    simp
  -- 连续性
  have hcont : Continuous (χ : ↥(tameInertia F) → Multiplicative (ZMod p)) := by
    rw [continuous_discrete_rng]
    intro b
    have hclosedMap : IsClosedMap (toTameInertia (K := F) :
        ↥(inertiaSubgroup F) → ↥(tameInertia F)) :=
      (toTameInertia (K := F)).continuous_toFun.isClosedMap
    -- 关键等式：`f' x = χ (π x)`
    have hval : ∀ x, f' x = χ (toTameInertia (K := F) x) := by
      intro x
      have h := congrArg (fun g : ↥(inertiaSubgroup F) →* Multiplicative (ZMod p) => g x) hcomp
      simpa using h.symm
    -- `χ ⁻¹' {b} = π '' (f' ⁻¹' {b})`
    have himg : (χ : ↥(tameInertia F) → Multiplicative (ZMod p)) ⁻¹' {b}
        = toTameInertia (K := F) '' (f' ⁻¹' {b}) := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, rfl⟩ := toTameInertia_surjective (K := F) y
        refine ⟨x, ?_, rfl⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
        rw [hval x]
        exact hy
      · rintro ⟨x, hx, rfl⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
        rw [← hval x]
        exact hx
    -- `(π '' (f' ⁻¹' {b}))ᶜ = π '' (f' ⁻¹' {b})ᶜ`
    have hcompl : (toTameInertia (K := F) '' (f' ⁻¹' {b}))ᶜ
        = toTameInertia (K := F) '' ((f' ⁻¹' {b})ᶜ) := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, rfl⟩ := toTameInertia_surjective (K := F) y
        exact ⟨x, fun hx => hy ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩ hcon
        obtain ⟨x', hx', heq⟩ := hcon
        have h1 : f' x' = f' x := by rw [hval x', hval x, heq]
        refine hx ?_
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx' ⊢
        rw [← h1]; exact hx'
    -- `f' ⁻¹' {b}` 的补是闭的（靶离散）
    have hclcompl : IsClosed ((f' ⁻¹' {b})ᶜ : Set ↥(inertiaSubgroup F)) := by
      rw [← Set.preimage_compl]
      exact (isClosed_discrete _).preimage f.continuous_toFun
    rw [himg]
    have hA : toTameInertia (K := F) '' (f' ⁻¹' {b})
        = (toTameInertia (K := F) '' ((f' ⁻¹' {b})ᶜ))ᶜ := by
      rw [← hcompl, compl_compl]
    rw [hA]
    exact (hclosedMap _ hclcompl).isOpen_compl
  refine ⟨⟨χ, hcont⟩, ?_⟩
  refine ContinuousMonoidHom.ext fun x => ?_
  have h := congrArg (fun g : ↥(inertiaSubgroup F) →* Multiplicative (ZMod p) => g x) hcomp
  rw [hf'] at h
  simpa [restrictTameInertia] using h

/-- ★★★★★ **GMS (7.3) 的第一等号**：`Hom_cont(I, μ_p) ≅ Hom_cont(I_t, μ_p)`。 -/
theorem restrictTameInertia_bijective (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q] (hpq : p ≠ q) :
    Function.Bijective (restrictTameInertia (F := F) p) :=
  ⟨restrictTameInertia_injective (F := F) p,
    restrictTameInertia_surjective (F := F) p q hpq⟩

/-- 由 GMS (7.3) 第一等号得到的 `Equiv`（供 `Finite`／`Nat.card` 搬运）。 -/
noncomputable def equivTameInertia (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q] (hpq : p ≠ q) :
    (↥(tameInertia F) →ₜ* Multiplicative (ZMod p)) ≃
      (↥(inertiaSubgroup F) →ₜ* Multiplicative (ZMod p)) :=
  Equiv.ofBijective _ (restrictTameInertia_bijective (F := F) p q hpq)

/-- **`H¹(I,μ_p)` 有限 ⟺ `H¹(I_t,μ_p)` 有限**（TauCeti 载体）。 -/
theorem finite_zmodDual_inertia_iff (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q] (hpq : p ≠ q) :
    Finite (↥(inertiaSubgroup F) →ₜ* Multiplicative (ZMod p)) ↔
      Finite (↥(tameInertia F) →ₜ* Multiplicative (ZMod p)) :=
  (equivTameInertia (F := F) p q hpq).finite_iff.symm

/-- 沿 `Hyp517` 的载体同构 `↥(inertiaSubgroup F) ≃ₜ* ↥(inertiaLoc F)` 搬运同态集。 -/
noncomputable def equivInertiaLocInertia :
    (↥(inertiaLoc F) →ₜ* Multiplicative (ZMod p)) ≃
      (↥(inertiaSubgroup F) →ₜ* Multiplicative (ZMod p)) where
  toFun χ := χ.comp
    ⟨(inertiaEquivInertiaLoc (F := F)).toMulEquiv.toMonoidHom,
      (inertiaEquivInertiaLoc (F := F)).continuous_toFun⟩
  invFun ψ := ψ.comp
    ⟨(inertiaEquivInertiaLoc (F := F)).symm.toMulEquiv.toMonoidHom,
      (inertiaEquivInertiaLoc (F := F)).symm.continuous_toFun⟩
  left_inv χ := ContinuousMonoidHom.ext fun x => by simp
  right_inv ψ := ContinuousMonoidHom.ext fun x => by simp

/-- ★★★★ **`H¹(inertiaLoc, μ_p)` 有限 ⟺ `H¹(I_t, μ_p)` 有限**（**战役载体**）。 -/
theorem finite_zmodDual_inertiaLoc_iff (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q] (hpq : p ≠ q) :
    Finite (↥(inertiaLoc F) →ₜ* Multiplicative (ZMod p)) ↔
      Finite (↥(tameInertia F) →ₜ* Multiplicative (ZMod p)) :=
  (equivInertiaLocInertia (F := F) p).finite_iff.trans
    (finite_zmodDual_inertia_iff (F := F) p q hpq)

end InertiaTame

end L20261018

#print axioms L20261018.wildInertia_le_ker_zmodDual
#print axioms L20261018.InertiaTame.restrictTameInertia
#print axioms L20261018.InertiaTame.restrictTameInertia_injective
#print axioms L20261018.InertiaTame.restrictTameInertia_surjective
#print axioms L20261018.InertiaTame.restrictTameInertia_bijective
#print axioms L20261018.InertiaTame.equivTameInertia
#print axioms L20261018.InertiaTame.finite_zmodDual_inertia_iff
#print axioms L20261018.InertiaTame.finite_zmodDual_inertiaLoc_iff
