import Hyp381

/-!
# R1296（S37 第 4 轮 · **S4 的系数对齐**）：`μ_p(F) ≅ ℤ/p` 作为 `G_F`-模

## 这一轮在补什么

论文的系数是 `μ_p = μ_p(F)`（**`F` 里的** `p` 次单位根），假设 `μ_p ⊂ F`。
本战役的机检件（`A.lean` 的 `GaloBase.muP K p`）把 `μ_p` **建模**为
**平凡作用的 `ZMod p`**：

```lean
noncomputable def muP : TopRep (ZMod p) (AbsoluteGaloisGroup K) :=
  TopRep.of (ContRepresentation.trivial (ZMod p) (AbsoluteGaloisGroup K) (ZMod p))
```

这个建模此前**没有机检过它的忠实性**。本轮补上：给定 `ζ : F` 是本源 `p` 次单位根，
`μ_p(F) := rootsOfUnity p F` 与平凡 `ZMod p` **是同一个 `ZMod p`-模**（`G_F` 等变），
从而 `H^i(G_F, μ_p(F)) ≅ H^i(G_F, ZMod p) = H^i(G_F, muP)`。
这正是 `GS68-CAMPAIGN` §1 的 S4「由 `μ_p ⊂ F` 把 `Z/p` 系数与 `μ_p` 系数对齐」的**系数半边**
（另一半 `r_v^i` 依赖 S2，见 `RECON-S2.md`）。

## 机检件

| 声明 | 内容 |
|---|---|
| `rootsOfUnity_nsmul_eq_zero` | `μ_p(F)` 的元素被 `p` 杀死（故有 `ZMod p`-模结构） |
| `zmod_smul_val` | `k • x = k.val • x`（`AddCommGroup.zmodModule` 的定义展开） |
| `zetaUnit` | `ζ` 作为单位 `Fˣ`（`hζ.ne_zero`） |
| `muGens` | `ζ` 作为 `Additive (rootsOfUnity p F)` 的元素 |
| **`muLinearEquiv`** | ★★★★★ `ZMod p ≃ₗ[ZMod p] Additive (rootsOfUnity p F)`（`k ↦ k • ζ`） |
| **`muPIso`** | ★★★★★ `muP F p ≅ ofDiscreteModule (ZMod p) (G_F) (μ_p(F))`（`G_F`-等变） |
| **`muCohomologyIso`** | ★★★★★ `H^i(G_F, μ_p(F)) ≅ H^i(G_F, ZMod p)`（全次数） |

## 忠实性口径

`muP` 的忠实性由 `muCohomologyIso` 机检：`H^i(G_F, muP)` 与「真的 `μ_p(F)` 的连续上同调」
同构。故本战役所有落在 `GaloBase.V`／`H2` 的陈述**可以**读作 `H¹(F,μ_p)`／`H²(F,μ_p)`。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

variable (p : ℕ) [NeZero p] [Fact p.Prime] (F : Type) [Field F]

/-! ### `μ_p(F)` 的 `ZMod p`-模结构 -/

/-- `μ_p(F)` 的元素被 `p` 乘死。 -/
theorem rootsOfUnity_nsmul_eq_zero (x : Additive (rootsOfUnity p F)) : p • x = 0 := by
  have h : ((Additive.toMul x : ↥(rootsOfUnity p F)) ^ p) = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity (M := F) p (Additive.toMul x : ↥(rootsOfUnity p F))).mp
      (Additive.toMul x).2
  apply Additive.toMul.injective
  rw [show (p • x).toMul = (Additive.toMul x : ↥(rootsOfUnity p F)) ^ p from rfl, h]
  rfl

/-- `μ_p(F)`（加性写法）是 `ZMod p`-模。 -/
noncomputable instance rootsOfUnityModule : Module (ZMod p) (Additive (rootsOfUnity p F)) :=
  AddCommGroup.zmodModule (rootsOfUnity_nsmul_eq_zero p F)

/-- `ZMod p` 的纯量作用就是 `val` 次加法累加（`zmodModule` 的定义展开）。 -/
theorem zmod_smul_val (hp : p ≠ 0) (k : ZMod p) (x : Additive (rootsOfUnity p F)) :
    k • x = k.val • x := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  rfl

/-! ### 拓扑与 `G_F`-作用（都是平凡的，因为 `μ_p ⊂ F`） -/

noncomputable instance : TopologicalSpace (Additive (rootsOfUnity p F)) := ⊥
noncomputable instance : DiscreteTopology (Additive (rootsOfUnity p F)) := ⟨rfl⟩

noncomputable instance : DistribMulAction (TauCeti.AbsoluteGaloisGroup F)
    (Additive (rootsOfUnity p F)) where
  smul _ m := m
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

noncomputable instance : SMulCommClass (TauCeti.AbsoluteGaloisGroup F) (ZMod p)
    (Additive (rootsOfUnity p F)) where
  smul_comm _ _ _ := rfl

noncomputable instance : ContinuousSMul (ZMod p) (Additive (rootsOfUnity p F)) :=
  ⟨continuous_of_discreteTopology⟩

noncomputable instance : ContinuousSMul (TauCeti.AbsoluteGaloisGroup F)
    (Additive (rootsOfUnity p F)) := ⟨continuous_snd⟩

/-! ### 生成元与线性等价 -/

/-- `ζ` 作为 `Fˣ` 的元素。 -/
noncomputable def zetaUnit {ζ : F} (hζ : IsPrimitiveRoot ζ p) : Fˣ :=
  Units.mk0 ζ (hζ.ne_zero (NeZero.ne p))

/-- `ζ` 作为 `Additive (rootsOfUnity p F)` 的元素。 -/
noncomputable def muGens {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    Additive (rootsOfUnity p F) :=
  Additive.ofMul ⟨zetaUnit p F hζ,
    (mem_rootsOfUnity (M := F) p (zetaUnit p F hζ)).mpr (by
      apply Units.ext
      simp [zetaUnit, hζ.pow_eq_one])⟩

theorem muGens_toMul {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    ((muGens p F hζ).toMul : Fˣ) = zetaUnit p F hζ := rfl

theorem muGens_ne_zero {ζ : F} (hζ : IsPrimitiveRoot ζ p) : muGens p F hζ ≠ 0 := by
  intro h
  have h1 : ((muGens p F hζ).toMul : Fˣ) = 1 := by rw [h]; rfl
  rw [muGens_toMul] at h1
  have hone : ζ = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) h1
    simpa [zetaUnit] using this
  exact hζ.ne_one (Fact.out (p := Nat.Prime p)).one_lt hone

/-- ★★★★★ **系数对齐**（`μ_p(F) ≅ ℤ/p`）：`k ↦ k • ζ` 是 `ZMod p`-线性等价。 -/
noncomputable def muLinearEquiv {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    ZMod p ≃ₗ[ZMod p] Additive (rootsOfUnity p F) :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (ZMod p) (Additive (rootsOfUnity p F)) (muGens p F hζ))
    (by
      have hp0 : p ≠ 0 := NeZero.ne p
      have hinj : Function.Injective
          fun k : ZMod p => k • muGens p F hζ := by
        intro k₁ k₂ h
        have h' : k₁ • muGens p F hζ = k₂ • muGens p F hζ := h
        have hz : (k₁ - k₂) • muGens p F hζ = 0 := by
          rw [sub_smul, h', sub_self]
        by_cases hk : k₁ - k₂ = 0
        · exact sub_eq_zero.mp hk
        · exfalso
          have h1 : muGens p F hζ = 0 := by
            calc muGens p F hζ = (1 : ZMod p) • muGens p F hζ := (one_smul _ _).symm
              _ = ((k₁ - k₂)⁻¹ * (k₁ - k₂)) • muGens p F hζ := by rw [inv_mul_cancel₀ hk]
              _ = (k₁ - k₂)⁻¹ • ((k₁ - k₂) • muGens p F hζ) := by rw [mul_smul]
              _ = 0 := by rw [hz, smul_zero]
          exact muGens_ne_zero p F hζ h1
      refine ⟨hinj, fun x => ?_⟩
      -- ζ 是本源的 ⟹ 每个 p 次单位根都是 ζ 的幂
      have hx : (((x.toMul : ↥(rootsOfUnity p F)) : Fˣ) : F) ^ p = 1 := by
        have h := (mem_rootsOfUnity (M := F) p (x.toMul : ↥(rootsOfUnity p F))).mp x.toMul.2
        simpa using congrArg (fun u : Fˣ => (u : F)) h
      obtain ⟨i, hi, hix⟩ := hζ.eq_pow_of_pow_eq_one hx
      refine ⟨(i : ZMod p), ?_⟩
      rw [LinearMap.toSpanSingleton_apply, zmod_smul_val p F hp0, ZMod.val_cast_of_lt hi]
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      rw [show (((i : ℕ) • muGens p F hζ).toMul : ↥(rootsOfUnity p F)) =
        (muGens p F hζ).toMul ^ i from rfl]
      simpa [muGens, zetaUnit] using hix)

/-! ### `TopRep` 层与上同调层的同构 -/

/-- 「真的」`μ_p(F)` 作为 `TopRep (ZMod p) (G_F)`。 -/
noncomputable abbrev muPReal : TopRep (ZMod p) (TauCeti.AbsoluteGaloisGroup F) :=
  TauCeti.ofDiscreteModule (ZMod p) (TauCeti.AbsoluteGaloisGroup F)
    (Additive (rootsOfUnity p F))

/-- ★★★★★ **`muP F p ≅ μ_p(F)`**（`G_F`-等变同构）。 -/
noncomputable def muPIso {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    GaloBase.muP F p ≅ muPReal p F :=
  TauCeti.ofDiscreteModuleIso (muLinearEquiv p F hζ) (fun _ _ => rfl)

/-- ★★★★★ **S4 的系数对齐（上同调层）**：`H^i(G_F, μ_p(F)) ≅ H^i(G_F, ZMod p)`。 -/
noncomputable def muCohomologyIso {ζ : F} (hζ : IsPrimitiveRoot ζ p) (i : ℕ) :
    continuousCohomology i (muPReal p F) ≅
      continuousCohomology i (GaloBase.muP F p) :=
  CategoryTheory.Functor.mapIso
    (TauCeti.ContinuousCohomology.continuousCohomologyFunctor (ZMod p)
      (TauCeti.AbsoluteGaloisGroup F) i) (muPIso p F hζ).symm

end L20261018

#print axioms L20261018.rootsOfUnity_nsmul_eq_zero
#print axioms L20261018.zmod_smul_val
#print axioms L20261018.muGens_ne_zero
#print axioms L20261018.muLinearEquiv
#print axioms L20261018.muPIso
#print axioms L20261018.muCohomologyIso
