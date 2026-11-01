import L20261018.Infra.Cohomology.Coinduced.Step003_coind_subgroup_acyclic_one

/-!
# S64 R2：`C2-INFRA-1′` —— 有限指数闭子群的**左陪集**分解

`Coind_⊥^G A ≃+[H] Coind_⊥^H (G ⧸ H → A)`（`H ≤ G` 有限指数、闭）。

## 为什么取**左**陪集（`S64-INFRA-PLAN.md` §0.1）

`PROMPT-S64` §① 的右陪集公式 `G = ⊔ V x_i` 带扭 `x_i v = u_i x_{σ(i)}`（右乘 `v` **不保持**右陪集）。
改取左陪集 `⊔ x_i H`：右乘 `h ∈ H` 把 `x_i H → x_i H h = x_i H`（**保持**），经 `u ↦ x_i u` 把
`x_i H ≅ H` 后作用正是**逐分量右平移**，**无扭**。

## 内容

| 声明 | 内容 |
|---|---|
| `cosRep` / `hCoord` | 左陪集代表与 `H`-坐标：`g = cosRep g * hCoord g` |
| `cosRep_mul_hCoord` / `mk_mul_coe` / `hCoord_cosRep_mul` | 三条群论恒等式（分解的骨架） |
| `toFun` / `invFun` | `f ↦ (u ↦ (x ↦ f (x.out * u)))` ／ `F ↦ (g ↦ F (hCoord g) (mk g))` |
| `coindBotAddEquiv` | ★ `DiscreteCoind G ⊥ A ≃+ DiscreteCoind H ⊥ (G ⧸ H → A)` |
| `toFun_smul` | ★ `H`-等变（右平移） |
| `subsingleton_continuousCohomology_one_coindBot` | ★★ 有限指数：`H¹(H, Coind_⊥^G A) = 0` |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

universe u

/-! ## A 陪集分解的群论部分 -/

section Coset

variable {G : Type u} [Group G] {H : Subgroup G}

/-- `g` 的**左**陪集代表（`Quotient.out`）；`G ⧸ H` 在 Mathlib 中是左陪集 `{gH}`。 -/
noncomputable def cosRep (g : G) : G := (Quotient.mk (QuotientGroup.leftRel H) g).out

/-- `g` 在其左陪集代表下的 `H`-坐标：`g = cosRep g * hCoord g`。 -/
noncomputable def hCoord (g : G) : H :=
  ⟨(cosRep (H := H) g)⁻¹ * g,
    QuotientGroup.leftRel_apply.mp (Quotient.exact (Quotient.out_eq (Quotient.mk _ g)))⟩

theorem cosRep_mul_hCoord (g : G) : cosRep (H := H) g * (hCoord (H := H) g : G) = g := by
  show cosRep (H := H) g * ((cosRep (H := H) g)⁻¹ * g) = g
  exact mul_inv_cancel_left _ _

/-- 左陪集代表乘 `H` 的元素不改变陪集。 -/
theorem mk_mul_coe (x : G ⧸ H) (u : H) :
    (Quotient.mk (QuotientGroup.leftRel H) (x.out * (u : G)) : G ⧸ H) = x := by
  have h : (Quotient.mk (QuotientGroup.leftRel H) (x.out * (u : G)) : G ⧸ H)
      = Quotient.mk (QuotientGroup.leftRel H) x.out :=
    Quotient.sound (QuotientGroup.leftRel_apply.mpr (by
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using H.inv_mem u.2))
  rw [h, Quotient.out_eq]

/-- `H`-坐标在 `x.out * u` 上就是 `u`。 -/
theorem hCoord_cosRep_mul (x : G ⧸ H) (u : H) : hCoord (H := H) (x.out * (u : G)) = u := by
  refine Subtype.ext ?_
  show (cosRep (H := H) (x.out * (u : G)))⁻¹ * (x.out * (u : G)) = (u : G)
  have h1 : cosRep (H := H) (x.out * (u : G)) = x.out := by
    show (Quotient.mk (QuotientGroup.leftRel H) (x.out * (u : G))).out = x.out
    rw [mk_mul_coe]
  rw [h1]
  exact inv_mul_cancel_left _ _

end Coset

/-! ## B–E 主构造 -/

section Main

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G]
variable {H : Subgroup G} [H.FiniteIndex]
variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-! ### B 前进映射 -/

/-- 前进映射的函数部分：`f ↦ (u ↦ (x ↦ f (x.out * u)))`。 -/
noncomputable def toFunFun (f : DiscreteCoind G ⊥ A) : H → (G ⧸ H → A) :=
  fun u x => f (x.out * (u : G))

theorem isLocallyConstant_toFunFun (f : DiscreteCoind G ⊥ A) :
    IsLocallyConstant (toFunFun (H := H) f) := by
  haveI : DiscreteTopology (G ⧸ H → A) := Pi.discreteTopology
  rw [IsLocallyConstant.iff_continuous]
  rw [continuous_pi_iff]
  intro x
  exact ((DiscreteCoind.isLocallyConstant f).comp_continuous
    (continuous_const.mul continuous_subtype_val)).continuous

noncomputable def toFun (f : DiscreteCoind G ⊥ A) : DiscreteCoind H ⊥ (G ⧸ H → A) :=
  DiscreteCoind.mk H ⊥ (G ⧸ H → A) (toFunFun (H := H) f)
    (isLocallyConstant_toFunFun (H := H) f)
    (fun u g => by
      funext x
      have hu : ((u : ↥(⊥ : Subgroup H)) : ↥H) = 1 := Subgroup.mem_bot.mp u.2
      simp only [toFunFun, Subgroup.smul_def, Pi.smul_apply, hu, one_mul, one_smul])

/-! ### C 反向映射 -/

/-- 反向映射的函数部分：`F ↦ (g ↦ F (hCoord g) (mk g))`。 -/
noncomputable def invFunFun (F : H → (G ⧸ H → A)) (g : G) : A :=
  F (hCoord (H := H) g) (Quotient.mk (QuotientGroup.leftRel H) g)

/-- `H` 开时，`g ↦ gH`（左陪集）局部常值。 -/
theorem isLocallyConstant_mk_quotient (hH : IsOpen (H : Set G)) :
    IsLocallyConstant (fun g : G => (Quotient.mk (QuotientGroup.leftRel H) g : G ⧸ H)) := by
  haveI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology_iff.2 hH
  intro s
  exact (isOpen_discrete s).preimage continuous_quotient_mk'

/-- `H` 开时 `hCoord : G → H` 连续（在每个开陪集 `x.out·H` 上就是 `g ↦ x.out⁻¹ * g`）。 -/
theorem continuous_hCoord (hH : IsOpen (H : Set G)) : Continuous (hCoord (H := H)) := by
  haveI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology_iff.2 hH
  have houtLC : IsLocallyConstant fun x : G ⧸ H => x.out := fun _ => isOpen_discrete _
  have hout : Continuous fun g : G => (Quotient.mk (QuotientGroup.leftRel H) g).out :=
    (houtLC.comp_continuous (isLocallyConstant_mk_quotient (H := H) hH).continuous).continuous
  have hval : Continuous fun g : G => (hCoord (H := H) g : G) := by
    have h1 : (fun g : G => (hCoord (H := H) g : G))
        = fun g : G => (Quotient.mk (QuotientGroup.leftRel H) g).out⁻¹ * g := rfl
    rw [h1]
    exact hout.inv.mul continuous_id
  exact hval.subtype_mk _

theorem isLocallyConstant_invFunFun (hH : IsOpen (H : Set G)) {F : H → (G ⧸ H → A)}
    (hF : IsLocallyConstant F) : IsLocallyConstant (invFunFun (H := H) F) := by
  haveI : DiscreteTopology (G ⧸ H → A) := Pi.discreteTopology
  haveI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology_iff.2 hH
  rw [IsLocallyConstant.iff_continuous]
  have hFc : Continuous F := (IsLocallyConstant.iff_continuous F).mp hF
  have hev : Continuous fun p : (G ⧸ H → A) × (G ⧸ H) => p.1 p.2 :=
    continuous_of_discreteTopology
  exact hev.comp ((hFc.comp (continuous_hCoord (H := H) hH)).prodMk
    (isLocallyConstant_mk_quotient (H := H) hH).continuous)

noncomputable def invFun (hH : IsOpen (H : Set G)) (F : DiscreteCoind H ⊥ (G ⧸ H → A)) :
    DiscreteCoind G ⊥ A :=
  DiscreteCoind.mk G ⊥ A (invFunFun (H := H) F)
    (isLocallyConstant_invFunFun (H := H) hH (DiscreteCoind.isLocallyConstant F))
    (fun u g => by
      have hu : ((u : ↥(⊥ : Subgroup G)) : G) = 1 := Subgroup.mem_bot.mp u.2
      simp only [invFunFun, Subgroup.smul_def, hu, one_mul, one_smul])

/-! ### D 往返两条 -/

theorem invFun_toFun (hH : IsOpen (H : Set G)) (f : DiscreteCoind G ⊥ A) :
    invFun (H := H) hH (toFun (H := H) f) = f := by
  refine DiscreteCoind.ext fun g => ?_
  show toFunFun (H := H) f (hCoord (H := H) g) (Quotient.mk (QuotientGroup.leftRel H) g) = f g
  show f (cosRep (H := H) g * (hCoord (H := H) g : G)) = f g
  rw [cosRep_mul_hCoord]

theorem toFun_invFun (hH : IsOpen (H : Set G)) (F : DiscreteCoind H ⊥ (G ⧸ H → A)) :
    toFun (H := H) (invFun (H := H) hH F) = F := by
  refine DiscreteCoind.ext fun u => ?_
  funext x
  show invFunFun (H := H) F (x.out * (u : G)) = F u x
  show F (hCoord (H := H) (x.out * (u : G)))
      (Quotient.mk (QuotientGroup.leftRel H) (x.out * (u : G))) = F u x
  rw [hCoord_cosRep_mul, mk_mul_coe]

/-- ★ **`C2-INFRA-1′`（加法等价形态）**：`H` 开、有限指数时
`Coind_⊥^G A ≃+ Coind_⊥^H (G ⧸ H → A)`。 -/
noncomputable def coindBotAddEquiv (hH : IsOpen (H : Set G)) :
    DiscreteCoind G ⊥ A ≃+ DiscreteCoind H ⊥ (G ⧸ H → A) where
  toFun := toFun (H := H)
  invFun := invFun (H := H) hH
  left_inv := invFun_toFun (H := H) hH
  right_inv := toFun_invFun (H := H) hH
  map_add' f g := rfl

/-! ### E `H`-等变（右平移） -/

/-- ★ **`H`-等变性**：前进映射与右平移交换。 -/
theorem toFun_smul (h : H) (f : DiscreteCoind G ⊥ A) :
    toFun (H := H) (h • f) = h • toFun (H := H) f := by
  refine DiscreteCoind.ext fun u => ?_
  funext x
  show (h • f) (x.out * (u : G)) = (h • toFun (H := H) f) u x
  rw [Subgroup.smul_def (S := H) h f, DiscreteCoind.coe_smul, DiscreteCoind.coe_smul]
  show f (x.out * (u : G) * (h : G)) = toFunFun (H := H) f ((u : H) * h) x
  show f (x.out * (u : G) * (h : G)) = f (x.out * (((u : H) * h : H) : G))
  rw [Subgroup.coe_mul, mul_assoc]

end Main

/-! ## F 有限指数：`H¹(H, Coind_⊥^G A) = 0` -/

section Zero

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G] [TotallyDisconnectedSpace G]
variable {H : Subgroup G} [H.FiniteIndex] [IsClosed (H : Set G)]
variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

instance : CompactSpace ↥H := isCompact_iff_compactSpace.mp ‹IsClosed (H : Set G)›.isCompact

/-- `Coind_⊥^H M` 在 `H` 上一阶零调（Shapiro ＋ 平凡群）。 -/
theorem subsingleton_H1_discreteCoind_bot_self :
    Subsingleton (continuousCohomology 1
      (ofDiscreteModule ℤ ↥H (DiscreteCoind H ⊥ (G ⧸ H → A)))) := by
  have hbot : Subsingleton (continuousCohomology 1
      (ofDiscreteModule ℤ (↥(⊥ : Subgroup H)) (G ⧸ H → A))) :=
    ContinuousCohomology.subsingleton_continuousCohomology_succ_of_subsingleton
      (k := ℤ) (G := ↥(⊥ : Subgroup H)) _ 0
  exact (ContinuousCohomology.subsingleton_continuousCohomology_discreteCoind_iff
    (G := ↥H) ⊥ (Subgroup.coe_bot (G := ↥H) ▸ isClosed_singleton) (G ⧸ H → A) 1).mpr hbot

/-- ★★ **有限指数闭子群上的零调性**：`H¹(H, Coind_⊥^G A) = 0`。

沿 `coindBotAddEquiv` 把系数换成 `Coind_⊥^H (G ⧸ H → A)`，再对 `⊥ ≤ H` 用 Shapiro。 -/
theorem subsingleton_continuousCohomology_one_coindBot (hH : IsOpen (H : Set G)) :
    Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥H (DiscreteCoind G ⊥ A))) := by
  haveI hY := subsingleton_H1_discreteCoind_bot_self (G := G) (H := H) (A := A)
  exact ContinuousCohomology.subsingleton_continuousCohomology_of_iso
    (ofDiscreteModuleIso (coindBotAddEquiv (H := H) hH).toIntLinearEquiv (toFun_smul (H := H))) 1

end Zero

end L20261018

#print axioms L20261018.coindBotAddEquiv
#print axioms L20261018.toFun_smul
#print axioms L20261018.subsingleton_continuousCohomology_one_coindBot
