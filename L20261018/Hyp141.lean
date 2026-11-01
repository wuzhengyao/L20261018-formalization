import L20261018.Hyp140

/-!
# R983：**`HenselResidueData` 的结构搬运**（沿载体等价）

R982 已确认第 4 章两个载体不是同一类型，桥的第 1 段（Kummer 类）已落。
本文件给出**桥的第 2 段的结构部分**：把 `HenselResidueData` 沿三个线性等价
`(Θ₁ : V ≃ₗ V')`、`(Θ₂ : H2 ≃ₗ H2')`、`(Θv : VK ≃ₗ VK')` 搬运，**唯一条件是杯积相容**

    hcup : ∀ x y, Θ₂ (cup x y) = cup' (Θ₁ x) (Θ₁ y)

**⟹ T4／T5 的剩余工作被归约为「一条杯积相容等式」**（不再涉及任何 11 字段结构）。

字段搬运公式（各字段都定义在"拉回"一侧，故全部 `simp` 可算）：
`res' = Θv ∘ D.res ∘ Θ₂⁻¹`｜`val' = D.val ∘ Θ₁⁻¹`｜`infl' = Θ₁ ∘ D.infl ∘ Θv⁻¹`｜
`pi' = Θ₁ D.pi`｜`split'` 由 `D.split ∘ Θ₁⁻¹` 推。
-/

set_option maxHeartbeats 2000000

namespace L20261018

open scoped LinearMap

universe u

/-- **`HenselResidueData` 沿载体等价搬运**。唯一前提是杯积相容 `hcup`。 -/
noncomputable def henselResidueDataTransport
    {k : Type u} [Field k]
    {V V' H2 H2' VK VK' : Type u}
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    [AddCommGroup H2] [Module k H2] [AddCommGroup H2'] [Module k H2']
    [AddCommGroup VK] [Module k VK] [AddCommGroup VK'] [Module k VK']
    {cup : V →ₗ[k] V →ₗ[k] H2} {cup' : V' →ₗ[k] V' →ₗ[k] H2'}
    (Θ₁ : V ≃ₗ[k] V') (Θ₂ : H2 ≃ₗ[k] H2') (Θv : VK ≃ₗ[k] VK')
    (hcup : ∀ x y : V, Θ₂ (cup x y) = cup' (Θ₁ x) (Θ₁ y))
    (D : HenselResidueData k V H2 VK cup) :
    HenselResidueData k V' H2' VK' cup' where
  res :=
    { toFun := fun w => Θv (D.res (Θ₂.symm w))
      map_add' := by intro a b; simp
      map_smul' := by intro c a; simp }
  val :=
    { toFun := fun x => D.val (Θ₁.symm x)
      map_add' := by intro a b; simp
      map_smul' := by intro c a; simp }
  infl :=
    { toFun := fun y => Θ₁ (D.infl (Θv.symm y))
      map_add' := by intro a b; simp
      map_smul' := by intro c a; simp }
  inj_infl := by
    intro y z hyz
    have h1 : D.infl (Θv.symm y) = D.infl (Θv.symm z) := Θ₁.injective hyz
    exact Θv.symm.injective (D.inj_infl h1)
  val_infl := by
    intro y
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Θ₁.symm_apply_apply]
    exact D.val_infl (Θv.symm y)
  pi := Θ₁ D.pi
  val_pi := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Θ₁.symm_apply_apply]
    exact D.val_pi
  split := by
    intro x
    obtain ⟨x₀, m, hm⟩ := D.split (Θ₁.symm x)
    refine ⟨Θv x₀, m, ?_⟩
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Θv.symm_apply_apply]
    simpa using congrArg (fun t => Θ₁ t) hm
  tame_uu := by
    intro y z
    have hkey : cup' (Θ₁ (D.infl (Θv.symm y))) (Θ₁ (D.infl (Θv.symm z)))
        = Θ₂ (cup (D.infl (Θv.symm y)) (D.infl (Θv.symm z))) := (hcup _ _).symm
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [hkey, Θ₂.symm_apply_apply, D.tame_uu, map_zero]
  tame_u_pi := by
    intro y
    have hkey : cup' (Θ₁ (D.infl (Θv.symm y))) (Θ₁ D.pi)
        = Θ₂ (cup (D.infl (Θv.symm y)) D.pi) := (hcup _ _).symm
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [hkey, Θ₂.symm_apply_apply, D.tame_u_pi, Θv.apply_symm_apply]
  tame_pi_u := by
    intro κ hκ z
    have hκ' : D.val (Θ₁.symm κ) = 1 := hκ
    have hkey : cup' (Θ₁ (Θ₁.symm κ)) (Θ₁ (D.infl (Θv.symm z)))
        = Θ₂ (cup (Θ₁.symm κ) (D.infl (Θv.symm z))) := (hcup _ _).symm
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Θ₁.apply_symm_apply κ, hkey, Θ₂.symm_apply_apply,
      D.tame_pi_u (Θ₁.symm κ) hκ' (Θv.symm z), map_neg, Θv.apply_symm_apply]

end L20261018
#print axioms L20261018.henselResidueDataTransport
