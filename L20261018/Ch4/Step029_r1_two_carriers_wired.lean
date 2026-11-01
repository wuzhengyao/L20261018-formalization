import L20261018.Ch4.Step028_r1_linear_transport
import L20261018.Ch2.Hensel.ResidueMap.Step028_residue_phi_injective
import L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness

/-!
# R1170（**残余 A 收口：(R1) 的两载体接线**）

## 本轮做什么

`Hyp285.exists_henselResidueData_of_le_range` 需要 (R1) 在 **`muNRep` 载体**上：

```
Injective (residuePhi ((kummerCupPairing ζ hζ).cup 1 1) (valH1LinearGen v hp) ((π)))
```

而 `Hyp201.residuePhi_injective_of_norm_form` 已在 **`GaloBase` 载体**上证出同一事实
（假设正是论文的 Hensel 层级：`[HenselianRing ↥𝒪[F] 𝔪]`，**无完备性**）。本轮把它接过来。

## 关键发现（避开整个 `Θ₁/Θ₂` 语料）

`Hyp156` 的 `theta1_free`／`theta2_free` 走的是
`GaloBase ⟶ H¹(G^Tc, ZMod p) ⟶ H¹(G^m, ZMod p) ⟶ H¹(μ_p)`
的三段链；但 `Hyp81` 的 **`H2Bridge.redEquiv`／`redEquiv1`** 已经是**同一三段链的合成**
（`GaloBase.V ≃+ muNRep H¹`、`GaloBase.H2 ≃+ muNRep H²`），且 `redEquiv_cup` 直接给出**杯积相容**：

```
redEquiv (cup_Galo A B) = kummerCupPairing.cup (redEquiv1 A) (redEquiv1 B)
```

⟹ **不需要** `Θ₁((π)) = (π)` 与 `val ∘ Θ₁ = val` 的两条独立对齐等式，只需：
1. **`hbridge π`**（`Hyp201` 已作为假设传入；`∅-bridge`，载体身份）；
2. **`val` 相容** `valH1LinearGen v hp (redEquiv1 x) = valLinOf v hp x` —— 本轮机检为
   `valH1LinearGen_redEquiv1`，**只由两条 `v̄` 的值公式 ＋ `hbridge` ＋ `kummerClass` 满射**得出
   （两侧在 `(a)` 上都等于 `v(a) mod p`，见 `valLinOf_kummerClass` 与 `valH1Gen_kummerClass`）。

## 本轮

| 声明 | 内容 |
|---|---|
| **`injective_of_comp_eq_fun`** | ★★★★ 单射性沿**任意**满射 `e` ＋ 单射 `e₂` 运输（比 `Hyp286` 的线性等价版更宽，避开构造 `≃ₗ` 的 `map_smul` 义务） |
| **`valH1LinearGen_redEquiv1`** | ★★★★★ **`v̄_muNRep ∘ redEquiv1 = v̄_Galo`**（残余 A 的第二条对齐） |
| **`residuePhi_injective_muNRep`** | ★★★★★ ****(R1) 在 `muNRep` 载体上成立**（论文 Hensel 层级）** |
| **`tameResidueFacts_Galo_of_span_eq_bot`** | ★★★★★ 第 4 章用：`GaloBase` 载体上 `residueSpan = ⊥ ⟹ TameResidueFacts`（(R2) 是唯一残余） |
| **`exists_henselResidueData_of_norm_form`** | ★★★★★ `Hyp285` 的 `hR1` **已填**：一般 Hensel 的 `D` 存在，只差不分歧分解 |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

/-! ## 1. 单射性沿「满射 ＋ 单射」运输（函数层，不需线性） -/

/-- ★★★★ **单射性沿任意满射 ＋ 单射运输**：`e : W ↠ W'`、`e₂ : H2 ↪ H2'`、
交换方块 `e₂ ∘ Φ = Φ' ∘ e`、`Φ` 单射 ⟹ `Φ'` 单射。

`Hyp286.injective_of_comp_eq` 要求 `≃ₗ`（于是要造 `map_smul`）；此处只需函数层的满射／单射，
正合本战役的用途（`e`／`e₂` 由 `AddEquiv` 提供）。 -/
theorem injective_of_comp_eq_fun
    {W : Type*} {W' : Type*} {H2 : Type*} {H2' : Type*}
    (Φ : W → H2) (Φ' : W' → H2') (e : W → W') (e₂ : H2 → H2')
    (he : Function.Surjective e) (he₂ : Function.Injective e₂)
    (hsq : ∀ x, e₂ (Φ x) = Φ' (e x)) (h : Function.Injective Φ) :
    Function.Injective Φ' := by
  intro x y hxy
  obtain ⟨x', rfl⟩ := he x
  obtain ⟨y', rfl⟩ := he y
  rw [← hsq x', ← hsq y'] at hxy
  rw [h (he₂ hxy)]

/-! ## 2. `v̄` 的两载体相容（残余 A 的对齐 #2） -/

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★★ **`v̄` 在两载体下一致**：`valH1LinearGen v hp (redEquiv1 x) = valLinOf v hp x`。

证明只用「两条 `v̄` 在 Kummer 类上同值」＋`hbridge`＋`kummerClass` 满射：
* `valLinOf_kummerClass`（`Hyp162`）：`valLinOf v hp ((a)) = v(a) mod p`；
* `valH1Gen_kummerClass`（`Hyp279`）：`valH1Gen v hp ((a)) = v(a) mod p`；
* `hbridge`（`Hyp201`／`Hyp164`）：`redEquiv1 ((a)_Galo) = (a)_muNRep`。

⟹ 两侧在满射族 `{(a)}` 上逐点相等，故处处相等。**此路完全绕过 `Hyp162` 的
`valLin_eq_valLinOf_normalizedValuation`（那条需完备性 `IsNonarchimedeanLocalField`，本层不用）。** -/
theorem valH1LinearGen_redEquiv1 {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F))
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hp a)
      = ClassFieldTheory.kummerClass F hp a)
    (x : GaloBase.V F p) :
    valH1LinearGen (p := p) v hp (H2Bridge.redEquiv1 hζ x) = valLinOf p v hp x := by
  obtain ⟨a, rfl⟩ := KummerV.kummerClass_surjective (F := F) (p := p) hp x
  rw [hbridge a]
  show valH1Gen (p := p) v hp (ClassFieldTheory.kummerClass F hp a)
    = valLinOf p v hp (KummerBridge.kummerClass F p hp a)
  rw [valH1Gen_kummerClass, valLinOf_kummerClass, valOfUnitOf]

/-! ## 3. (R1) 在 `muNRep` 载体上 -/

variable [ValuativeRel F] [TopologicalSpace F]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ} {ζ : F}

/-- ★★★★★ ****(R1) 直接落在 `muNRep` 载体上**（论文 Hensel 层级，**无完备性**）。

把 `Hyp201.residuePhi_injective_of_norm_form`（`GaloBase` 载体）沿
`redEquiv1`／`redEquiv` 搬到 `Hyp285` 需要的载体。交换方块由
`H2Bridge.redEquiv_cup` ＋ `hbridge π` 逐点给出。 -/
theorem residuePhi_injective_muNRep
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Function.Injective (residuePhi ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hpF) (ClassFieldTheory.kummerClass F hpF π)) := by
  have hG := residuePhi_injective_of_norm_form (F := F) p hp hpF hζ hbridge hv hπ hp2
  -- 载体等价 `e : ker v̄_Galo → ker v̄_muNRep`（由 `redEquiv1` 限制）
  let e : ↥(LinearMap.ker (valLinOf p v hpF)) → ↥(LinearMap.ker (valH1LinearGen (p := p) v hpF)) :=
    fun x => ⟨H2Bridge.redEquiv1 hζ (x : GaloBase.V F p), by
      rw [LinearMap.mem_ker,
        valH1LinearGen_redEquiv1 (F := F) (p := p) hζ v hpF hbridge (x : GaloBase.V F p)]
      exact x.2⟩
  refine injective_of_comp_eq_fun _ _ e (H2Bridge.redEquiv hζ) ?_ (H2Bridge.redEquiv hζ).injective ?_ hG
  · -- `e` 满射（`redEquiv1` 是等价，`ker` 由 §2 的等式互相定义）
    intro y
    refine ⟨⟨(H2Bridge.redEquiv1 hζ).symm (y : ↑(continuousCohomology 1
      (ClassFieldTheory.muNRep p F)).toModuleCat), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker]
      rw [← valH1LinearGen_redEquiv1 (F := F) (p := p) hζ v hpF hbridge]
      rw [AddEquiv.apply_symm_apply]
      exact y.2
    · exact Subtype.ext (AddEquiv.apply_symm_apply (H2Bridge.redEquiv1 hζ) (y :
        ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat))
  · -- 交换方块：`redEquiv ∘ Φ_Galo = Φ_muNRep ∘ e`
    intro x
    show H2Bridge.redEquiv hζ (GaloBase.cup (K := F) (p := p) (x : GaloBase.V F p)
        (KummerBridge.kummerClass F p hpF π))
      = ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
          ((e x : ↥(LinearMap.ker (valH1LinearGen (p := p) v hpF))) :
            ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat)
          (ClassFieldTheory.kummerClass F hpF π)
    rw [H2Bridge.redEquiv_cup, hbridge π]

/-! ## 4. 第 4 章侧的「只剩 (R2)」形态（`GaloBase` 载体） -/

section GaloBaseSide

/-- ★★★★★ **第 4 章的四条定理只差 (R2)**：在 `GaloBase` 载体上，若
`residueSpan (cup_Galo) (valLinOf v hp) = ⊥`（**唯一残余**），则 `TameResidueFacts` 成立。

⟹ `Hyp162.orth_eq_bot_of_discrete_valuation`／`thm_ramified_1_of_discrete_valuation`／
`corollary_4_4_of_discrete_valuation` 的三条 `hfacts` 输入**从此可被消去**（只余 (R2)）。 -/
theorem tameResidueFacts_Galo_of_span_eq_bot
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hspan : residueSpan (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) = ⊥) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) :=
  tameResidueFacts_of_span_eq_bot hspan
    (residuePhi_injective_of_norm_form (F := F) p hp hpF hζ hbridge hv hπ hp2)

end GaloBaseSide

/-! ## 5. 一般 Hensel 的 `D`：`hR1` 已填 -/

section Assembly

/-- ★★★★★ **一般 Hensel 的 `D` 存在 —— `Hyp285` 的 `hR1` 已机检填上**。

与 `Hyp285.exists_henselResidueData_of_le_range` 相比，**(R1)** 从假设变为
`residuePhi_injective_muNRep` 的结论（代价：论文 Hensel 层级的常规假设 ＋ `∅-bridge`）。
⟹ 第 5 项的剩余**只剩一条**：不分歧分解 `residueSpan ≤ range f`（`f` 定义域 subsingleton）。 -/
theorem exists_henselResidueData_of_norm_form
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hskew : ∀ x y, ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) x y
      = -(((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) y x))
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M] [Subsingleton M]
    (f : M →ₗ[ZMod p]
      ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat)
    (hdecomp : residueSpan ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hpF) ≤ LinearMap.range f) :
    ∃ D : HenselResidueData (ZMod p)
        ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat
        ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat
        ↥(LinearMap.ker (valH1LinearGen (p := p) v hpF))
        ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1),
      D.val = valH1LinearGen (p := p) v hpF :=
  exists_henselResidueData_of_le_range (p := p) v hpF hζ hπ hskew
    (residuePhi_injective_muNRep (F := F) (p := p) (v := v) (π := π) hp hpF hζ hbridge hv hπ hp2)
    f hdecomp

end Assembly

end L20261018

#print axioms L20261018.injective_of_comp_eq_fun
#print axioms L20261018.valH1LinearGen_redEquiv1
#print axioms L20261018.residuePhi_injective_muNRep
#print axioms L20261018.tameResidueFacts_Galo_of_span_eq_bot
#print axioms L20261018.exists_henselResidueData_of_norm_form
