import Hyp287

/-!
# R1171（**残余 B 收口：把「不分歧分解」压成一条纯代数陈述**）

## 本轮做什么

`Hyp287.exists_henselResidueData_of_norm_form` 把一般 Hensel 的 `D` 归约到 `hdecomp`，而
`Hyp285.residueSpan_eq_bot_of_le_range` 已机检 `hdecomp ⟺ residueSpan = ⊥`。
⟹ 第 5 项的**唯一残余**就是 `residueSpan cup val = ⊥`（＝论文 (R2)）。

本轮把它**压成一条纯代数陈述**，并给出**为什么不必走 inflation 路**的实测证据。

## 数学内容（三块，全部 `[Field F]` 层级）

### 块 1：`ker v̄` 恰好由**真正的单位**类张成

`valH1Gen_kummerClass` 给 `v̄((a)) = v(a) mod p`。故 `y ∈ ker v̄` ⟹ 可取 `a` 使
`y = (a)` 且 `v(a) ≡ 0 (mod p)`。再用 `π^{-v(a)}` 把 `a` 化成**单位**
`u = a · π^{-v(a)}`（`Hyp280.val_mul_uniformizer_zpow`：`v(u) = 1`），
而 `(a) = (u) + v(a)•(π) = (u)`（因 `v(a) ≡ 0` ⟹ 该项为 `0`）。
⟹ `exists_unit_of_valH1Gen_eq_zero`。

### 块 2：单位×单位杯积为零 ⟹ `residueSpan = ⊥`

`residueSpan` 是 `{cup y z}_{y,z ∈ ker v̄}` 的张成，块 1 把生成元换成 `cup (u) (w)`
⟹ 单位×单位消失时整个子空间塌为 `⊥`（`residueSpan_eq_bot_of_units`）。

### 块 3（★ 本轮的决定性一步）：单位×单位杯积 = 0 **等价于**「单位是范数」

`TauCeti.ClassFieldTheory.cup_kummerClass_eq_zero_iff_mem_normGroup` 的**完整上下文**
（本轮 `#check` 实测）**只有 `[Field K]`**：

```
(hζ : IsPrimitiveRoot ζ n) (hn : IsUnit ↑n) {L} [Field L] [Algebra K L] [FiniteDimensional K L]
  (a b : Kˣ) {s : L}, s ^ n = algebraMap K L b → K⟮s⟯ = ⊤ →
    (cup (kummerClass a) (kummerClass b) = 0 ↔ a ∈ normGroup K L)
```

**无 `IsNonarchimedeanLocalField`、无 `ValuativeRel`、无完备性。**
⟹ (R2) 等价于**纯代数**陈述（记 `NormUnits`）：
「对任意单位 `u, w`，`u` 是 `F(w^{1/p})/F` 的范数」。

## 为什么**不**走 `PROMPT-S33` §⑤ 的 inflation 路（`L46` 侦察实测）

| 需要件 | 库内状态 | 结论 |
|---|---|---|
| inflation × cup 相容 | ✅ **`Cup/Inflation.lean:155 explicitInfl2_explicitCup11`**（`@[simp]`） | 可复用 |
| `H²(𝕜, M) = 0` | ✅ `zHat.subsingleton_continuousCohomology_two_of_isAddTorsion` | 可复用 |
| `G_𝕜 ≃ Ẑ` 的**绝对层**识别 | ❌ 全库 0 命中（只有有限层 `ResidueCorrespondence.lean:150 residueFieldAutEquiv`） | **须自建** |
| `IsUnramified`／惯性／不分歧 CFT | ⚠️ **全部 section 含 `IsNonarchimedeanLocalField`（完备）** | **须去完备（周级）** |
| 「单位 ⟹ 不分歧」 | ⚠️ `Unramified/Criterion.lean:93` 只给完备情形 | **须去完备** |

⟹ inflation 路在一般 Hensel 下要自建整套不分歧理论；而**块 3 的路只需一条范数陈述**。

## 本轮

| 声明 | 内容 |
|---|---|
| **`exists_unit_of_valH1Gen_eq_zero`** | ★★★★★ **`ker v̄` 的类都是真正单位的 Kummer 类** |
| **`residueSpan_eq_bot_of_units`** | ★★★★★ **单位×单位杯积为零 ⟹ `residueSpan = ⊥`** |
| **`cup_kummerClass_unit_eq_zero_of_norm`** | ★★★★★ **（块 3）`u ∈ normGroup F L ⟹ (u)∪(w) = 0`**（TauCeti 的**类无关**定理，无完备性） |
| **`residueSpan_eq_bot_of_norm`** | ★★★★★ 合成：范数条件 ⟹ `residueSpan = ⊥` |
| **`unitsCupVanish_of_subsingleton`** | 非空见证（`H² = 0` ⟹ 假设成立） |
| **`tameResidueFacts_of_units_cup`** | (R2) 已消 ⟹ `TameResidueFacts`（(R1) 由 `Hyp287` 给） |
| **`exists_henselResidueData_of_units_cup`** | ★★★★★ **一般 Hensel 的 `D` 存在，唯一残余 = 单位×单位杯积为零** |
| **`residueSpan_Galo_eq_bot_of_muNRep`** | 把 `residueSpan = ⊥` 运回 `GaloBase` 载体（第 4 章用） |
| **`tameResidueFacts_Galo_of_units_cup`** | ★★★★★ **第 4 章四条定理只剩一条单位×单位杯积** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

variable {F : Type} [Field F] {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-! ## 1. `ker v̄` 的类都是真正单位的 Kummer 类 -/

/-- ★★★★★ **`ker v̄` 恰好由真正的单位类生成**：若 `v̄(y) = 0`，则存在**单位**
`u`（即 `v u = 1`）使 `y = (u)`。

`v̄` 的分子 `v` 只到 `ZMod p`，故 `v̄(y) = 0` 只说明 `v(a) ≡ 0 (mod p)`。用一致化元
`π` 的 `-v(a)` 次幂把 `a` 化成单位（`val_mul_uniformizer_zpow`），而 `(a)` 与 `(u)` 的差
是 `v(a)•(π)`，该系数在 `ZMod p` 中为 `0` ⟹ 差为零。 -/
theorem exists_unit_of_valH1Gen_eq_zero (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F))
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    {y : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat}
    (hy : valH1Gen (p := p) v hp y = 0) :
    ∃ u : Fˣ, v u = 1 ∧ y = ClassFieldTheory.kummerClass F hp u := by
  obtain ⟨a, rfl⟩ := ClassFieldTheory.kummerClass_surjective F hp y
  refine ⟨a * π ^ (-(Multiplicative.toAdd (v a))), val_mul_uniformizer_zpow v hπ a, ?_⟩
  have hn : ((Multiplicative.toAdd (v a) : ℤ) : ZMod p) = 0 := by
    have h := hy
    rw [valH1Gen_kummerClass] at h
    exact h
  have hz : (-(Multiplicative.toAdd (v a))) • ClassFieldTheory.kummerClass F hp π = 0 := by
    rw [neg_smul]
    have h2 : Multiplicative.toAdd (v a) • ClassFieldTheory.kummerClass F hp π = 0 := by
      rw [← Int.cast_smul_eq_zsmul (ZMod p), hn, zero_smul]
    rw [h2, neg_zero]
  rw [ClassFieldTheory.kummerClass_mul, ClassFieldTheory.kummerClass_zpow, hz, add_zero]

/-! ## 2. 单位 × 单位杯积为零 ⟹ `residueSpan = ⊥` -/

/-- ★★★★★ **单位 × 单位杯积为零 ⟹ `residueSpan = ⊥`**（`muNRep` 载体）。

`residueSpan` 由 `{cup y z}_{y,z ∈ ker v̄}` 张成；由 §1 每个生成元都可写成
`cup (u) (w)`（`u, w` 为真正的单位）⟹ 假设使其全部为零 ⟹ 张成塌为 `⊥`。 -/
theorem residueSpan_eq_bot_of_units {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F))
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (hUU : ∀ u w : Fˣ, v u = 1 → v w = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hp u) (ClassFieldTheory.kummerClass F hp w) = 0) :
    residueSpan ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hp) = ⊥ := by
  rw [eq_bot_iff, residueSpan, Submodule.span_le]
  rintro _ ⟨⟨y, z⟩, rfl⟩
  obtain ⟨u, hu, hyu⟩ := exists_unit_of_valH1Gen_eq_zero (p := p) v hp hπ (y := (y : _)) y.2
  obtain ⟨w, hw, hzw⟩ := exists_unit_of_valH1Gen_eq_zero (p := p) v hp hπ (y := (z : _)) z.2
  have hgoal : ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (y : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat)
      (z : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat) = 0 := by
    rw [hyu, hzw]
    exact hUU u w hu hw
  simpa using hgoal

/-! ## 3. ★ 块 3：`u ∈ normGroup F L ⟹ (u)∪(w) = 0`（**类无关**！） -/

/-- ★★★★★ **单位 × 单位杯积为零的 `normGroup` 判据**（`Lua` 侧）。

直接实例化 `TauCeti.ClassFieldTheory.cup_kummerClass_eq_zero_iff_mem_normGroup`，其上下文
**只有 `[Field F]`** —— 无 `IsNonarchimedeanLocalField`、无 `ValuativeRel`、无完备性。

⟹ (R2) 的精确残余 = **纯代数陈述**「单位 `u` 是 Kummer 扩张 `F(w^{1/p})/F` 的范数」。 -/
theorem cup_kummerClass_unit_eq_zero_of_norm {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : F)) {u w : Fˣ}
    {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] {s : L}
    (hs : s ^ p = algebraMap F L ((w : Fˣ) : F))
    (hgen : IntermediateField.adjoin F ({s} : Set L) = ⊤)
    (hnorm : u ∈ normGroup F L) :
    ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (ClassFieldTheory.kummerClass F hp u) (ClassFieldTheory.kummerClass F hp w) = 0 :=
  (ClassFieldTheory.cup_kummerClass_eq_zero_iff_mem_normGroup (hζ := hζ) (hn := hp) u w hs
    hgen).mpr hnorm

/-- ★★★★★ **合成版**：范数条件 ⟹ `residueSpan = ⊥`。

`L`／`s` 作为**数据**给出（每个单位 `w` 配一个 Kummer 模型 `L w ∋ s w`，`s w ^ p = w`，
`F⟮s w⟯ = ⊤`），假设 `hnorm`：每个单位 `u` 在 `L w` 中都是范数。 -/
theorem residueSpan_eq_bot_of_norm {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F))
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (L : Fˣ → Type) [∀ w, Field (L w)] [∀ w, Algebra F (L w)]
    [∀ w, FiniteDimensional F (L w)]
    (s : ∀ w, L w)
    (hs : ∀ w, v w = 1 → (s w) ^ p = algebraMap F (L w) ((w : Fˣ) : F))
    (hgen : ∀ w, v w = 1 → IntermediateField.adjoin F ({s w} : Set (L w)) = ⊤)
    (hnorm : ∀ u w : Fˣ, v u = 1 → v w = 1 → u ∈ normGroup F (L w)) :
    residueSpan ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hp) = ⊥ :=
  residueSpan_eq_bot_of_units (p := p) hζ v hp hπ
    (fun u w hu hw =>
      cup_kummerClass_unit_eq_zero_of_norm (p := p) hζ hp (hs w hw) (hgen w hw) (hnorm u w hu hw))

/-! ## 4. 非空性见证（`L1`／`L10①`） -/

/-- **非空见证**：若 `H²` 是 subsingleton（例如 `cd_p(G_F) ≤ 1` 时，见
`Hyp284.h2_eq_zero_of_cd_le_one`），则单位 × 单位杯积假设**成立**。
⟹ 该假设类**非空**，不是空洞条件。 -/
theorem unitsCupVanish_of_subsingleton {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : F)) [Subsingleton
      ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat] :
    ∀ u w : Fˣ, (1 : Multiplicative ℤ) = 1 → (1 : Multiplicative ℤ) = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hp u) (ClassFieldTheory.kummerClass F hp w) = 0 :=
  fun _ _ _ _ => Subsingleton.elim _ _

/-! ## 5. 收口：`TameResidueFacts` 与 `∃ D` -/

/-- ★★★★★ **`TameResidueFacts` 只剩「单位 × 单位杯积为零」一条**（`muNRep` 载体，一般 Hensel）。

(R1) 由 `Hyp287.residuePhi_injective_muNRep` 供给（本定理把它作为输入以便在无 Hensel
假设时可单独调用）；(R2) 由 §2。 -/
theorem tameResidueFacts_of_units_cup {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F))
    {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (hUU : ∀ u w : Fˣ, v u = 1 → v w = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hp u) (ClassFieldTheory.kummerClass F hp w) = 0)
    (hR1 : Function.Injective (residuePhi ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hp) (ClassFieldTheory.kummerClass F hp π))) :
    TameResidueFacts ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hp) (ClassFieldTheory.kummerClass F hp π) :=
  tameResidueFacts_of_span_eq_bot
    (residueSpan_eq_bot_of_units (p := p) hζ v hp hπ hUU) hR1

variable [ValuativeRel F] [TopologicalSpace F]

/-- ★★★★★ **一般 Hensel 的 `D` 存在 —— 唯一残余 = 单位 × 单位杯积为零**。

与 `Hyp287.exists_henselResidueData_of_norm_form` 相比，**`hdecomp` 从假设变为结论**
（由 `hUU` 推出 `residueSpan = ⊥` ⟹ `≤ range f` 对任意 `f` 平凡成立）。

剩余输入：
* 论文 Hensel 层级的常规假设（`Irreducible`／`Module.Finite`／`HenselianRing`）；
* `hbridge`（`∅-bridge`，载体身份）；
* **`hUU`：单位 × 单位杯积为零** —— 由 §3 机检等价于「单位是范数」这一纯代数陈述。 -/
theorem exists_henselResidueData_of_units_cup {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hskew : ∀ x y, ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) x y
      = -(((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) y x))
    (hUU : ∀ u w : Fˣ, v u = 1 → v w = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hpF u) (ClassFieldTheory.kummerClass F hpF w) = 0) :
    ∃ D : HenselResidueData (ZMod p)
        ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat
        ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat
        ↥(LinearMap.ker (valH1LinearGen (p := p) v hpF))
        ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1),
      D.val = valH1LinearGen (p := p) v hpF :=
  (generalHensel_reduction (p := p) v hpF hζ hπ hskew).mpr
    (tameResidueFacts_of_units_cup (p := p) hζ v hpF hπ hUU
      (residuePhi_injective_muNRep (F := F) (p := p) (v := v) (π := π) hp hpF hζ hbridge hv hπ hp2))

/-! ## 6. 运回 `GaloBase` 载体（第 4 章用） -/

/-- ★★★★★ **`residueSpan = ⊥` 从 `muNRep` 载体运回 `GaloBase` 载体**。

`redEquiv` 把 `GaloBase` 的 residue 张成**送进** `muNRep` 的（`redEquiv_cup` ＋
`valH1LinearGen_redEquiv1` 保证 `redEquiv1` 保持 `ker v̄`），而 `redEquiv` 单射
⟹ 后者塌为 `⊥` 时前者也塌。 -/
theorem residueSpan_Galo_eq_bot_of_muNRep {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {v : Fˣ →* Multiplicative ℤ} (hpF : IsUnit (p : F))
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hspan : residueSpan ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hpF) = ⊥) :
    residueSpan (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) = ⊥ := by
  rw [eq_bot_iff, residueSpan, Submodule.span_le]
  rintro _ ⟨⟨y, z⟩, rfl⟩
  have h1 : valH1LinearGen (p := p) v hpF (H2Bridge.redEquiv1 hζ (y : GaloBase.V F p)) = 0 := by
    rw [valH1LinearGen_redEquiv1 (F := F) (p := p) hζ v hpF hbridge (y : GaloBase.V F p)]
    exact y.2
  have h2 : valH1LinearGen (p := p) v hpF (H2Bridge.redEquiv1 hζ (z : GaloBase.V F p)) = 0 := by
    rw [valH1LinearGen_redEquiv1 (F := F) (p := p) hζ v hpF hbridge (z : GaloBase.V F p)]
    exact z.2
  have hzero : GaloBase.cup (K := F) (p := p)
      (y : GaloBase.V F p) (z : GaloBase.V F p) = 0 := by
    refine (H2Bridge.redEquiv hζ).injective ?_
    rw [map_zero, H2Bridge.redEquiv_cup]
    have hmem := cup_mem_residueSpan ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hpF)
      (⟨H2Bridge.redEquiv1 hζ (y : GaloBase.V F p), by rw [LinearMap.mem_ker]; exact h1⟩ :
        ↥(LinearMap.ker (valH1LinearGen (p := p) v hpF)))
      (⟨H2Bridge.redEquiv1 hζ (z : GaloBase.V F p), by rw [LinearMap.mem_ker]; exact h2⟩ :
        ↥(LinearMap.ker (valH1LinearGen (p := p) v hpF)))
    rw [hspan, Submodule.mem_bot] at hmem
    exact hmem
  simpa using hzero

/-- ★★★★★ **第 4 章四条定理只剩一条**：单位 × 单位杯积为零 ⟹ `GaloBase` 载体的
`TameResidueFacts` ⟹ `Hyp162` 的 `orth_eq_bot_of_discrete_valuation`／
`thm_ramified_1_of_discrete_valuation`／`corollary_4_4_of_discrete_valuation` 的 `hfacts` 可消去。 -/
theorem tameResidueFacts_Galo_of_units_cup {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hUU : ∀ u w : Fˣ, v u = 1 → v w = 1 →
      ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
        (ClassFieldTheory.kummerClass F hpF u) (ClassFieldTheory.kummerClass F hpF w) = 0) :
    TameResidueFacts (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) (KummerBridge.kummerClass F p hpF π) :=
  tameResidueFacts_Galo_of_span_eq_bot (F := F) (p := p) (v := v) (π := π)
    hp hpF hζ hbridge hv hπ hp2
    (residueSpan_Galo_eq_bot_of_muNRep (p := p) hζ hpF hbridge
      (residueSpan_eq_bot_of_units (p := p) hζ v hpF hπ hUU))

end L20261018

#print axioms L20261018.exists_unit_of_valH1Gen_eq_zero
#print axioms L20261018.residueSpan_eq_bot_of_units
#print axioms L20261018.cup_kummerClass_unit_eq_zero_of_norm
#print axioms L20261018.residueSpan_eq_bot_of_norm
#print axioms L20261018.unitsCupVanish_of_subsingleton
#print axioms L20261018.tameResidueFacts_of_units_cup
#print axioms L20261018.exists_henselResidueData_of_units_cup
#print axioms L20261018.residueSpan_Galo_eq_bot_of_muNRep
#print axioms L20261018.tameResidueFacts_Galo_of_units_cup
