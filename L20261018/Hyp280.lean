import L20261018.Hyp279

/-!
# R1156（**第 5 项第二块：`D` 初等块的剩余字段 —— `infl`／`pi`／`split`，仍零完备性**）

## 本轮做什么

`Hyp279` 给了初等块的 `val`（`valH1Gen`，类无关）。本轮补齐其余初等字段并**打包**：

| 字段 | 构造（全部类无关） |
|---|---|
| `VK` | `ker v̄ = ↥(LinearMap.ker (valH1Gen …))` |
| `infl` | 子模包含 `VK ↪ V` |
| `inj_infl`／`val_infl` | 子模包含的单射性／`ker` 的定义 |
| `pi` | `kummerClass F hp π` |
| `val_pi` | `Hyp279.valH1Gen_kummerClass_pi` |
| **`split`** | ★ `x = kummerClass a`（库内 `kummerClass_surjective`）；取 `n := toAdd (v a)`、`w := a * π^(-n)`（则 `v(w) = 1` 故 `kummerClass w ∈ ker v̄`）；由库内 `kummerClass_mul`／`kummerClass_zpow` 得 `x = (w) + n•(π)`；再用 `(n : ZMod p) • (π) = n • (π)`（`Int.cast_smul_eq_zsmul`） |

## 判据

本文件**不得出现** `IsNonarchimedeanLocalField` —— 只允许 `[Field F]`、`v : Fˣ →* Multiplicative ℤ`、
`π` 与 `IsUnit (p : F)`（后者由库内 `kummerEquiv` 需要）。

## 本轮

| 声明 | 内容 |
|---|---|
| `ofAdd_one_zpow_gen` | `(ofAdd 1)^k = ofAdd k`（本地重证，避免跨支 import） |
| **`val_mul_uniformizer_zpow`** | `v(a · π^{-n}) = 1`（`n = toAdd (v a)`） |
| **`kummerClass_split_gen`** | ★★★ `x = (a · π^{-n}) 的类 + n•(π)` |
| **`exists_elementary_henselData`** | ★★★★★ **`D` 的初等七字段在一般 Hensel（无完备性）情形存在** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {F : Type} [Field F] {p : ℕ} [NeZero p]

/-- `(ofAdd 1 : Multiplicative ℤ)^k = ofAdd k`。 -/
theorem ofAdd_one_zpow_gen (k : ℤ) :
    (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) ^ k = Multiplicative.ofAdd k := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, ih]; simp
  | pred n ih => rw [zpow_sub_one, ih]; simp; rw [div_eq_mul_inv]

/-- ★★★ **单位/一致化元分解**：`v(a · π^{-n}) = 1`，其中 `n = toAdd (v a)`（即 `a·π^{-n}` 是单位）。 -/
theorem val_mul_uniformizer_zpow (v : Fˣ →* Multiplicative ℤ) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (a : Fˣ) :
    v (a * π ^ (-(Multiplicative.toAdd (v a)))) = 1 := by
  rw [map_mul, map_zpow, hπ, ofAdd_one_zpow_gen]
  rw [show v a = Multiplicative.ofAdd (Multiplicative.toAdd (v a)) from rfl, ← ofAdd_add]
  simp

/-- ★★★ **`split`（类无关）**：每个 `H¹` 类 = 单位类 ＋ `n•(π)`。 -/
theorem kummerClass_split_gen (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (x : ↑(continuousCohomology 1 (TauCeti.ClassFieldTheory.muNRep p F)).toModuleCat) :
    ∃ (x₀ : ↑(continuousCohomology 1 (TauCeti.ClassFieldTheory.muNRep p F)).toModuleCat)
      (m : ZMod p),
      valH1Gen (p := p) v hp x₀ = 0 ∧
        x = x₀ + m • TauCeti.ClassFieldTheory.kummerClass F hp π := by
  obtain ⟨a, rfl⟩ := TauCeti.ClassFieldTheory.kummerClass_surjective F hp x
  refine ⟨TauCeti.ClassFieldTheory.kummerClass F hp
    (a * π ^ (-(Multiplicative.toAdd (v a)))),
    ((Multiplicative.toAdd (v a) : ℤ) : ZMod p), ?_, ?_⟩
  · rw [valH1Gen_kummerClass, val_mul_uniformizer_zpow v hπ a]
    simp
  · rw [TauCeti.ClassFieldTheory.kummerClass_mul, TauCeti.ClassFieldTheory.kummerClass_zpow]
    rw [Int.cast_smul_eq_zsmul]
    have h1 : (-(Multiplicative.toAdd (v a))) • TauCeti.ClassFieldTheory.kummerClass F hp π
        = -(Multiplicative.toAdd (v a) • TauCeti.ClassFieldTheory.kummerClass F hp π) :=
      neg_smul _ _
    rw [h1]
    abel

/-- `valH1Gen` 的线性映射版（`AddMonoidHom.toZModLinearMap`）。 -/
noncomputable def valH1LinearGen (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) :
    ↑(continuousCohomology 1 (TauCeti.ClassFieldTheory.muNRep p F)).toModuleCat →ₗ[ZMod p] ZMod p :=
  AddMonoidHom.toZModLinearMap p (valH1Gen (p := p) v hp)

/-- ★★★★★ **`D` 的初等七字段在一般 Hensel（无完备性）情形成立**：

`VK := ker v̄`、`infl := 子模包含`、`pi := (π)`、`val := v̄`；
单射性／`val ∘ infl = 0`／`val π = 1`／`split` 全部机检。
**上下文只有 `[Field F]` ＋ `v : Fˣ →* Multiplicative ℤ` ＋ `IsUnit (p:F)`。** -/
theorem elementary_henselData (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) :
    Function.Injective (Submodule.subtype (LinearMap.ker (valH1LinearGen (p := p) v hp))) ∧
      (∀ y : ↥(LinearMap.ker (valH1LinearGen (p := p) v hp)),
        valH1LinearGen (p := p) v hp (Submodule.subtype _ y) = 0) ∧
      valH1LinearGen (p := p) v hp (TauCeti.ClassFieldTheory.kummerClass F hp π) = 1 ∧
      (∀ x : ↑(continuousCohomology 1 (TauCeti.ClassFieldTheory.muNRep p F)).toModuleCat,
        ∃ (x₀ : ↥(LinearMap.ker (valH1LinearGen (p := p) v hp))) (m : ZMod p),
          x = Submodule.subtype _ x₀ + m • TauCeti.ClassFieldTheory.kummerClass F hp π) := by
  refine ⟨Submodule.subtype_injective _, ?_, ?_, ?_⟩
  · intro y
    exact y.2
  · exact valH1Gen_kummerClass_pi v hp hπ
  · intro x
    obtain ⟨x₀, m, hx₀, hx⟩ := kummerClass_split_gen (p := p) v hp hπ x
    exact ⟨⟨x₀, by rw [LinearMap.mem_ker]; exact hx₀⟩, m, hx⟩

end L20261018

#print axioms L20261018.ofAdd_one_zpow_gen
#print axioms L20261018.val_mul_uniformizer_zpow
#print axioms L20261018.kummerClass_split_gen
#print axioms L20261018.valH1LinearGen
#print axioms L20261018.elementary_henselData
