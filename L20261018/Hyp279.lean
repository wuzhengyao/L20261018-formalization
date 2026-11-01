import L20261018.Hyp278

/-!
# R1155（**第 5 项第一块：一般 Hensel 情形下 `D` 的「初等块」—— 与完备性无关**）

## 本轮做什么

`CH4-COVERAGE-AUDIT.md` §3.5：我们的形式化落在 `IsNonarchimedeanLocalField`（＝离散 ＋ **完备**），
论文的一般 Hensel 情形未被覆盖。本轮开始把 `HenselResidueData`（＝`D`）的构造**逐块去完备**。

`HenselResidueData` 的 11 个字段分两类：

| 类 | 字段 | 需要什么 |
|---|---|---|
| **初等块**（本轮） | `val`／`infl`／`pi`／`split`（＋`inj_infl`／`val_infl`／`val_pi`） | 只需 `v : Fˣ →* Multiplicative ℤ`（**离散赋值，不用完备性**）＋ `π` ＋ `μ_p ⊂ F` ＋ Kummer 理论 |
| **剩余块**（下一块） | `res`／`tame_uu`／`tame_u_pi`／`tame_pi_u` | `prop:prelim-residue`，即 (R1) ＋ (R2)（GS `Construction 6.8.5`） |

**本轮机检的初等块**：赋值模 `p` 的下降（`v̄ : Fˣ → ZMod p`，杀死 `p` 次幂 ⟹ 经库内
`kummerEquiv` 搬到 `H¹(F, μ_p)`）＋ 「一致化元类的值 = 1」。**全部只用 `[Field F]`，无 `IsNonarchimedeanLocalField`。**

## 本轮

| 声明 | 内容 |
|---|---|
| `toAdd_pow_int` | `Multiplicative ℤ` 中 `toAdd` 的幂法则 |
| **`valMonoidGen`** | ★★★ **赋值模 `p`（类无关）**：`v : Fˣ →* Multiplicative ℤ` 的模 `p` 归约 |
| **`valMonoidGen_ker`** | 它杀死 `p` 次幂 ⟹ 可下降到幂类商 |
| `valQuotGen`／`valQuotGenAdd` | 幂类商上的赋值（乘法／加法形式） |
| **`valH1Gen`** | ★★★★ **`H¹(F, μ_p) →+ ZMod p`**（经库内 `kummerEquiv`，**无完备性**） |
| **`valH1Gen_kummerClass`** | `v̄ (kummerClass a) = v(a) mod p` |
| **`valH1Gen_kummerClass_pi`** | ★★★★ **`v(π) = 1 ⟹ v̄((π)) = 1`（`val_pi` 的类无关版）** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {F : Type} [Field F] {p : ℕ} [NeZero p]

/-- 在 `Multiplicative ℤ` 中 `toAdd` 的幂法则。 -/
theorem toAdd_pow_int (z : Multiplicative ℤ) (n : ℕ) :
    Multiplicative.toAdd (z ^ n) = n * Multiplicative.toAdd z := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, show Multiplicative.toAdd (z ^ k * z)
        = Multiplicative.toAdd (z ^ k) + Multiplicative.toAdd z from rfl, ih]
      push_cast
      ring

/-- ★★★ **赋值模 `p`（类无关）**：`v : Fˣ →* Multiplicative ℤ` 的模 `p` 归约。 -/
noncomputable def valMonoidGen (v : Fˣ →* Multiplicative ℤ) : Fˣ →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd ((v x).toAdd : ZMod p)
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul]
    show Multiplicative.ofAdd ((Multiplicative.toAdd (v x * v y) : ℤ) : ZMod p)
      = Multiplicative.ofAdd (((Multiplicative.toAdd (v x) : ℤ) : ZMod p))
        * Multiplicative.ofAdd (((Multiplicative.toAdd (v y) : ℤ) : ZMod p))
    rw [← ofAdd_add]
    congr 1
    have hmul : Multiplicative.toAdd (v x * v y)
        = Multiplicative.toAdd (v x) + Multiplicative.toAdd (v y) := by simp
    rw [hmul]
    push_cast
    ring

/-- 它杀死 `p` 次幂 ⟹ 可下降到幂类商。 -/
theorem valMonoidGen_ker (v : Fˣ →* Multiplicative ℤ) :
    (powMonoidHom p : Fˣ →* Fˣ).range ≤ (valMonoidGen (p := p) v).ker := by
  rintro x ⟨y, rfl⟩
  rw [MonoidHom.mem_ker]
  show Multiplicative.ofAdd ((Multiplicative.toAdd (v (y ^ p)) : ℤ) : ZMod p) = 1
  rw [map_pow, toAdd_pow_int]
  have hzero : (((p : ℤ) * Multiplicative.toAdd (v y) : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  rw [hzero]
  rfl

/-- 幂类商上的赋值模 `p`（类无关）。 -/
noncomputable def valQuotGen (v : Fˣ →* Multiplicative ℤ) :
    TauCeti.powerClassQuotient Fˣ p →* Multiplicative (ZMod p) :=
  QuotientGroup.lift _ (valMonoidGen (p := p) v) (valMonoidGen_ker v)

/-- 同上，加法同态形式。 -/
noncomputable def valQuotGenAdd (v : Fˣ →* Multiplicative ℤ) :
    Additive (TauCeti.powerClassQuotient Fˣ p) →+ ZMod p where
  toFun x := Multiplicative.toAdd (valQuotGen (p := p) v x.toMul)
  map_zero' := by simp
  map_add' x y := by
    show Multiplicative.toAdd (valQuotGen (p := p) v (x.toMul * y.toMul))
      = Multiplicative.toAdd (valQuotGen (p := p) v x.toMul)
        + Multiplicative.toAdd (valQuotGen (p := p) v y.toMul)
    rw [map_mul]
    rfl

/-- ★★★★ **`H¹(F, μ_p)` 上的赋值模 `p`（类无关）**：经库内 `kummerEquiv`
（`MuNRep.lean:270`，其 section 只需 `[Field F]`）把 `v̄` 搬到 `H¹`。 -/
noncomputable def valH1Gen (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) :
    ↑(continuousCohomology 1 (TauCeti.ClassFieldTheory.muNRep p F)).toModuleCat →+ ZMod p :=
  (valQuotGenAdd (p := p) v).comp (TauCeti.ClassFieldTheory.kummerEquiv F hp).symm.toAddMonoidHom

/-- `v̄` 在 Kummer 类上的值 = 赋值的模 `p`。 -/
theorem valH1Gen_kummerClass (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) (a : Fˣ) :
    valH1Gen (p := p) v hp (TauCeti.ClassFieldTheory.kummerClass F hp a)
      = ((v a).toAdd : ZMod p) := by
  have hsymm : (TauCeti.ClassFieldTheory.kummerEquiv F hp).symm
      (TauCeti.ClassFieldTheory.kummerClass F hp a)
        = Additive.ofMul (TauCeti.powerClassHom Fˣ p a) := by
    rw [← TauCeti.ClassFieldTheory.kummerEquiv_ofMul_mk F hp a]
    exact AddEquiv.symm_apply_apply _ _
  rw [valH1Gen, AddMonoidHom.comp_apply]
  show valQuotGenAdd (p := p) v ((TauCeti.ClassFieldTheory.kummerEquiv F hp).symm
      (TauCeti.ClassFieldTheory.kummerClass F hp a)) = _
  rw [hsymm]
  show Multiplicative.toAdd (valQuotGen (p := p) v (TauCeti.powerClassHom Fˣ p a)) = _
  rw [show valQuotGen (p := p) v (TauCeti.powerClassHom Fˣ p a) = valMonoidGen (p := p) v a from rfl]
  rfl

/-- ★★★★ **`val_pi` 的类无关版**：`v(π) = 1 ⟹ v̄((π)) = 1`。 -/
theorem valH1Gen_kummerClass_pi (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) :
    valH1Gen (p := p) v hp (TauCeti.ClassFieldTheory.kummerClass F hp π) = 1 := by
  rw [valH1Gen_kummerClass]
  have : (v π).toAdd = 1 := by rw [hπ]; rfl
  rw [this]
  simp

end L20261018

#print axioms L20261018.toAdd_pow_int
#print axioms L20261018.valMonoidGen
#print axioms L20261018.valMonoidGen_ker
#print axioms L20261018.valQuotGen
#print axioms L20261018.valQuotGenAdd
#print axioms L20261018.valH1Gen
#print axioms L20261018.valH1Gen_kummerClass
#print axioms L20261018.valH1Gen_kummerClass_pi
