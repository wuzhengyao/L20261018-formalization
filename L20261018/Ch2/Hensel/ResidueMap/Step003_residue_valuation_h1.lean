import L20261018.Ch2.Hensel.ResidueMap.Step002_unit_reduction_principal_units
import L20261018.Ch3.BiKummer.Step011_restriction_kernel_eq_u

/-!
# R942：`prop:prelim-kummer-valuation`(2) 的第一字段 —— `\bar v : H¹(F,μ_p) → F_p`

论文 `raw/L20261018.tex:1005`（`label:prop:prelim-kummer-valuation`）(2) 要求分裂正合列

$$0\longrightarrow H^1(K,\mu_p)\xrightarrow{\mathrm{inf}}H^1(F,\mu_p)
\xrightarrow{\bar v}\Fp\longrightarrow0,\qquad \bar v=v\bmod p .$$

**本文件造出其中的 `\bar v`**（在论文的载体 `GaloBase.V F p = H¹(G_F, μ_p)` 上），
并机检它的两条决定性性质：

* `valLin_kummerClass`：`\bar v((a)) = v(a) mod p`（逐字就是论文的 `\bar v = v \bmod p`）；
* `valLin_pi`：`v(\pi)=1 ⟹ \bar v((\pi)) = 1`（正合列右端满射的见证）。

## 构造要点（不需要任何上同调新件）

1. `v(a) mod p` 只依赖**Kummer 类** `(a) = kummerClass a`：若 `(a) = (b)`，则 `a/b ∈ F^{×p}`
   （`kummerClass_eq_zero_iff` ＋ `kummerClass_mul`／`_inv`），故 `v(a/b) = p\cdot v(z)` ⟹ `v(a)\equiv v(b) \pmod p`；
2. `kummerClass` 满射（`Hyp36.kummerClass_surjective`）⟹ 用 `Classical.choose` 把 `v(\cdot) \bmod p`
   沿满射下降到整个 `V` 上；
3. 加性用 `kummerClass_mul`（`(ab) = (a)+(b)`）＋ `v` 的乘性；
4. `ZMod p`-线性用 `AddMonoidHom.toZModLinearMap`（**任何加法同态**自动是 `ZMod p`-线性）。

⟹ 这一格**完全不需要 `∂₂`**，也不需要用「`H¹(I,μ_p)` 的 1 维性」那个未决探针。
-/

set_option maxHeartbeats 2000000

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace L20261018

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- `v(a) mod p`（整数轴上的取值，未下降到 `V` 上）。 -/
noncomputable def valOfUnit (a : Fˣ) : ZMod p :=
  ((Multiplicative.toAdd (TauCeti.normalizedValuation F a) : ℤ) : ZMod p)

lemma toAdd_mul' (a b : Multiplicative ℤ) :
    Multiplicative.toAdd (a * b) = Multiplicative.toAdd a + Multiplicative.toAdd b := rfl

lemma toAdd_pow' (a : Multiplicative ℤ) (n : ℕ) :
    Multiplicative.toAdd (a ^ n) = (n : ℤ) * Multiplicative.toAdd a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, toAdd_mul', ih, Nat.cast_succ, add_mul, one_mul]

lemma valOfUnit_mul (a b : Fˣ) : valOfUnit F p (a * b) = valOfUnit F p a + valOfUnit F p b := by
  rw [valOfUnit, valOfUnit, valOfUnit, map_mul, toAdd_mul']
  push_cast
  ring

lemma valOfUnit_one : valOfUnit F p 1 = 0 := by
  simp [valOfUnit]

/-- **`v(a) ≡ v(b) (mod p)` 当 `(a) = (b)`**：引理把 `a/b` 写成 `p` 次幂。 -/
theorem valOfUnit_eq_of_kummerClass_eq (hp : IsUnit (p : F)) {a b : Fˣ}
    (h : KummerBridge.kummerClass F p hp a = KummerBridge.kummerClass F p hp b) :
    valOfUnit F p a = valOfUnit F p b := by
  -- `(a·b⁻¹) = (a) - (b) = 0`
  have hd : KummerBridge.kummerClass F p hp (a * b⁻¹) = 0 := by
    rw [KummerV.kummerClass_mul (F := F) (p := p) hp,
      KummerV.kummerClass_inv (F := F) (p := p) hp, h, add_neg_cancel]
  rw [KummerBridge.kummerClass_eq_zero_iff (F := F) (p := p) hp] at hd
  obtain ⟨z, hz⟩ := hd
  -- `v(a·b⁻¹) = v(z^p) = p · v(z)`
  have hv : Multiplicative.toAdd (TauCeti.normalizedValuation F (a * b⁻¹))
      = (p : ℤ) * Multiplicative.toAdd (TauCeti.normalizedValuation F z) := by
    rw [← hz, show (powMonoidHom p : Fˣ →* Fˣ) z = z ^ p from rfl, map_pow, toAdd_pow']
  -- `v(a) = v(b) + p·v(z)`
  have hsplit : Multiplicative.toAdd (TauCeti.normalizedValuation F a)
      = Multiplicative.toAdd (TauCeti.normalizedValuation F b)
        + (p : ℤ) * Multiplicative.toAdd (TauCeti.normalizedValuation F z) := by
    have h1 : TauCeti.normalizedValuation F a
        = TauCeti.normalizedValuation F (a * b⁻¹) * TauCeti.normalizedValuation F b := by
      rw [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [h1, toAdd_mul', hv]
    ring_nf
  rw [valOfUnit, valOfUnit, hsplit]
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero]

/-- **`\bar v = v \bmod p` 在论文载体上的实现**：`V = H¹(G_F, μ_p) → F_p`，加法同态。 -/
noncomputable def valAddHom (hp : IsUnit (p : F)) : GaloBase.V F p →+ ZMod p where
  toFun x := valOfUnit F p (Classical.choose (KummerV.kummerClass_surjective (F := F) (p := p) hp x))
  map_zero' := by
    have h0 : KummerBridge.kummerClass F p hp
        (Classical.choose (KummerV.kummerClass_surjective (F := F) (p := p) hp 0)) = 0 :=
      Classical.choose_spec (KummerV.kummerClass_surjective (F := F) (p := p) hp 0)
    have h1 : KummerBridge.kummerClass F p hp
        (Classical.choose (KummerV.kummerClass_surjective (F := F) (p := p) hp 0))
        = KummerBridge.kummerClass F p hp 1 := by
      rw [h0]
      exact ((KummerBridge.kummerClass_eq_zero_iff (F := F) (p := p) hp 1).mpr (one_mem _)).symm
    rw [valOfUnit_eq_of_kummerClass_eq (F := F) (p := p) hp h1]
    exact valOfUnit_one F p
  map_add' x y := by
    set ax := Classical.choose (KummerV.kummerClass_surjective (F := F) (p := p) hp x) with hax
    set ay := Classical.choose (KummerV.kummerClass_surjective (F := F) (p := p) hp y) with hay
    have hx : KummerBridge.kummerClass F p hp ax = x :=
      Classical.choose_spec (KummerV.kummerClass_surjective (F := F) (p := p) hp x)
    have hy : KummerBridge.kummerClass F p hp ay = y :=
      Classical.choose_spec (KummerV.kummerClass_surjective (F := F) (p := p) hp y)
    have hkey : KummerBridge.kummerClass F p hp
        (Classical.choose (KummerV.kummerClass_surjective (F := F) (p := p) hp (x + y)))
        = KummerBridge.kummerClass F p hp (ax * ay) := by
      rw [Classical.choose_spec (KummerV.kummerClass_surjective (F := F) (p := p) hp (x + y)),
        KummerV.kummerClass_mul (F := F) (p := p) hp, hx, hy]
    rw [valOfUnit_eq_of_kummerClass_eq (F := F) (p := p) hp hkey]
    exact valOfUnit_mul F p ax ay

/-- **`\bar v : H¹(F,μ_p) → F_p`**（`ZMod p`-线性）。 -/
noncomputable def valLin (hp : IsUnit (p : F)) :
    GaloBase.V F p →ₗ[ZMod p] ZMod p :=
  (valAddHom F p hp).toZModLinearMap p

/-- **`\bar v((a)) = v(a) mod p`** —— 论文的「`\bar v = v \bmod p`」在 Kummer 类上逐字成立。 -/
-- @source file=raw/L20261018.tex locator=label:prop:prelim-kummer-valuation quote="\xrightarrow{\bar v}\Fp\longrightarrow0,\bar v=v\bmod p,"
theorem valLin_kummerClass (hp : IsUnit (p : F)) (a : Fˣ) :
    valLin F p hp (KummerBridge.kummerClass F p hp a) = valOfUnit F p a := by
  have : valLin F p hp (KummerBridge.kummerClass F p hp a) = valAddHom F p hp (KummerBridge.kummerClass F p hp a) := rfl
  rw [this]
  exact valOfUnit_eq_of_kummerClass_eq (F := F) (p := p) hp
    (Classical.choose_spec (KummerV.kummerClass_surjective (F := F) (p := p) hp
      (KummerBridge.kummerClass F p hp a)))

/-- **正合列右端满射的见证**：`v(\pi) = 1 ⟹ \bar v((\pi)) = 1`。 -/
theorem valLin_pi (hp : IsUnit (p : F)) {π : Fˣ}
    (hπ : TauCeti.normalizedValuation F π = Multiplicative.ofAdd (1 : ℤ)) :
    valLin F p hp (KummerBridge.kummerClass F p hp π) = 1 := by
  rw [valLin_kummerClass]
  rw [valOfUnit, hπ]
  simp

end L20261018

#print axioms L20261018.valOfUnit_eq_of_kummerClass_eq
#print axioms L20261018.valLin_kummerClass
#print axioms L20261018.valLin_pi
