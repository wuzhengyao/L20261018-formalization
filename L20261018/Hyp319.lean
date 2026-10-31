import Hyp320
import Hyp288

/-!
# R1223–R1225（S34）：**(R1-σ) 与 (R1) 去掉 `hbridge`／完备性**

## 起点（`L47`：库内已有优先于自建）

`Hyp223`（R1092）早已机检 `(T1)`，`Hyp207` 已把它接成 `(R1-σ)`，`Hyp207` 的
`residuePhi_injective_of_bridgeKc` 已把 `(T1)` 接成 `(R1)`。三者都**不需要完备性**
（只是 section 变量带上了 `[IsNonarchimedeanLocalField F]`）。`Hyp320` 已把 `(T1)` 搬到
`[ValuativeRel F] [TopologicalSpace F]` 层级 ⟹ 本轮把下游三件也搬下来，并**换掉 `hbridge`**。

## 本轮

| 声明 | 内容 |
|---|---|
| `scaled_bridge_uncond` | ★ **(R1-σ)**：`∃ c ≠ 0, redEquiv1 (kc a) = c • kc_T a` |
| `valH1LinearGen_redEquiv1_smul` | ★ `v̄_muNRep ∘ redEquiv1 = c • v̄_Galo` |
| `valLinOf_eq_zero_iff` | `v̄_Galo x = 0 ↔ v̄_muNRep (redEquiv1 x) = 0`（核对应） |
| **`residuePhi_injective_t1`** | ★ **(R1)（`GaloBase` 载体，无 `hbridge`、无完备性）** |
| **`residuePhi_injective_muNRep'`** | ★ **(R1)（`muNRep` 载体，无 `hbridge`）** |
| **`residueSpan_Galo_eq_bot_of_muNRep'`** | ★ (R2) 的载体运输（无 `hbridge`） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section ScaledBridge

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

/-- ★ **(R1-σ) 无条件**（任意 `hpF`）：`redEquiv1` 把战役侧的 Kummer 类送到 `muNRep` 侧，
只差一个非零标量。这是 `Hyp316.scaled_bridge_of_hTheta` 的**无需 `hΘ`** 版本。 -/
theorem scaled_bridge_uncond (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p) :
    ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ,
      H2Bridge.redEquiv1 (p := p) (K := F) hζ (KummerBridge.kummerClass F p hpF a)
        = c • ClassFieldTheory.kummerClass F hpF a :=
  scaled_bridge_of_bridgeKc (F := F) (p := p) hζ
    (t1_closed' (F := F) (p := p) hpF hζ)

end ScaledBridge

section ValCompat

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

/-- ★★★★★ **`v̄` 在两载体下差一个标量**：`valH1LinearGen v hp (redEquiv1 x) = c • valLinOf v hp x`。 -/
theorem valH1LinearGen_redEquiv1_smul (hζ : IsPrimitiveRoot ζ p)
    (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) (c : ZMod p)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hp a)
      = c • ClassFieldTheory.kummerClass F hp a)
    (x : GaloBase.V F p) :
    valH1LinearGen (p := p) v hp (H2Bridge.redEquiv1 hζ x)
      = c • valLinOf (F := F) (p := p) v hp x := by
  obtain ⟨a, rfl⟩ := KummerV.kummerClass_surjective (F := F) (p := p) hp x
  rw [hbridge a, LinearMap.map_smul, valLinOf_kummerClass, valOfUnitOf]
  show c • valH1Gen (p := p) v hp (ClassFieldTheory.kummerClass F hp a)
    = c • ((Multiplicative.toAdd (v a) : ℤ) : ZMod p)
  rw [valH1Gen_kummerClass]

/-- ★★ **核对应**：`(R1-σ)` 保 `ker v̄`（标量非零 ⟹ 不改变零点）。 -/
theorem valLinOf_eq_zero_iff (hζ : IsPrimitiveRoot ζ p)
    (v : Fˣ →* Multiplicative ℤ) (hp : IsUnit (p : F)) (c : ZMod p) (hc : c ≠ 0)
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hp a)
      = c • ClassFieldTheory.kummerClass F hp a)
    (x : GaloBase.V F p) :
    valH1LinearGen (p := p) v hp (H2Bridge.redEquiv1 hζ x) = 0
      ↔ valLinOf (F := F) (p := p) v hp x = 0 := by
  rw [valH1LinearGen_redEquiv1_smul (F := F) (p := p) hζ v hp c hbridge x, smul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hc
    · exact h
  · intro h
    exact Or.inr h

end ValCompat

section R1

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ} {ζ : F}

/-- ★★★★★ **(R1) 在 `GaloBase` 载体上，无 `hbridge`、无完备性**：
`residuePhi (∪, v̄, (π))` 单射。

`Hyp223.residuePhi_injective_of_t1` 的**无完备性**版：把 `(T1)` 换成 `Hyp320.t1_closed_of_hζ'`。 -/
theorem residuePhi_injective_t1
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hζ : IsPrimitiveRoot ζ p)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Function.Injective (residuePhi (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit)
      (KummerBridge.kummerClass F p hζ.neZero'.out.isUnit π)) :=
  residuePhi_injective_of_bridgeKc (F := F) (p := p) hp hζ
    (t1_closed_of_hζ' (F := F) (p := p) hζ) hv hπ hp2

/-- ★★★★★ **(R1) 在 `muNRep` 载体上，无 `hbridge`**：

`Hyp287.residuePhi_injective_muNRep` 里 `hbridge` 只被用在两处 ——
核对应（`valLinOf_eq_zero_iff`）与交换方块（`redEquiv_cup` ＋ **(R1-σ)**）。
两者现在都无需假设 ⟹ `hbridge` 消去。 -/
theorem residuePhi_injective_muNRep'
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Function.Injective (residuePhi ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hpF) (ClassFieldTheory.kummerClass F hpF π)) := by
  obtain ⟨c, hc0, hsc⟩ := scaled_bridge_uncond (F := F) (p := p) hpF hζ
  have hpp : hpF = hζ.neZero'.out.isUnit := Subsingleton.elim _ _
  subst hpp
  have hR1G := residuePhi_injective_t1 (F := F) (p := p) (v := v) (π := π) hp hζ hv hπ hp2
  intro y z hyz
  -- `e := redEquiv1`：`y = e x_y`，`x_y ∈ ker v̄`
  have hxker : ∀ t : ↥(LinearMap.ker (valH1LinearGen (p := p) v hζ.neZero'.out.isUnit)),
      valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit
        ((H2Bridge.redEquiv1 hζ).symm (t : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat)) = 0 := by
    intro t
    have h1 : valH1LinearGen (p := p) v hζ.neZero'.out.isUnit
        (H2Bridge.redEquiv1 hζ ((H2Bridge.redEquiv1 hζ).symm (t : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat))) = 0 := by
      rw [AddEquiv.apply_symm_apply]
      exact t.2
    exact ((valLinOf_eq_zero_iff (F := F) (p := p) hζ v hζ.neZero'.out.isUnit c hc0 hsc _).mp h1)
  -- 关键的交换：`e (Φ_Galo x) = c • Φ_muNRep (e x)`
  have hsq : ∀ t : ↥(LinearMap.ker (valH1LinearGen (p := p) v hζ.neZero'.out.isUnit)),
      H2Bridge.redEquiv hζ
        (residuePhi (GaloBase.cup (K := F) (p := p))
          (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit)
          (KummerBridge.kummerClass F p hζ.neZero'.out.isUnit π)
          ⟨(H2Bridge.redEquiv1 hζ).symm (t : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat), hxker t⟩)
      = c • residuePhi ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
          (valH1LinearGen (p := p) v hζ.neZero'.out.isUnit)
          (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit π) t := by
    intro t
    show H2Bridge.redEquiv hζ
        (((GaloBase.cup (K := F) (p := p))
          ((H2Bridge.redEquiv1 hζ).symm (t : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat)))
          (KummerBridge.kummerClass F p hζ.neZero'.out.isUnit π))
      = c • (((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) (t : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat))
          (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit π)
    rw [H2Bridge.redEquiv_cup]
    rw [AddEquiv.apply_symm_apply, hsc π, map_smul]
  -- 由 `Φ_muNRep y = Φ_muNRep z` 得 `e (Φ_Galo x_y) = e (Φ_Galo x_z)`
  have hy := hsq y
  have hz := hsq z
  have hkey : H2Bridge.redEquiv hζ
      (residuePhi (GaloBase.cup (K := F) (p := p))
        (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit)
        (KummerBridge.kummerClass F p hζ.neZero'.out.isUnit π)
        ⟨(H2Bridge.redEquiv1 hζ).symm (y : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat), hxker y⟩)
      = H2Bridge.redEquiv hζ
        (residuePhi (GaloBase.cup (K := F) (p := p))
          (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit)
          (KummerBridge.kummerClass F p hζ.neZero'.out.isUnit π)
          ⟨(H2Bridge.redEquiv1 hζ).symm (z : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat), hxker z⟩) := by
    rw [hy, hz, hyz]
  have hxeq : (⟨(H2Bridge.redEquiv1 hζ).symm (y : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat), hxker y⟩ :
      ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit)))
      = ⟨(H2Bridge.redEquiv1 hζ).symm (z : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat), hxker z⟩ :=
    hR1G ((H2Bridge.redEquiv hζ).injective hkey)
  have : (y : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat) = (z : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat) := by
    have h2 := congrArg (fun t => (H2Bridge.redEquiv1 hζ)
      ((t : ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit))) :
        GaloBase.V F p)) hxeq
    simpa using h2
  exact Subtype.ext this

/-- ★★★★★ **`residueSpan = ⊥` 从 `muNRep` 载体运回 `GaloBase` 载体**（无 `hbridge`）：

`Hyp288.residueSpan_Galo_eq_bot_of_muNRep` 的 `hbridge` 只用于「`redEquiv1` 保 `ker v̄`」，
现由 `valLinOf_eq_zero_iff` 供给。 -/
theorem residueSpan_Galo_eq_bot_of_muNRep'
    (hζ : IsPrimitiveRoot ζ p) (hpF : IsUnit (p : F))
    (hspan : residueSpan ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (valH1LinearGen (p := p) v hpF) = ⊥) :
    residueSpan (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) = ⊥ := by
  obtain ⟨c, hc0, hsc⟩ := scaled_bridge_uncond (F := F) (p := p) hpF hζ
  rw [eq_bot_iff, residueSpan, Submodule.span_le]
  rintro _ ⟨⟨y, z⟩, rfl⟩
  have h1 : valH1LinearGen (p := p) v hpF (H2Bridge.redEquiv1 hζ (y : GaloBase.V F p)) = 0 :=
    (valLinOf_eq_zero_iff (F := F) (p := p) hζ v hpF c hc0 hsc _).mpr y.2
  have h2 : valH1LinearGen (p := p) v hpF (H2Bridge.redEquiv1 hζ (z : GaloBase.V F p)) = 0 :=
    (valLinOf_eq_zero_iff (F := F) (p := p) hζ v hpF c hc0 hsc _).mpr z.2
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

end R1

end L20261018

#print axioms L20261018.scaled_bridge_uncond
#print axioms L20261018.valH1LinearGen_redEquiv1_smul
#print axioms L20261018.valLinOf_eq_zero_iff
#print axioms L20261018.residuePhi_injective_t1
#print axioms L20261018.residuePhi_injective_muNRep'
#print axioms L20261018.residueSpan_Galo_eq_bot_of_muNRep'
