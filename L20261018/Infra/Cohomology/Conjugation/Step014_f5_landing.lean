import L20261018.Infra.Cohomology.Conjugation.Step013_h_conj1_discharged

/-!
# S73 R4：★★★★ **`F5` 的落点**——膨胀的类无分歧 ⟹ `H1 (Γ⧸I, ℤ/p) → VKG` 到手（缺口 ② 的实质一步）

## 为什么这一步是对的（并修正 `PLAN-f5-assembly.md` 的旧判断）

旧判断（S72）：`F5` 需要一条「显式模型 ↔ TopRep」的桥，而那是 `D68`／`D69` 的禁走族。
**本轮实测推翻**：`D68`／`D69` 禁的是**造系数桥**（`TopRep.ofHom`／`ofDiscreteModulePair (R := ℤ)`
把 `ZMod p` 包成 `TopRep` 对象）；而**显式 `H1` 与 `GaloBase.V` 之间的桥早已机检**：

```
KummerBridge.h1ToVEquiv : H1 (AbsoluteGaloisGroup F) (ZMod p) ≃+ GaloBase.V F p
Hyp758.res1V_h1ToVEquiv  : res1V (h1ToVEquiv y) = explicitRes1 y
Hyp747.valLinOf_eq_zero_iff_res1V_eq_zero : v̄ y = 0 ↔ res₁ y = 0
TauCeti.ContCohomology.explicitRes1_explicitMap1_eq_zero_of_map_le  ← 「无分歧类拉回仍无分歧」
```

⟹ **`VKG = ker v̄` 的成员性可以完全在显式模型里判**：`I.map (Γ → Γ⧸I) ≤ ⊥`，故沿商映射拉回的类
在 `⊥` 上的限制为 `0`，于是膨胀后的类 `res₁ = 0`，故 `v̄ = 0`，即落在 `VKG`。

## 交付

| 声明 | 内容 |
|---|---|
| **`h1ToVEquiv_infl_valLinOf_eq_zero`** | ★★★★★ **膨胀的类无分歧**：`v̄ (h1ToVEquiv (infl c)) = 0` |
| **`inflToVKG`** | ★★★★★ **`H1 (Γ⧸I, ℤ/p) →ₗ[ℤ/p] VKG`**（膨胀 ⟹ 落在 `ker v̄`） |
| **`F5_uncond`** | ★★★★★ **`F5` 本体**：`H1 (Γ⧸I, H¹(I,ℤ/p)) →ₗ[ℤ/p] VKG`（＝ `inflToVKG ∘ coeffChangeEquiv_uncond`） |

**⟹ 缺口 ② 的组装完成**（`F5` **存在且线性**）。

⚠ **尚未机检的一步**：把 `Hyp757.hd_infl_of_linear` 作用到 `F5_uncond` 上，须先把它要的
`{v}`／`hv : ValCompat v`／`hπ : v π = ofAdd 1` 与 `TauCeti.normalizedValuation F` 对齐
（`Hyp747` 文件头：`ValCompat v` ＋ `v π = 1` 就刻画 `normalizedValuation`）——**下一轮的一行**。

## 诚实边界

* `F5_uncond` 仍带三条**技术实例**（`DiscreteTopology`／`IsTopologicalAddGroup`／`ContinuousSMul (Γ⧸I)`）；
  其中 `IsTopologicalAddGroup` 可自动合成，另两条**不可**（本轮实测：`DiscreteTopology` 超时、
  `ContinuousSMul` 合成失败）⟹ 仍按 `STARTUP` §3 登记为技术实例。
* 本件证明的是「`F5` 存在且线性」。`hd_cup_pi`（缺口 ③）仍需对**这个** `F5` 证明 `d(cup (infl y) π) = y`。
* `v` 取 `TauCeti.normalizedValuation F`（`Hyp747` 的 `valLinOf_eq_zero_iff_res1V_eq_zero` 要求；
  `Hyp747` 文件头已论证：`ValCompat v` ＋ `v π = 1` 就刻画它，故这是**归约而非限制**）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-! ## ① 膨胀的类无分歧 -/

/-- ★★★★★ **膨胀的类无分歧**：`Γ⧸I` 上的类沿商映射拉回后，`v̄ = 0`（即落在 `ker v̄ = VKG`）。

**证明**（三步，全用现成件）：
1. `Hyp747.valLinOf_eq_zero_iff_res1V_eq_zero`：`v̄ = 0 ↔ res₁ = 0`；
2. `Hyp758.res1V_h1ToVEquiv`：`res₁ (h1ToVEquiv y) = explicitRes1 y`；
3. `explicitRes1_explicitMap1_eq_zero_of_map_le`（TauCeti）：取 `S = ⊥`、`T = I`
   （`I.map (Γ → Γ⧸I) ≤ ⊥`），`c` 在 `⊥` 上的限制为 `0`（平凡群上 `H¹` 单点）⟹ 膨胀后仍为 `0`。 -/
theorem h1ToVEquiv_infl_valLinOf_eq_zero (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p)
    (c : H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)) :
    valLinOf (F := F) (p := p) (TauCeti.normalizedValuation F) hp
      (KummerBridge.h1ToVEquiv (F := F) (p := p)
        (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p) (AbsoluteGaloisGroup F)
          (ZMod p) (inertiaLoc F).quotientMkContinuousMonoidHom
          (AddMonoidHom.id (ZMod p)) continuous_id (fun _ _ => rfl) c)) = 0 := by
  rw [valLinOf_eq_zero_iff_res1V_eq_zero (F := F) (p := p) hp hpq _ rfl]
  rw [res1V_h1ToVEquiv]
  refine ContinuousMonoidHom.explicitRes1_explicitMap1_eq_zero_of_map_le
    (G := AbsoluteGaloisGroup F ⧸ inertiaLoc F) (M := ZMod p)
    (H := AbsoluteGaloisGroup F) (N := ZMod p)
    (φ := (inertiaLoc F).quotientMkContinuousMonoidHom) (f := AddMonoidHom.id (ZMod p))
    continuous_id (fun _ _ => rfl) (S := ⊥) (T := inertiaLoc F) ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    simpa using hx
  · exact Subsingleton.elim _ _

/-! ## ② `H1 (Γ⧸I, ℤ/p) →ₗ VKG` -/

/-- 膨胀 + `h1ToVEquiv` 的加性形态（值域 `GaloBase.V`）。 -/
noncomputable def inflToVAddHom :
    H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p) →+ GaloBase.V F p :=
  (KummerBridge.h1ToVEquiv (F := F) (p := p)).toAddMonoidHom.comp
    (explicitMap1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p) (AbsoluteGaloisGroup F)
      (ZMod p) (inertiaLoc F).quotientMkContinuousMonoidHom
      (AddMonoidHom.id (ZMod p)) continuous_id (fun _ _ => rfl))

/-- ★★★★★ **`H1 (Γ⧸I, ℤ/p) →ₗ[ℤ/p] VKG`**：膨胀的类落在 `ker v̄` 里。

线性性来自 `AddMonoidHom.toZModLinearMap`（`ℤ/p`-线性由加性自动给出，`ZMod` 归纳）。 -/
noncomputable def inflToVKG (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p) :
    H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p) →ₗ[ZMod p]
      VKG F p (TauCeti.normalizedValuation F) hp :=
  (AddMonoidHom.toZModLinearMap p (inflToVAddHom (F := F) (p := p))).codRestrict
    (LinearMap.ker (valLinOf (F := F) (p := p) (TauCeti.normalizedValuation F) hp))
    (fun c => h1ToVEquiv_infl_valLinOf_eq_zero (F := F) (p := p) hp hpq c)

/-! ## ③ `F5` 本体 -/

/-- ★★★★★ **`F5`（缺口 ② 的落点）**：`H¹(Γ⧸I, H¹(I,ℤ/p)) →ₗ[ℤ/p] VKG`。

＝ `inflToVKG ∘ coeffChangeEquiv_uncond`：先用 `Hyp771`（**无条件**）的系数变换把
`H¹(Γ⧸I, H¹(I,ℤ/p))` 化成 `H¹(Γ⧸I, ℤ/p)`，再膨胀、再落到 `ker v̄`。

**⟹ `Hyp757.hd_infl_of_linear` 可以直接作用在这个 `F5` 上。** -/
noncomputable def F5_uncond [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    [IsTopologicalAddGroup (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (H1 ↥(inertiaLoc F) (ZMod p))]
    (hp : IsUnit (p : F)) (hpq : ¬ ringChar 𝓀[F] ∣ p) (hpq' : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤)
    (x : H1 ↥(inertiaLoc F) (ZMod p)) (hx : x ≠ 0) :
    H1 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p)) →ₗ[ZMod p]
      VKG F p (TauCeti.normalizedValuation F) hp :=
  (inflToVKG (F := F) (p := p) hp hpq).comp
    (AddMonoidHom.toZModLinearMap p
      ((coeffChangeEquiv_uncond (F := F) p q hpq' ζ hζ hgen x hx).toAddMonoidHom))

end L20261018

#print axioms L20261018.h1ToVEquiv_infl_valLinOf_eq_zero
#print axioms L20261018.inflToVAddHom
#print axioms L20261018.inflToVKG
#print axioms L20261018.F5_uncond
