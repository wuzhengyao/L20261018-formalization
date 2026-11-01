import L20261018.Infra.Cohomology.ResidueLES.Step014_continuous_d_two_blocks

/-!
# S46 R4：★★★★ **`VKG` 的 Kummer 分解 ＋ `kills` 的归约接口**

## 这一步在 GS 的哪一句

GS 6.8.8(2)（在战役里是 `GsResidueData` 的 `kills` 字段）说 `∂₂((u) ∪ (w)) = 0`（`u, w` 单位）。
但战役的 `kills` 写的是 `residueSpan ≤ ker dRes`，而 `residueSpan` 是按 `ker v̄` **整个**张成的。
本件把两者接通：

```
y ∈ ker v̄  ⟹  y = (u)（某个 u ∈ Fˣ）且 v(u) = 1
```

（两行：`kummerClass` **满射**（`Hyp36.kummerClass_surjective`）＋ `valLinOf_kummerClass`（`Hyp162`）。）
于是「对 `ker v̄` 全体的陈述」⟺「对单位的陈述」——这正是 GS 6.8.8(2) 的形态。

**注意**：`ker v̄` 严格大于不分歧类（`Hyp435.ker_valLin_contains_zeta`：`(ζ_p) ∈ ker v̄` 却分歧），
故本件的分解**不能**加强成「`ker v̄` 只有 Teichmüller 部分」。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`exists_unit_kummerClass_of_mem_ker`** | ★★★★ `y ∈ ker v̄ ⟹ ∃ u, y = (u) ∧ valOfUnitOf v u = 0` |
| **`forall_VKG_cup_eq_zero_of_units`** | ★★★★★ **「单位杯积为零 ⟹ `ker v̄` 全体杯积为零」**（`Hyp342` 的 `hd_infl` 入口） |
| **`residueSpan_le_ker_of_units`** | ★★★★★ **「单位杯积为零 ⟹ `residueSpan ≤ ker d`」**（`Hyp532.GsResidueData.kills` 的直接入口） |
| `residueSpan_le_ker_iff` | 两者的等价（便于反向使用） |

## 诚实边界

* 本件**只做归约**：它把 `kills` 从「`ker v̄` 全体」降到「单位对」，**不证**单位杯积为零
  （那是 GS 6.8.8(2) 的数学内容，须经 `(u) = Inf(ū)` ＋ (d)，见 `S46-DIGEST` §5）。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ}

/-- ★★★★ **`ker v̄` 的每个元素都是某个「单位」的 Kummer 类**。

证明 = `kummerClass` 满射（`Hyp36`）取原像 ＋ `valLinOf_kummerClass`（`Hyp162`）读出 `v(u) ≡ 0`。 -/
theorem exists_unit_kummerClass_of_mem_ker (hp : IsUnit (p : F)) {y : GaloBase.V F p}
    (hy : y ∈ LinearMap.ker (valLinOf (F := F) (p := p) v hp)) :
    ∃ u : Fˣ, KummerBridge.kummerClass F p hp u = y ∧ valOfUnitOf (p := p) v u = 0 := by
  obtain ⟨u, rfl⟩ := KummerV.kummerClass_surjective (F := F) (p := p) hp y
  refine ⟨u, rfl, ?_⟩
  have h : valLinOf (F := F) (p := p) v hp (KummerBridge.kummerClass F p hp u) = 0 := hy
  rwa [valLinOf_kummerClass] at h

/-- ★★★★★ **单位杯积为零 ⟹ `ker v̄` 全体的杯积为零**（`Hyp342.hd_infl` 的入口形态）。 -/
theorem forall_VKG_cup_eq_zero_of_units (hp : IsUnit (p : F))
    (d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hp)
    (h_cup : ∀ a b : Fˣ, valOfUnitOf (p := p) v a = 0 → valOfUnitOf (p := p) v b = 0 →
      d (GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a)
        (KummerBridge.kummerClass F p hp b)) = 0) :
    ∀ y z : VKG F p v hp,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0 := by
  intro y z
  obtain ⟨a, ha, hva⟩ :=
    exists_unit_kummerClass_of_mem_ker (p := p) (v := v) hp (y := (y : GaloBase.V F p)) y.2
  obtain ⟨b, hb, hvb⟩ :=
    exists_unit_kummerClass_of_mem_ker (p := p) (v := v) hp (y := (z : GaloBase.V F p)) z.2
  rw [← ha, ← hb]
  exact h_cup a b hva hvb

/-- ★★★★★ **单位杯积为零 ⟹ `residueSpan ≤ ker d`**（`GsResidueData.kills` 的直接入口）。 -/
theorem residueSpan_le_ker_of_units (hp : IsUnit (p : F))
    (d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hp)
    (h_cup : ∀ a b : Fˣ, valOfUnitOf (p := p) v a = 0 → valOfUnitOf (p := p) v b = 0 →
      d (GaloBase.cup (K := F) (p := p) (KummerBridge.kummerClass F p hp a)
        (KummerBridge.kummerClass F p hp b)) = 0) :
    residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hp)
      ≤ LinearMap.ker d := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, rfl⟩
  exact forall_VKG_cup_eq_zero_of_units (p := p) (v := v) hp d h_cup ⟨y, hy⟩ ⟨z, hz⟩

/-- 反向：`residueSpan ≤ ker d` ⟹ `ker v̄` 全体的杯积被杀（两者等价，便于双向使用）。 -/
theorem VKG_cup_eq_zero_of_residueSpan_le (hp : IsUnit (p : F))
    (d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hp)
    (h : residueSpan (GaloBase.cup (K := F) (p := p)) (valLinOf (F := F) (p := p) v hp)
      ≤ LinearMap.ker d) :
    ∀ y z : VKG F p v hp,
      d (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0 :=
  fun y z => h (cup_mem_residueSpan (GaloBase.cup (K := F) (p := p))
    (valLinOf (F := F) (p := p) v hp) y z)

end L20261018

#print axioms L20261018.exists_unit_kummerClass_of_mem_ker
#print axioms L20261018.forall_VKG_cup_eq_zero_of_units
#print axioms L20261018.residueSpan_le_ker_of_units
#print axioms L20261018.VKG_cup_eq_zero_of_residueSpan_le
