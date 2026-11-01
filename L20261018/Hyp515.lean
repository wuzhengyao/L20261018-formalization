import Hyp514
import TauCeti.NumberTheory.LocalField.WildInertia

/-!
# S43 R20（**S2**）：`I_K` 的 ℓ-Sylow 化到 `I_K/P_K`，且与 `P_K` 交平凡

## 本件在（★）的哪一格

S3c 已闭合（`Hyp513` ＋ `Hyp514`）：模型 `ℤ̂^{(p')}(1) = I_K/P_K` 的 ℓ-部分 ≅ `ℤ_ℓ` 且无限。
本件补上**从 `I_K` 到 `I_K/P_K` 的那一趟**（`PROMPT-S43` §2.2 的 S2）：

```
（★）：I_K 的 ℓ-Sylow ≅ ℤ_ℓ   （ℓ ≠ char κ）
   ├─ ① I_K 的 ℓ-Sylow 的像 = I_K/P_K 的 ℓ-Sylow      ← 本件（Sylow 商引理）
   └─ ② ℓ-Sylow ∩ P_K = ⊥                            ← 本件（互素消没）
```

## 数学

`P_K`（野惯性）是 `I_K` 的 **char κ-Sylow**（TauCeti `isProPSylow_wildInertiaSubgroup`），
且是**唯一**的（`eq_subgroupOf_wildInertiaSubgroup_of_isProPSylow`）。于是对 ℓ ≠ char κ：

* ① **Sylow 商引理**（`IsProPSylow.map_of_surjective`）：`I_K ↠ I_K/P_K` 连续满射，
  源紧、靶 T2 ⟹ ℓ-Sylow 的像仍是 ℓ-Sylow；
* ② **互素消没**（`IsProP.subsingleton_of_ne`）：`P ⊓ P_K` 同时 pro-ℓ（≤ `P`）与 pro-char κ
  （≤ `P_K`），两素数不同 ⟹ 平凡。

## 载体选择：为什么靶是 `↥(tameInertia K)` 而不是商类型

TauCeti 的 `tameQuotient K = G_K / P_K`，而 `tameInertia K = I_K` 的像（`Tame/Quotient.lean:300`）。
**`ker(toTameQuotient) = P_K`**（`toTameQuotient_eq_one_iff`）⟹ `tameInertia K ≅ I_K / P_K`。
取 `↥(tameInertia K)` 作靶有两个好处：`T2Space` 是现成实例（`tameQuotient K` 的 T2 ＋ 子类型），
且 `tameInertiaHom : M ≅ tameInertia`（`range_tameInertiaHom` ＋ 单射）**已经是现成件**，
下一轮 S4 直接沿它搬运 S3c 的结论。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`toTameInertia`** | `↥I_K →ₜ* ↥(tameInertia K)`（`toTameQuotient` 的受限像） |
| **`toTameInertia_surjective`** | 它是满射 |
| **`isProPSylow_map_toTameInertia`** | ★★★★★ **S2①**：ℓ-Sylow 的像是 ℓ-Sylow |
| **`inf_wildInertia_eq_bot`** | ★★★★★ **S2②**：ℓ ≠ char κ ⟹ `P ⊓ P_K = ⊥` |

## 诚实边界

* 本件**不**组装（★）：`I_K` 自身的 `InertiaProPSylowData` 还差 S4 的**拓扑**等价
  `↥P ≃ₜ* ↥(ℓ-Sylow of tameInertia)`（②只给抽象 iso，拓扑版需「紧 Hausdorff 上连续双射是同胚」）。
* `Ch4TameSymbolHyp`（一般 `K`）仍 `∅-open`。

## 侦察记录（三件套）

* `grep -n "^theorem" raw/TauCeti/TauCeti/NumberTheory/LocalField/WildInertia.lean`
  —— 命中 `isProP_wildInertiaSubgroup`／`isProPSylow_wildInertiaSubgroup`／
  `eq_subgroupOf_wildInertiaSubgroup_of_isProPSylow`／`le_wildInertiaSubgroup_of_isProP`；
  **扫过的目录**：`NumberTheory/LocalField/`（`WildInertia`／`Tame/` 6 文件／`Unramified/Inertia`）、
  `Topology/Algebra/Group/Profinite/{Sylow,ProP}`；
* `port_tau.py TauCeti.NumberTheory.LocalField.WildInertia`（已缓存）＋ `.probe/q1.lean` 的 `#check`；
* `IsProPSylow.map_of_surjective` 由 S42 的内容式检索命中（`Sylow/Functoriality.lean:52`），本件首次消费。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti
open scoped TauCeti.zHat

namespace L20261018

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **S2 的载体桥**：`↥I_K →ₜ* ↥(tameInertia K)`，即 `I_K ↠ I_K/P_K`
（`ker(toTameQuotient) = P_K`）。 -/
noncomputable def toTameInertia :
    ↥(inertiaSubgroup K) →ₜ* ↥(tameInertia K) where
  toMonoidHom :=
    ((toTameQuotient K).toMonoidHom.comp (inertiaSubgroup K).subtype).codRestrict
      (tameInertia K) fun σ => by
        rw [tameInertia_def]
        exact Subgroup.mem_map.mpr ⟨σ.1, σ.2, rfl⟩
  continuous_toFun :=
    Continuous.subtype_mk ((toTameQuotient K).continuous.comp continuous_subtype_val) _

/-- **S2 的桥是满射**（`tameInertia K` 按定义就是 `I_K` 的像）。 -/
theorem toTameInertia_surjective : Function.Surjective (toTameInertia (K := K)) := by
  rintro ⟨y, hy⟩
  rw [tameInertia_def] at hy
  obtain ⟨σ, hσ, hσy⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨σ, hσ⟩, Subtype.ext hσy⟩

/-- ★★★★★ **S2①：`I_K` 的 ℓ-Sylow 的像是 `I_K/P_K` 的 ℓ-Sylow**
（Sylow 的连续满射函子性，源紧 ＋ 靶 T2）。 -/
theorem isProPSylow_map_toTameInertia (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Subgroup ↥(inertiaSubgroup K)) (hP : IsProPSylow ℓ P) :
    IsProPSylow ℓ (Subgroup.map (toTameInertia (K := K)).toMonoidHom P) := by
  haveI : CompactSpace ↥(inertiaSubgroup K) :=
    isCompact_iff_compactSpace.mp (isClosed_inertiaSubgroup K).isCompact
  exact hP.map_of_surjective _ (toTameInertia (K := K)).continuous toTameInertia_surjective

/-- ★★★★★ **S2②：ℓ ≠ char κ 时 `I_K` 的 ℓ-Sylow 与野惯性交平凡**
（互素消没：`P ⊓ P_K` 同时 pro-ℓ 与 pro-`char κ`）。 -/
theorem inf_wildInertia_eq_bot (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) q]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (P : Subgroup ↥(inertiaSubgroup K)) (hP : IsProPSylow ℓ P) :
    P ⊓ (wildInertiaSubgroup K).subgroupOf (inertiaSubgroup K) = ⊥ := by
  haveI : Fact q.Prime :=
    ⟨CharP.char_is_prime (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) q⟩
  haveI : CompactSpace ↥(inertiaSubgroup K) :=
    isCompact_iff_compactSpace.mp (isClosed_inertiaSubgroup K).isCompact
  -- `P_K` 在 `↥I_K` 里闭
  have hPKclosed : IsClosed
      (((wildInertiaSubgroup K).subgroupOf (inertiaSubgroup K) :
        Subgroup ↥(inertiaSubgroup K)) : Set ↥(inertiaSubgroup K)) := by
    have hset : (((wildInertiaSubgroup K).subgroupOf (inertiaSubgroup K) :
          Subgroup ↥(inertiaSubgroup K)) : Set ↥(inertiaSubgroup K))
        = (fun x : ↥(inertiaSubgroup K) => (x : Field.absoluteGaloisGroup K)) ⁻¹'
            ((wildInertiaSubgroup K) : Set (Field.absoluteGaloisGroup K)) := by
      ext x
      exact Subgroup.mem_subgroupOf
    rw [hset]
    exact (isClosed_wildInertiaSubgroup K).preimage continuous_subtype_val
  set R : Subgroup ↥(inertiaSubgroup K) :=
    P ⊓ (wildInertiaSubgroup K).subgroupOf (inertiaSubgroup K) with hR
  have hRclosed : IsClosed (R : Set ↥(inertiaSubgroup K)) := hP.isClosed.inter hPKclosed
  haveI : CompactSpace ↥R := isCompact_iff_compactSpace.mp hRclosed.isCompact
  -- `R` 同时 pro-ℓ 与 pro-`q`
  have hRℓ : IsProP ℓ ↥R := hP.isProP.mono inf_le_left
  have hPKq : IsProP q ↥((wildInertiaSubgroup K).subgroupOf (inertiaSubgroup K)) :=
    (Subgroup.isProP_subgroupOf_iff (wildInertiaSubgroup_le_inertiaSubgroup K)).2
      (isProP_wildInertiaSubgroup K q)
  have hRq : IsProP q ↥R := hPKq.mono inf_le_right
  haveI : Subsingleton ↥R := IsProP.subsingleton_of_ne hRℓ hRq hℓq
  refine Subgroup.eq_bot_iff_forall R |>.mpr fun x hx => ?_
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥R) 1)

/-- **S2② 的常用形式**：由「`ℓ` 与 char κ 互素」直接得交平凡。 -/
theorem inf_wildInertia_eq_bot' (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) q]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime q)
    (P : Subgroup ↥(inertiaSubgroup K)) (hP : IsProPSylow ℓ P) :
    P ⊓ (wildInertiaSubgroup K).subgroupOf (inertiaSubgroup K) = ⊥ := by
  have hnd : ¬ ℓ ∣ q := (Fact.out : ℓ.Prime).coprime_iff_not_dvd.1 hℓ
  exact inf_wildInertia_eq_bot q ℓ (fun h => hnd (h ▸ dvd_rfl)) P hP

end L20261018

#print axioms L20261018.toTameInertia
#print axioms L20261018.toTameInertia_surjective
#print axioms L20261018.isProPSylow_map_toTameInertia
#print axioms L20261018.inf_wildInertia_eq_bot
#print axioms L20261018.inf_wildInertia_eq_bot'
