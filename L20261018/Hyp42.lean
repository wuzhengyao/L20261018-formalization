import L20261018.Hyp36
import L20261018.Hyp41
/-!
# C1 收口：`hroots` **恒真**（`p` 在基域中可逆即可），故不再是技术前提

`Hyp29`／`Hyp35`／`Hyp36`／`Hyp40` 都带一条技术前提

```
hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F)
```

即「`Δ` 的元素在可分闭包中可开 `p` 次方」。本文件证明它**不需要假设**：

* `SeparableClosure F` 是**可分闭**的（`SeparableClosure.isSepClosed`）；
* `hp : IsUnit (p : F)` 给出 `(p : SeparableClosure F) ≠ 0`；
* 于是 `IsSepClosed.exists_pow_nat_eq` 直接给出 `p` 次根。

⟹ `A` 档各条的技术前提 `hroots` 可以整个去掉。本文件给出去掉后的
`lemma_3_1_2_galo'`（3.1(2) 的 `hroots`-free 形式）作为示例。

## 主结果

* `RootsOfUnityExists.exists_pow_eq_algebraMap`：**`hroots` 恒真**。
* `RootsOfUnityExists.exists_pow_eq_algebraMap'`：集合形式的同一陈述。
-/

open TauCeti

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RootsOfUnityExists

/-- **`hroots` 恒真**：`p` 在基域中可逆时，`F` 的任一元素在可分闭包中都有 `p` 次根。

`SeparableClosure F` 可分闭，`X^p − b` 在 `hp` 下可分，故根存在；
这里用 `IsSepClosed.exists_pow_nat_eq` 一步得到。 -/
theorem exists_pow_eq_algebraMap {F : Type} [Field F] {p : ℕ} (hp : IsUnit (p : F))
    (b : Fˣ) :
    ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F) := by
  haveI : NeZero (p : SeparableClosure F) := by
    refine ⟨fun h => ?_⟩
    have h' : algebraMap F (SeparableClosure F) (p : F) = 0 := by
      rw [map_natCast]; exact h
    have hpne : (p : F) ≠ 0 := hp.ne_zero
    exact hpne ((algebraMap F (SeparableClosure F)).injective (by rw [h', map_zero]))
  exact IsSepClosed.exists_pow_nat_eq (algebraMap F (SeparableClosure F) (b : F)) p

/-- **`hroots` 作为 `Hyp29`／`Hyp35`／`Hyp36`／`Hyp40` 的前提，可以被直接填上。** -/
theorem hroots {F : Type} [Field F] {p : ℕ} (hp : IsUnit (p : F)) (Δ : Subgroup Fˣ) :
    ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F) :=
  fun b _ => exists_pow_eq_algebraMap hp b

/-- **3.1(2) 的 `hroots`-free 形式**（A 档 3.1(2) 的技术前提去掉一个）。 -/
-- @source file=raw/L20261018.tex locator=label:lem:orthogonal quote="限制映射 $\res_{E/F}|_{U^\perp}:U^\perp\to H^1(E,\mu_p)$ 为单射；"
theorem lemma_3_1_2_galo' {F : Type} [Field F] {p : ℕ} [Fact p.Prime]
    [HasEnoughRootsOfUnity F p] (hp : IsUnit (p : F)) (a1 a2 : Fˣ) (hp2 : p ≠ 2)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex
      (Subgroup.closure ({a1, a2} : Set Fˣ))]
    (hne : GaloBase.cup (K := F) (p := p)
      (KummerBridge.kummerClass F p hp a1) (KummerBridge.kummerClass F p hp a2) ≠ 0) :
    Function.Injective (fun x : (L20261018.galoBiKummer (K := F) (p := p)
        (KummerBridge.kummerClass F p hp a1)
        (KummerBridge.kummerClass F p hp a2) hne).Uperp =>
      (ContinuousCohomology.res
        (IntermediateField.val (kummerField (SeparableClosure F) p
          (Subgroup.closure ({a1, a2} : Set Fˣ)))).fieldRange.fixingSubgroup
        (GaloBase.muP F p) 1).hom x.val) :=
  KummerV.lemma_3_1_2_galo hp a1 a2 hp2 (hroots hp _) hne

end RootsOfUnityExists
