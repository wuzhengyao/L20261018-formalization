import Hyp168
import Mathlib.RingTheory.AdjoinRoot

/-!
# R1022（路径 A · **A1′·2·b**）：`O_F[s]` 上**模 `s` 的剩余映射**

`Hyp168` 给了 `X^p − C π` 在 `𝒪_F` 上关于 `𝔪` 的 Eisenstein 性。本文件在
`O_F[s] ≅ 𝒪_F[X]/(X^p − π)`（`AdjoinRoot`）上造出 A1′·2 所需的**剩余映射**

```
φ : 𝒪_F[X]/(X^p − π)  →+*  𝓀_F ,     X ↦ 0 （再取剩余）
```

它是「**把 `x = a₀ + a₁s + … + a_{p−1}s^{p−1}` 送到 `ā₀`**」的严格形式，
也是下一步（`·c`：`p×p` 乘性矩阵模 `π` 后上三角、对角 `a₀` ⟹ `N(x) ≡ a₀^p (mod s)`）的入口。

| 声明 | 内容 |
|---|---|
| **`residueAtRoot`** | 上述 `φ`（`AdjoinRoot.lift`：`𝒪_F → 𝓀_F` 取剩余，`X ↦ 0`） |
| `residueAtRoot_root` | `φ(s) = 0` |
| `residueAtRoot_C` | `φ(C a) = 残差 a`（即 `φ` 在常数项上就是单位约化） |
| `residueAtRoot_surjective` | `φ` 满射（`IsLocalRing.residue_surjective` 提升） |
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section Residue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **模 `s` 的剩余映射**：`𝒪_F[X]/(X^p − π) → 𝓀_F`，把 `s ↦ 0` 后取单位约化。

（`X^p − π` 在 `X = 0` 处的求值只看到常数项 `−π`，而 `π ∈ 𝔪` 故其剩余为 `0`。） -/
noncomputable def residueAtRoot (hv : ValFiltrationCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {b : 𝒪[F]ˣ}
    (hb : Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) b = π) :
    AdjoinRoot (X ^ p - C (b : ↥𝒪[F])) →+* 𝓀[F] := by
  have hb𝔪 : (b : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] :=
    (hv.mem_maximalIdeal b).mpr ⟨1, one_pos, by rw [hb, hπ]⟩
  have hres : IsLocalRing.residue ↥𝒪[F] (b : ↥𝒪[F]) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hb𝔪
  refine AdjoinRoot.lift (IsLocalRing.residue ↥𝒪[F]) 0 ?_
  simp [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, hres,
    zero_pow (Fact.out : p.Prime).pos.ne']

/-- **`φ(s) = 0`**。 -/
theorem residueAtRoot_root (hv : ValFiltrationCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {b : 𝒪[F]ˣ}
    (hb : Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) b = π) :
    residueAtRoot (F := F) p hv hπ hb (AdjoinRoot.root (X ^ p - C (b : ↥𝒪[F]))) = 0 := by
  unfold residueAtRoot
  exact AdjoinRoot.lift_root _

/-- **`φ(C a) = 残差 a`**（`φ` 在常数项上就是单位约化）。 -/
theorem residueAtRoot_C (hv : ValFiltrationCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {b : 𝒪[F]ˣ}
    (hb : Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) b = π) (a : ↥𝒪[F]) :
    residueAtRoot (F := F) p hv hπ hb
      (AdjoinRoot.mk (X ^ p - C (b : ↥𝒪[F])) (Polynomial.C a)) = IsLocalRing.residue ↥𝒪[F] a := by
  unfold residueAtRoot
  rw [AdjoinRoot.lift_mk]
  simp

/-- **`φ` 满射**（`𝒪_F → 𝓀_F` 的剩余满射的提升）。 -/
theorem residueAtRoot_surjective (hv : ValFiltrationCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {b : 𝒪[F]ˣ}
    (hb : Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) b = π) :
    Function.Surjective (residueAtRoot (F := F) p hv hπ hb) := by
  intro y
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective y
  exact ⟨AdjoinRoot.mk _ (Polynomial.C a), by rw [residueAtRoot_C]; exact ha⟩

end Residue

end L20261018

#print axioms L20261018.residueAtRoot_root
#print axioms L20261018.residueAtRoot_C
#print axioms L20261018.residueAtRoot_surjective
