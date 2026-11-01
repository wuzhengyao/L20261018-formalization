import L20261018.Hyp161

/-!
# R1246（S34 第 17 轮）：**用论文的 `∂₂` 两条性质替换 `[Finite (ResidueField)]`**

`HenselResidueData` 的构造原先把 `(R1)`／`(R2)`（`TameResidueFacts`）当作输入；
本战役此前的路线（`Hyp302.unitsCupVanish`）在**有限**剩余域下证它们，
于是 `Hyp321`／`Hyp323` 都带 `[Finite (IsLocalRing.ResidueField ↥𝒪[F])]` ——
**而论文第 4 章没有这条假设**（`raw/L20261018.tex:1554–1566`）。

本轮把 `[Finite (ResidueField)]` 换回**论文自己的** `prop:prelim-residue` (1)：

* `∂₂(inf ξ) = 0`（对一切 `ξ ∈ H²(𝓀, μ_p)`），
* `∂₂(inf η ∪ (π)) = η`，

再加上 `ker \bar v = range inf` 的满射性（`prop:prelim-kummer-valuation`，同为论文假设），
**即可推出 `TameResidueFacts`** —— 不需要剩余域有限，也不需要杯积本身为零
（后者对无限剩余域**为假**：`= infl(ū∪w̄)` 而 `Br(𝓀)[p] ≠ 0`）。

## 本轮

| 声明 | 内容 |
|---|---|
| **`tameResidueFacts_of_residueMap`** | ★★★★★★ **`(R1) ∧ (R2)` 由 `∂₂` 的两条性质推出** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace L20261018

open TauCeti

variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]
  {H2 : Type*} [AddCommGroup H2] [Module k H2]
  {VK : Type*} [AddCommGroup VK] [Module k VK]

/-- ★★★★★★ **`TameResidueFacts` 由 `∂₂` 的两条性质推出**（替代 `[Finite (ResidueField)]`）。

假设：
* `ker val ⊆ range infl`（`prop:prelim-kummer-valuation` 的满射性），`val ∘ infl = 0`；
* `d : H² →ₗ VK` 满足 **`d (cup (inf y) (inf z)) = 0`** 与 **`d (cup (inf y) π) = y`**
  —— 这正是论文 `prop:prelim-residue` (1) 的两条（`∂₂(inf ξ)=0` 与 `∂₂(inf η ∪ (π))=η`）。

则 `(R1) Φ 单射` 与 `(R2) range Φ ⊥ residueSpan` 同时成立：
任取 `x ∈ ker val`，写 `x = inf η`，则 `d (Φ x) = η`；
而 `d` 在 `residueSpan` 上为零（其生成元是 `inf` 的两两杯积）⟹ `η = 0` ⟹ `x = 0`。 -/
theorem tameResidueFacts_of_residueMap
    (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) (π : V)
    (infl : VK →ₗ[k] V) (hval_infl : ∀ y : VK, val (infl y) = 0)
    (hsurj : ∀ x : V, val x = 0 → ∃ y : VK, infl y = x)
    (d : H2 →ₗ[k] VK)
    (hd_infl : ∀ y z : VK, d (cup (infl y) (infl z)) = 0)
    (hd_cup_pi : ∀ y : VK, d (cup (infl y) π) = y) :
    TameResidueFacts cup val π where
  phi_injective := by
    intro x y hxy
    obtain ⟨ηx, hx_eq⟩ := hsurj (x : V) x.2
    obtain ⟨ηy, hy_eq⟩ := hsurj (y : V) y.2
    have ex : (⟨infl ηx, hval_infl ηx⟩ : ↥(LinearMap.ker val)) = x := Subtype.ext hx_eq
    have ey : (⟨infl ηy, hval_infl ηy⟩ : ↥(LinearMap.ker val)) = y := Subtype.ext hy_eq
    have h1 : ηx = ηy := by
      rw [← hd_cup_pi ηx, ← hd_cup_pi ηy]
      rw [← show residuePhi cup val π ⟨infl ηx, hval_infl ηx⟩ = cup (infl ηx) π from rfl]
      rw [← show residuePhi cup val π ⟨infl ηy, hval_infl ηy⟩ = cup (infl ηy) π from rfl]
      rw [ex, ey, hxy]
    exact Subtype.ext (by rw [← hx_eq, h1, hy_eq])
  disjoint := by
    rw [Submodule.disjoint_def]
    intro y hy hyspan
    have hspan : ∀ w ∈ residueSpan cup val, d w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem _ hp =>
          obtain ⟨⟨z, z'⟩, rfl⟩ := hp
          obtain ⟨η₁, h₁⟩ := hsurj (z : V) z.2
          obtain ⟨η₂, h₂⟩ := hsurj (z' : V) z'.2
          show d (cup (z : V) (z' : V)) = 0
          rw [← h₁, ← h₂]
          exact hd_infl η₁ η₂
      | zero => simp
      | add _ _ _ _ ha hb => simp [map_add, ha, hb]
      | smul c _ _ ha => simp [map_smul, ha]
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨η, hη_eq⟩ := hsurj (x : V) x.2
    have ex : (⟨infl η, hval_infl η⟩ : ↥(LinearMap.ker val)) = x := Subtype.ext hη_eq
    have h1 : residuePhi cup val π x = 0 := by
      have h0 : η = 0 := by
        rw [← hd_cup_pi η]
        rw [← show residuePhi cup val π ⟨infl η, hval_infl η⟩ = cup (infl η) π from rfl]
        rw [ex]
        exact hspan _ hyspan
      rw [← ex, h0]
      simp [residuePhi]
    exact h1

end L20261018

#print axioms L20261018.tameResidueFacts_of_residueMap
