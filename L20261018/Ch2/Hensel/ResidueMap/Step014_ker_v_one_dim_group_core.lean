import L20261018.Ch2.Hensel.ResidueMap.Step013_huu_reduced_to_linear_dependence

/-!
# R974：`ker\bar v ≤ 1` 维的第 2 步 —— 群论核心（`κˣ/(κˣ)^p` 中任两元成幂关系）

R973 已把 `hUU` 归约成 `hdep`（`\ker\bar v` 内任两元线性相关）。本文件证**群论侧**：

**`exists_pow_eq_of_pow_eq_one`**：`G` 有限交换循环、`H ◁ G`、商群 `G ⧸ H` 的指数整除素数 `p`
⟹ 商群中任两元成幂关系（`b ≠ 1 ⟹ ∃ n : ℕ, a = b ^ n`）。

证法（**不用模结构**，纯 `Nat.card` ＋ `orderOf`）：
取生成元 `γ`（`IsCyclic.exists_generator`），`Nat.card Q = orderOf γ ∣ p` ⟹ `Nat.card Q ≤ p`；
对 `b ≠ 1`：`orderOf b ∣ p` 且 `≠ 1` ⟹ `orderOf b = p`；子群卡片整除 ⟹ `Nat.card Q = p`；
于是 `Nat.card ↥(zpowers b) = p = Nat.card Q` ⟹ `zpowers b = ⊤`（`Subgroup.eq_top_of_card_eq`）
⟹ `a = b ^ k`（`k : ℤ`）；最后用 `zpow_eq_zpow_emod` 把 `k` 降到 `[0, p)` 得 `ℕ`-幂。

**这是 R973 三次失败的修法**：不再引入 `Module (ZMod p)`（那会使 `ofMul_zpow` 的 `•` 与模 smul 冲突），
而走纯卡片／`orderOf` 路线。
-/

set_option maxHeartbeats 1000000

namespace L20261018

/-- **群论核心**：有限交换循环群对正规子群的商，若指数整除素数 `p`，
则商群中任意两元成幂关系。 -/
theorem exists_pow_eq_of_pow_eq_one
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (H : Subgroup G) [H.Normal] (p : ℕ) [Fact p.Prime]
    (hH : ∀ x : G ⧸ H, x ^ p = 1) :
    ∀ a b : G ⧸ H, b ≠ 1 → ∃ n : ℕ, a = b ^ n := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  -- 商群循环
  haveI : IsCyclic (G ⧸ H) :=
    isCyclic_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  haveI : Finite (G ⧸ H) := Quotient.finite _
  -- 取生成元，`Nat.card Q = orderOf γ ∣ p`
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G ⧸ H)
  have hγtop : Subgroup.zpowers γ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact hγ x
  have hcard : Nat.card (G ⧸ H) = orderOf γ := by
    rw [← Nat.card_zpowers γ, hγtop]
    exact (Nat.card_congr (Subgroup.topEquiv).toEquiv).symm
  have hdvd : Nat.card (G ⧸ H) ∣ p := by
    rw [hcard]
    exact orderOf_dvd_iff_pow_eq_one.mpr (hH γ)
  have hle : Nat.card (G ⧸ H) ≤ p := Nat.le_of_dvd hp hdvd
  intro a b hb
  -- `orderOf b = p`
  have hob_dvd : orderOf b ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hH b)
  have hob_ne : orderOf b ≠ 1 := by
    intro h
    exact hb (orderOf_eq_one_iff.mp h)
  have hob : orderOf b = p := by
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hob_dvd with h | h
    · exact absurd h hob_ne
    · exact h
  -- 子群 `⟨b⟩` 的卡片也是 `p`，故等于顶
  have hbz : Nat.card ↥(Subgroup.zpowers b) = p := by
    rw [Nat.card_zpowers]
    exact hob
  have hb_le : Nat.card ↥(Subgroup.zpowers b) ≤ Nat.card (G ⧸ H) :=
    Nat.le_of_dvd (Nat.card_pos) (Subgroup.card_subgroup_dvd_card _)
  have hQ : Nat.card (G ⧸ H) = p := le_antisymm hle (hbz ▸ hb_le)
  haveI : Finite ↥(Subgroup.zpowers b) := Subtype.finite
  have htop : Subgroup.zpowers b = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hbz, hQ])
  -- `a ∈ ⟨b⟩` ⟹ `a = b ^ k`（`k : ℤ`），再降到 `ℕ`-幂
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top a)
  refine ⟨(k % (p : ℤ)).toNat, ?_⟩
  have hz : b ^ (p : ℤ) = 1 := by rw [zpow_natCast, hH b]
  have h1 : b ^ k = b ^ (k % (p : ℤ)) := zpow_eq_zpow_emod k hz
  have h2 : b ^ (k % (p : ℤ)) = b ^ ((k % (p : ℤ)).toNat) := by
    rw [← zpow_natCast]
    congr 1
    exact (Int.toNat_of_nonneg (Int.emod_nonneg k hpne)).symm
  rw [← hk, h1, h2]

end L20261018
#print axioms L20261018.exists_pow_eq_of_pow_eq_one
