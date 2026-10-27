import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# 缺口 1 的残余（第一半）：**呈现定义的符号代数** `(a,b)_ζ` 与它的正规形

论文 `def:decomposable`（`raw/L20261018.tex` 行 633–651）把次数 `p` 的**符号代数**定义为
生成元–关系呈现

    (a,b)_F = F⟨x,y⟩ / (x^p − a,  y^p − b,  yx − ζ_p xy),

并**在同一处**声明：若 `a ∉ F^{×p}`、`L = F(a^{1/p})`、`σ(a^{1/p}) = ζ_p a^{1/p}`，
则 `(a,b)_F ≅ (L/F, σ, b)`（循环代数；GS2017 §2.5）。

本战役此前只有这个对象的**散文描述**：`Hyp34`／`Hyp37`／`Hyp41` 三层引擎讨论的都是
「循环代数」那一侧，而**呈现本身从未被定义**——因此 `[[hyp-symbol-cup]]` 的残余
（「呈现定义 = 循环交叉积」）一直无对象可写。本文件补上那个缺失的对象。

## 技术选择

用 `RingQuot`（mathlib 的「任意关系生成的商」，`Mathlib/Algebra/RingQuot.lean`）而非
`Ideal.Quotient`：本 pin 的 `Ideal R` 对非交换 `R` 只是**左**理想（`Ideal.IsTwoSided` 是
额外类型类，`Ideal.span` 不自动带该实例），而 `RingQuot` 自带 `Ring`／`Algebra` 实例、
**泛性质**（`RingQuot.liftAlgHom`）与**满射性**（`RingQuot.mkAlgHom_surjective`）。

## 主定义

* `SymbolPres.rel`：三条关系（作为 `FreeAlgebra K (Fin 2)` 上的关系）。
* `SymbolPres.SymbolAlg K p a b ζ = F⟨x,y⟩/(x^p−a, y^p−b, yx−ζxy)`，生成元
  `SymbolPres.SymbolAlg.x`／`.y`。

## 主结果（全部 0 error / 0 sorry / axioms 恰 `propext, Classical.choice, Quot.sound`）

* `x_pow`／`y_pow`／`y_mul_x`：三条关系在 `SymbolAlg` 内成立。
* `adjoin_eq_top`：`SymbolAlg` 由 `x, y` 生成。
* `liftOf`：**泛性质**——任何 `K`-代数中满足三条关系的 `X, Y` 给出 `SymbolAlg →ₐ[K] B`；
  `liftOf_x`／`liftOf_y` 是其计算规则。
* `y_mul_x_pow`／`y_pow_mul_x_pow`：`y^n x^m = ζ^{nm} x^m y^n`。
* `x_pow_eq_smul`／`y_pow_eq_smul`：`x^n = a^{⌊n/p⌋} x^{n mod p}`（指数降次）。
* `span_monomials_eq_top`：**正规形**——`{x^i y^j}_{i,j<p}` 线性张成 `SymbolAlg`
  （这是 GS 那本「呈现给出次数 `p` 的代数」的实质内容）。
* `finiteDimensional`／`finrank_le`：`finrank ≤ p²`。
* `nonempty_algEquiv_of_finrank`：**维数桥**——若 `B` 有满足关系的 `X, Y`、`liftOf` 满射、
  且 `finrank B = p²`，则 `SymbolAlg ≅ B`。这是下一步（`Hyp48`：与循环交叉积、与
  `M_p(K)` 对齐）的通用收口器，对应 TauCeti `CrossedProduct/Quaternion.lean` 的
  `nonempty_quaternionAlgebra_algEquiv_quadratic`（`p = 2` 版）。
* `liftOf_surjective_of_adjoin_eq_top`：满射性判据（`X, Y` 生成 `B` ⟹ `liftOf` 满射）。
* `hom_ext`：从 `SymbolAlg` 出发的同态由两个生成元的像决定（两支认同的反向合成要用）。

## 尚未做的（`Hyp48` 的入口）

* **非退化情形** `a ∉ K^{×p}`：取 `L = K(a^{1/p})`、`σ(α) = ζα`、carry 余环 `c`，
  在 `CrossedProduct c` 内取 `X = α`、`Y = u_σ`，用 `nonempty_algEquiv_of_finrank` 收口
  （三条关系与 `finrank = p²` 是全部所需）。
* **退化情形** `a = α^p`（即 `(f)` 实际需要的）：`SymbolAlg ≅ M_p(K)`，
  `X = α·diag(ζ^i)`、`Y =` 带 `b` 的移位；满射性用「对角 ＋ 移位生成全矩阵代数」。
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace SymbolPres

universe u

variable (K : Type u) [Field K] (p : ℕ)

/-- 定义关系用的自由代数缩写。 -/
abbrev Fr := FreeAlgebra K (Fin 2)

/-- 两个生成元在自由代数中的像。 -/
def gen (i : Fin 2) : Fr K := FreeAlgebra.ι K i

/-- 三条关系，写成 `RingQuot` 需要的关系 `(u, v) ↦ u = 关系式 ∧ v = 0`。 -/
def rel (a b ζ : K) (u v : Fr K) : Prop :=
  (u = gen K 0 ^ p - algebraMap K (Fr K) a ∧ v = 0) ∨
  (u = gen K 1 ^ p - algebraMap K (Fr K) b ∧ v = 0) ∨
  (u = gen K 1 * gen K 0 - algebraMap K (Fr K) ζ * (gen K 0 * gen K 1) ∧ v = 0)

/-- **符号代数** `(a,b)_ζ = K⟨x,y⟩/(x^p−a, y^p−b, yx−ζxy)`（论文 `def:decomposable`）。 -/
abbrev SymbolAlg (a b ζ : K) : Type u := RingQuot (rel K p a b ζ)

namespace SymbolAlg

variable {K p}

/-- 第一个生成元 `x`。 -/
noncomputable def x (a b ζ : K) : SymbolAlg K p a b ζ :=
  RingQuot.mkAlgHom K (rel K p a b ζ) (gen K 0)

/-- 第二个生成元 `y`。 -/
noncomputable def y (a b ζ : K) : SymbolAlg K p a b ζ :=
  RingQuot.mkAlgHom K (rel K p a b ζ) (gen K 1)

variable (a b ζ : K)

/-- **关系 1**：`x ^ p = a`。 -/
theorem x_pow : x a b ζ ^ p = algebraMap K (SymbolAlg K p a b ζ) a := by
  have hrel : RingQuot.mkAlgHom K (rel K p a b ζ)
      (gen K 0 ^ p - algebraMap K (Fr K) a) = 0 := by
    have := RingQuot.mkAlgHom_rel (S := K) (s := rel K p a b ζ)
      (x := gen K 0 ^ p - algebraMap K (Fr K) a) (y := 0) (Or.inl ⟨rfl, rfl⟩)
    simpa using this
  rw [map_sub, map_pow, AlgHom.commutes, sub_eq_zero] at hrel
  have hx : x a b ζ = RingQuot.mkAlgHom K (rel K p a b ζ) (gen K 0) := rfl
  rw [hx]
  exact hrel

/-- **关系 2**：`y ^ p = b`。 -/
theorem y_pow : y a b ζ ^ p = algebraMap K (SymbolAlg K p a b ζ) b := by
  have hrel : RingQuot.mkAlgHom K (rel K p a b ζ)
      (gen K 1 ^ p - algebraMap K (Fr K) b) = 0 := by
    have := RingQuot.mkAlgHom_rel (S := K) (s := rel K p a b ζ)
      (x := gen K 1 ^ p - algebraMap K (Fr K) b) (y := 0) (Or.inr (Or.inl ⟨rfl, rfl⟩))
    simpa using this
  rw [map_sub, map_pow, AlgHom.commutes, sub_eq_zero] at hrel
  have hy : y a b ζ = RingQuot.mkAlgHom K (rel K p a b ζ) (gen K 1) := rfl
  rw [hy]
  exact hrel

/-- **关系 3**：`y * x = ζ • (x * y)`（即 `yx = ζ_p xy`）。 -/
theorem y_mul_x : y a b ζ * x a b ζ
    = algebraMap K (SymbolAlg K p a b ζ) ζ * (x a b ζ * y a b ζ) := by
  have hrel : RingQuot.mkAlgHom K (rel K p a b ζ)
      (gen K 1 * gen K 0 - algebraMap K (Fr K) ζ * (gen K 0 * gen K 1)) = 0 := by
    have := RingQuot.mkAlgHom_rel (S := K) (s := rel K p a b ζ)
      (x := gen K 1 * gen K 0 - algebraMap K (Fr K) ζ * (gen K 0 * gen K 1)) (y := 0)
      (Or.inr (Or.inr ⟨rfl, rfl⟩))
    simpa using this
  rw [map_sub, map_mul, map_mul, map_mul, AlgHom.commutes, sub_eq_zero] at hrel
  have hx : x a b ζ = RingQuot.mkAlgHom K (rel K p a b ζ) (gen K 0) := rfl
  have hy : y a b ζ = RingQuot.mkAlgHom K (rel K p a b ζ) (gen K 1) := rfl
  rw [hx, hy]
  exact hrel

/-- `SymbolAlg` 由两个生成元生成（`RingQuot` 的满射性 ＋ `FreeAlgebra.adjoin_range_ι`）。 -/
theorem adjoin_eq_top : Algebra.adjoin K ({x a b ζ, y a b ζ} : Set (SymbolAlg K p a b ζ)) = ⊤ := by
  classical
  rw [Algebra.eq_top_iff]
  intro z
  obtain ⟨w, rfl⟩ := RingQuot.mkAlgHom_surjective K (rel K p a b ζ) z
  have hgen : Algebra.adjoin K (Set.range (gen K : Fin 2 → Fr K)) = ⊤ :=
    FreeAlgebra.adjoin_range_ι K (Fin 2)
  have hsub : Algebra.adjoin K (Set.range (gen K : Fin 2 → Fr K)) ≤
      Subalgebra.comap (RingQuot.mkAlgHom K (rel K p a b ζ))
        (Algebra.adjoin K ({x a b ζ, y a b ζ} : Set (SymbolAlg K p a b ζ))) := by
    refine Algebra.adjoin_le (fun u hu => ?_)
    obtain ⟨i, rfl⟩ := hu
    refine (Subalgebra.mem_comap _ _ _).mpr ?_
    fin_cases i
    · show RingQuot.mkAlgHom K (rel K p a b ζ) (gen K 0) ∈
        Algebra.adjoin K ({x a b ζ, y a b ζ} : Set (SymbolAlg K p a b ζ))
      rw [show RingQuot.mkAlgHom K (rel K p a b ζ) (gen K 0) = x a b ζ from rfl]
      exact Algebra.subset_adjoin (by simp)
    · show RingQuot.mkAlgHom K (rel K p a b ζ) (gen K 1) ∈
        Algebra.adjoin K ({x a b ζ, y a b ζ} : Set (SymbolAlg K p a b ζ))
      rw [show RingQuot.mkAlgHom K (rel K p a b ζ) (gen K 1) = y a b ζ from rfl]
      exact Algebra.subset_adjoin (by simp)
  have hw : w ∈ Algebra.adjoin K (Set.range (gen K : Fin 2 → Fr K)) := by
    rw [hgen]; simp
  exact (Subalgebra.mem_comap _ _ _).mp (hsub hw)

/-! ### 交换关系 `y^n x^m = ζ^{nm} x^m y^n` -/

/-- 关系 3 的点积形式：`y x = ζ • (x y)`。 -/
theorem y_mul_x_smul :
    y a b ζ * (x a b ζ : SymbolAlg K p a b ζ) = ζ • (x a b ζ * y a b ζ) := by
  rw [y_mul_x, Algebra.smul_def]

/-- `y x^m = ζ^m • (x^m y)`。 -/
theorem y_mul_x_pow (m : ℕ) :
    y a b ζ * x a b ζ ^ m = (ζ ^ m) • ((x a b ζ : SymbolAlg K p a b ζ) ^ m * y a b ζ) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    calc y a b ζ * (x a b ζ ^ k * x a b ζ)
        = (y a b ζ * x a b ζ ^ k) * x a b ζ := (mul_assoc _ _ _).symm
      _ = ((ζ ^ k) • (x a b ζ ^ k * y a b ζ)) * x a b ζ := by rw [ih]
      _ = (ζ ^ k) • ((x a b ζ ^ k * y a b ζ) * x a b ζ) := smul_mul_assoc _ _ _
      _ = (ζ ^ k) • (x a b ζ ^ k * (y a b ζ * x a b ζ)) := by rw [mul_assoc]
      _ = (ζ ^ k) • (x a b ζ ^ k * (ζ • (x a b ζ * y a b ζ))) := by rw [y_mul_x_smul]
      _ = (ζ ^ k) • (ζ • (x a b ζ ^ k * (x a b ζ * y a b ζ))) := by rw [mul_smul_comm]
      _ = (ζ ^ k * ζ) • (x a b ζ ^ k * (x a b ζ * y a b ζ)) := smul_smul _ _ _
      _ = (ζ ^ k * ζ) • ((x a b ζ ^ k * x a b ζ) * y a b ζ) := by rw [mul_assoc]
      _ = (ζ ^ (k + 1)) • ((x a b ζ ^ k * x a b ζ) * y a b ζ) := by rw [pow_succ]

/-- `y^n x^m = ζ^{nm} • (x^m y^n)`。 -/
theorem y_pow_mul_x_pow (n m : ℕ) :
    y a b ζ ^ n * x a b ζ ^ m
      = (ζ ^ (n * m)) • ((x a b ζ : SymbolAlg K p a b ζ) ^ m * y a b ζ ^ n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    conv_lhs => rw [pow_succ]
    calc y a b ζ ^ k * y a b ζ * x a b ζ ^ m
        = y a b ζ ^ k * (y a b ζ * x a b ζ ^ m) := by rw [mul_assoc]
      _ = y a b ζ ^ k * ((ζ ^ m) • (x a b ζ ^ m * y a b ζ)) := by rw [y_mul_x_pow]
      _ = (ζ ^ m) • (y a b ζ ^ k * (x a b ζ ^ m * y a b ζ)) := mul_smul_comm _ _ _
      _ = (ζ ^ m) • ((y a b ζ ^ k * x a b ζ ^ m) * y a b ζ) := by rw [mul_assoc]
      _ = (ζ ^ m) • (((ζ ^ (k * m)) • (x a b ζ ^ m * y a b ζ ^ k)) * y a b ζ) := by rw [ih]
      _ = (ζ ^ m) • ((ζ ^ (k * m)) • ((x a b ζ ^ m * y a b ζ ^ k) * y a b ζ)) := by
            rw [smul_mul_assoc]
      _ = (ζ ^ m * ζ ^ (k * m)) • ((x a b ζ ^ m * y a b ζ ^ k) * y a b ζ) :=
            smul_smul _ _ _
      _ = (ζ ^ (k * m) * ζ ^ m) • ((x a b ζ ^ m * y a b ζ ^ k) * y a b ζ) := by rw [mul_comm]
      _ = (ζ ^ (k * m + m)) • ((x a b ζ ^ m * y a b ζ ^ k) * y a b ζ) := by rw [← pow_add]
      _ = (ζ ^ ((k + 1) * m)) • ((x a b ζ ^ m * y a b ζ ^ k) * y a b ζ) := by
            rw [Nat.succ_mul]
      _ = (ζ ^ ((k + 1) * m)) • (x a b ζ ^ m * y a b ζ ^ (k + 1)) := by
            rw [mul_assoc, ← pow_succ]

/-- `x^n = a^{⌊n/p⌋} • x^{n % p}`：把指数降到 `[0, p)`。 -/
theorem x_pow_eq_smul (hp : 0 < p) (n : ℕ) :
    x a b ζ ^ n = (a ^ (n / p)) • ((x a b ζ : SymbolAlg K p a b ζ) ^ (n % p)) := by
  have hn : p * (n / p) + n % p = n := Nat.div_add_mod n p
  conv_lhs => rw [← hn]
  rw [pow_add, pow_mul, x_pow, ← map_pow, ← Algebra.smul_def]

/-- `y^n = b^{⌊n/p⌋} • y^{n % p}`。 -/
theorem y_pow_eq_smul (hp : 0 < p) (n : ℕ) :
    y a b ζ ^ n = (b ^ (n / p)) • ((y a b ζ : SymbolAlg K p a b ζ) ^ (n % p)) := by
  have hn : p * (n / p) + n % p = n := Nat.div_add_mod n p
  conv_lhs => rw [← hn]
  rw [pow_add, pow_mul, y_pow, ← map_pow, ← Algebra.smul_def]

/-! ### 泛性质：从 `SymbolAlg` 出发的代数同态

呈现的全部用处都在这条：任何带两个元素 `X, Y` 满足三条关系的 `K`-代数都接收一个
`SymbolAlg →ₐ[K] B`。这是 `Hyp48` 之后把 `SymbolAlg` 与循环交叉积对上的唯一入口。 -/

/-- **泛性质**：`X, Y` 满足 `x^p, y^p, yx−ζxy` 三条关系 ⟹ 存在 `SymbolAlg →ₐ[K] B`。 -/
noncomputable def liftOf {B : Type*} [Ring B] [Algebra K B] (X Y : B)
    (h1 : X ^ p = algebraMap K B a) (h2 : Y ^ p = algebraMap K B b)
    (h3 : Y * X = algebraMap K B ζ * (X * Y)) :
    SymbolAlg K p a b ζ →ₐ[K] B :=
  RingQuot.liftAlgHom K ⟨FreeAlgebra.lift K (fun i : Fin 2 => if i = 0 then X else Y), by
    rintro u v (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simpa [gen, sub_eq_zero] using h1
    · simpa [gen, sub_eq_zero] using h2
    · simpa [gen, sub_eq_zero] using h3⟩

variable {a b ζ}

/-- 泛性质在第一个生成元上的取值。 -/
@[simp]
theorem liftOf_x {B : Type*} [Ring B] [Algebra K B] (X Y : B)
    (h1 : X ^ p = algebraMap K B a) (h2 : Y ^ p = algebraMap K B b)
    (h3 : Y * X = algebraMap K B ζ * (X * Y)) :
    liftOf (p := p) a b ζ X Y h1 h2 h3 (x a b ζ) = X := by
  rw [liftOf]
  change RingQuot.liftAlgHom K _ (RingQuot.mkAlgHom K (rel K p a b ζ)
    (FreeAlgebra.ι K (0 : Fin 2))) = X
  rw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
  rfl

/-- 泛性质在第二个生成元上的取值。 -/
@[simp]
theorem liftOf_y {B : Type*} [Ring B] [Algebra K B] (X Y : B)
    (h1 : X ^ p = algebraMap K B a) (h2 : Y ^ p = algebraMap K B b)
    (h3 : Y * X = algebraMap K B ζ * (X * Y)) :
    liftOf (p := p) a b ζ X Y h1 h2 h3 (y a b ζ) = Y := by
  rw [liftOf]
  change RingQuot.liftAlgHom K _ (RingQuot.mkAlgHom K (rel K p a b ζ)
    (FreeAlgebra.ι K (1 : Fin 2))) = Y
  rw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
  rfl

/-! ### `{x^i y^j}_{i,j<p}` 张成整个 `SymbolAlg`（呈现的「正规形」） -/

/-- 两个指数都 `< p` 的单项式集合 `{x^i y^j}`。 -/
def monomials (a b ζ : K) : Set (SymbolAlg K p a b ζ) :=
  {z | ∃ i j : ℕ, i < p ∧ j < p ∧ z = x a b ζ ^ i * y a b ζ ^ j}

/-- 重组引理 `A B (C D) = A (B C) D`（非交换环里没有 `mul_mul_mul_comm`）。 -/
private theorem reassoc (A B C D : SymbolAlg K p a b ζ) :
    A * B * (C * D) = A * (B * C) * D := by
  rw [mul_assoc A B (C * D), ← mul_assoc B C D, ← mul_assoc A (B * C) D]

/-- **单项式乘以单项式**：结果是 `ζ^{jk} a^{⌊(i+k)/p⌋} b^{⌊(j+l)/p⌋}` 倍的
`x^{(i+k) mod p} y^{(j+l) mod p}`，故仍在单项式张成的子模里。 -/
theorem monomial_mul_monomial (hp : 0 < p) {u v : SymbolAlg K p a b ζ}
    (hu : u ∈ monomials (p := p) a b ζ) (hv : v ∈ monomials (p := p) a b ζ) :
    u * v ∈ Submodule.span K (monomials (p := p) a b ζ) := by
  obtain ⟨i, j, -, -, rfl⟩ := hu
  obtain ⟨k, l, -, -, rfl⟩ := hv
  -- 先把 `y^j` 移过 `x^k`
  have hstep : (x a b ζ : SymbolAlg K p a b ζ) ^ i * y a b ζ ^ j *
      (x a b ζ ^ k * y a b ζ ^ l)
      = (ζ ^ (j * k)) • (x a b ζ ^ (i + k) * y a b ζ ^ (j + l)) := by
    rw [reassoc, y_pow_mul_x_pow, mul_smul_comm, smul_mul_assoc, ← mul_assoc, ← pow_add,
      mul_assoc, ← pow_add]
  -- 再把两个指数各自降到 `[0, p)`
  have hred : (ζ ^ (j * k)) • (x a b ζ ^ (i + k) * y a b ζ ^ (j + l))
      = (ζ ^ (j * k) * a ^ ((i + k) / p) * b ^ ((j + l) / p)) •
        ((x a b ζ : SymbolAlg K p a b ζ) ^ ((i + k) % p) * y a b ζ ^ ((j + l) % p)) := by
    rw [x_pow_eq_smul (a := a) (b := b) (ζ := ζ) hp,
      y_pow_eq_smul (a := a) (b := b) (ζ := ζ) hp]
    rw [smul_mul_smul, smul_smul, mul_assoc]
  rw [hstep, hred]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨_, _, Nat.mod_lt _ hp, Nat.mod_lt _ hp, rfl⟩

/-- 单项式张成的子模对乘法封闭。 -/
theorem mul_mem_span (hp : 0 < p) {u v : SymbolAlg K p a b ζ}
    (hu : u ∈ Submodule.span K (monomials (p := p) a b ζ))
    (hv : v ∈ Submodule.span K (monomials (p := p) a b ζ)) :
    u * v ∈ Submodule.span K (monomials (p := p) a b ζ) := by
  classical
  -- 先对 `u` 归纳（`v` 固定）
  have key : ∀ u ∈ Submodule.span K (monomials (p := p) a b ζ),
      ∀ v ∈ Submodule.span K (monomials (p := p) a b ζ),
      u * v ∈ Submodule.span K (monomials (p := p) a b ζ) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem m hm =>
      intro v hv
      induction hv using Submodule.span_induction with
      | mem n hn => exact monomial_mul_monomial (a := a) (b := b) (ζ := ζ) hp hm hn
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
    | zero => intro v _; rw [zero_mul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => intro v hv; rw [add_mul]; exact Submodule.add_mem _ (hx v hv) (hy v hv)
    | smul c x _ hx => intro v hv; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ (hx v hv)
  exact key u hu v hv

/-- 单项式张成的子模是一个子代数。 -/
noncomputable def monomialSubalgebra (hp : 0 < p) : Subalgebra K (SymbolAlg K p a b ζ) where
  carrier := Submodule.span K (monomials (p := p) a b ζ)
  add_mem' := fun hx hy => Submodule.add_mem _ hx hy
  zero_mem' := Submodule.zero_mem _
  mul_mem' := fun hx hy => mul_mem_span (a := a) (b := b) (ζ := ζ) hp hx hy
  one_mem' := by
    have h : (1 : SymbolAlg K p a b ζ) = x a b ζ ^ 0 * y a b ζ ^ 0 := by simp
    rw [h]
    exact Submodule.subset_span ⟨0, 0, hp, hp, rfl⟩
  algebraMap_mem' := fun c => by
    rw [Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ _ ?_
    have h : (1 : SymbolAlg K p a b ζ) = x a b ζ ^ 0 * y a b ζ ^ 0 := by simp
    rw [h]
    exact Submodule.subset_span ⟨0, 0, hp, hp, rfl⟩

/-- **呈现的「正规形」**：`SymbolAlg` 由 `{x^i y^j}_{i,j<p}` 线性张成。 -/
theorem span_monomials_eq_top (hp : 1 < p) :
    Submodule.span K (monomials (p := p) a b ζ) = ⊤ := by
  have hp0 : 0 < p := Nat.zero_lt_of_lt hp
  refine le_antisymm le_top (fun z _ => ?_)
  have h1 : Algebra.adjoin K ({x a b ζ, y a b ζ} : Set (SymbolAlg K p a b ζ))
      ≤ monomialSubalgebra (p := p) (a := a) (b := b) (ζ := ζ) hp0 := by
    refine Algebra.adjoin_le ?_
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · have h : (x a b ζ : SymbolAlg K p a b ζ) = x a b ζ ^ 1 * y a b ζ ^ 0 := by simp
      rw [h]
      refine Submodule.subset_span ?_
      exact ⟨1, 0, hp, hp0, rfl⟩
    · have h : (y a b ζ : SymbolAlg K p a b ζ) = x a b ζ ^ 0 * y a b ζ ^ 1 := by simp
      rw [h]
      refine Submodule.subset_span ?_
      exact ⟨0, 1, hp0, hp, rfl⟩
  have h2 : (⊤ : Subalgebra K (SymbolAlg K p a b ζ))
      ≤ monomialSubalgebra (p := p) (a := a) (b := b) (ζ := ζ) hp0 := by
    rw [← adjoin_eq_top a b ζ]
    exact h1
  exact h2 (by simp)

/-- 单项式给出的线性满射 `(Fin p × Fin p →₀ K) ↠ SymbolAlg`。 -/
theorem linearCombination_surjective (hp : 1 < p) :
    Function.Surjective
      (Finsupp.linearCombination K
        (fun ij : Fin p × Fin p =>
          (x a b ζ : SymbolAlg K p a b ζ) ^ (ij.1 : ℕ) * y a b ζ ^ (ij.2 : ℕ))) := by
  classical
  have hspan := span_monomials_eq_top (p := p) (a := a) (b := b) (ζ := ζ) hp
  intro z
  have hz : z ∈ Submodule.span K (Set.range (fun ij : Fin p × Fin p =>
      (x a b ζ : SymbolAlg K p a b ζ) ^ (ij.1 : ℕ) * y a b ζ ^ (ij.2 : ℕ))) := by
    rw [show Set.range (fun ij : Fin p × Fin p =>
          (x a b ζ : SymbolAlg K p a b ζ) ^ (ij.1 : ℕ) * y a b ζ ^ (ij.2 : ℕ))
        = monomials (p := p) a b ζ from ?_]
    · rw [hspan]; exact Submodule.mem_top
    · ext w
      constructor
      · rintro ⟨⟨i, j⟩, rfl⟩
        exact ⟨i, j, i.2, j.2, rfl⟩
      · rintro ⟨i, j, hi, hj, rfl⟩
        exact ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, rfl⟩
  have hmem : z ∈ LinearMap.range (Finsupp.linearCombination K
      (fun ij : Fin p × Fin p =>
        (x a b ζ : SymbolAlg K p a b ζ) ^ (ij.1 : ℕ) * y a b ζ ^ (ij.2 : ℕ))) := by
    rw [Finsupp.range_linearCombination]
    exact hz
  exact LinearMap.mem_range.mp hmem

/-- `SymbolAlg` 是有限维 `K`-代数（由 `p²` 个单项式张成）。 -/
theorem finiteDimensional (hp : 1 < p) : FiniteDimensional K (SymbolAlg K p a b ζ) :=
  Module.Finite.of_surjective _
    (linearCombination_surjective (p := p) (a := a) (b := b) (ζ := ζ) hp)

/-- **推论**：`(a,b)_ζ` 的 `K`-维数不超过 `p²`。 -/
theorem finrank_le (hp : 1 < p) :
    Module.finrank K (SymbolAlg K p a b ζ) ≤ p * p := by
  classical
  have h := LinearMap.finrank_le_finrank_of_surjective
    (linearCombination_surjective (p := p) (a := a) (b := b) (ζ := ζ) hp)
  rwa [Module.finrank_finsupp_self, Fintype.card_prod, Fintype.card_fin] at h

/-- **维数桥（本文件的主接口）**：若 `B` 中有一对满足三条关系的元素 `X, Y`，且
`liftOf X Y` 满射、`finrank B = p²`，则 `SymbolAlg ≅ B`。

这是 `def:decomposable` 里「呈现 = 循环代数」那一步的**通用收口器**：只需给出 `X, Y`
与维数，不必再碰自由代数。（`p = 2` 的对应物见 TauCeti `CrossedProduct/Quaternion.lean`
的 `nonempty_quaternionAlgebra_algEquiv_quadratic`。） -/
theorem nonempty_algEquiv_of_finrank {B : Type*} [Ring B] [Algebra K B]
    [FiniteDimensional K B] (hp : 1 < p) (X Y : B)
    (h1 : X ^ p = algebraMap K B a) (h2 : Y ^ p = algebraMap K B b)
    (h3 : Y * X = algebraMap K B ζ * (X * Y))
    (hsurj : Function.Surjective (liftOf (p := p) a b ζ X Y h1 h2 h3))
    (hdim : Module.finrank K B = p * p) :
    Nonempty (SymbolAlg K p a b ζ ≃ₐ[K] B) := by
  classical
  haveI := finiteDimensional (p := p) (a := a) (b := b) (ζ := ζ) hp
  have hle : Module.finrank K (SymbolAlg K p a b ζ) ≤ Module.finrank K B := by
    rw [hdim]
    exact finrank_le (p := p) (a := a) (b := b) (ζ := ζ) hp
  have hsurj' : Function.Surjective (liftOf (p := p) a b ζ X Y h1 h2 h3).toLinearMap := hsurj
  have hge : Module.finrank K B ≤ Module.finrank K (SymbolAlg K p a b ζ) :=
    LinearMap.finrank_le_finrank_of_surjective hsurj'
  have heq : Module.finrank K (SymbolAlg K p a b ζ) = Module.finrank K B :=
    le_antisymm hle hge
  have hinj : Function.Injective (liftOf (p := p) a b ζ X Y h1 h2 h3) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (liftOf (p := p) a b ζ X Y h1 h2 h3).toLinearMap) heq).mpr hsurj
  exact ⟨AlgEquiv.ofBijective _ ⟨hinj, hsurj⟩⟩

/-! ### 两支认同共用的两个接口 -/

section Dict

/-- **满射性判据**：若 `X, Y` 生成 `B`，则 `liftOf X Y` 满射。
（两支认同都只需证「生成」＋「`finrank = p²`」。） -/
theorem liftOf_surjective_of_adjoin_eq_top {B : Type*} [Ring B] [Algebra K B]
    (X Y : B) (h1 : X ^ p = algebraMap K B a) (h2 : Y ^ p = algebraMap K B b)
    (h3 : Y * X = algebraMap K B ζ * (X * Y))
    (hgen : Algebra.adjoin K ({X, Y} : Set B) = ⊤) :
    Function.Surjective (liftOf (p := p) a b ζ X Y h1 h2 h3) := by
  intro z
  have hz : z ∈ Algebra.adjoin K ({X, Y} : Set B) := by rw [hgen]; trivial
  have hsub : Algebra.adjoin K ({X, Y} : Set B) ≤ (liftOf (p := p) a b ζ X Y h1 h2 h3).range := by
    refine Algebra.adjoin_le ?_
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact ⟨x a b ζ, by simp⟩
    · exact ⟨y a b ζ, by simp⟩
  exact hsub hz

/-- 从呈现到呈现的同态由生成元的像决定。 -/
theorem hom_ext {B : Type*} [Ring B] [Algebra K B] {f g : SymbolAlg K p a b ζ →ₐ[K] B}
    (hx : f (x a b ζ) = g (x a b ζ)) (hy : f (y a b ζ) = g (y a b ζ)) : f = g := by
  refine RingQuot.ringQuot_ext' K f g (FreeAlgebra.hom_ext ?_)
  funext i
  fin_cases i
  · simpa [gen, x] using hx
  · simpa [gen, y] using hy

end Dict

end SymbolAlg

end SymbolPres
