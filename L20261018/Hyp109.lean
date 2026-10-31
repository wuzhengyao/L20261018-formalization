import Hyp108

/-!
# 第 4 章 T2（抽象层）：`ResidueCupData` —— §2.4 工具的形状 —— 与 T3 的抽象内核

论文 §4 的两条主结果（`lem:ramified-vanishing` 4.2、`thm:ramified` 4.3）的证明
（`raw/L20261018.tex:1611–1624`）**只**用到第二章 2.4 的三条工具：

* `prop:prelim-kummer-valuation`：$x=\inf(x_0)+m(\pi)$ 的**赋值分解**，且
  $0\to H^1(K,\mu_p)\to H^1(F,\mu_p)\to\Fp\to0$ **分裂正合**
  （⇒ `infl` 单射、$v\circ\inf=0$、$v(\pi)=1$）；
* `prop:prelim-residue` 的**驯符号公式** `eq:prelim-tame`：$\partial_2((a)\cup(b))=(-1)^{v(a)v(b)}(a^{v(b)}b^{-v(a)})$，
  在证明里只以**三处特化**出现（`tame_uu`／`tame_u_pi`／`tame_pi_u`）；
* 双线性／斜对称（`prop:prelim-cup`）。

本文件把这三条打包成 `ResidueCupData`（Route B：**具名假设**，见 `PROMPT-CH4` §7 T2／§8(甲)），
并在这一层机检 T3 的**完整数学内核**。论文层（真实 `GaloBase.cup`／`H¹(F,μ_p)`）见
`Hyp110`；本层是它的**证明主体**，不是替代品。

## 论文证明与 Lean 步骤的对应（`:1611–1624`）

| 论文 | Lean |
|---|---|
| 取基 $(\pi u),(c)$，$u,c\in\mathcal O_F^\times$ | `hval` 给 $u\in U$ 且 $v(u)\ne0$，`hu_def` 归一化成 $v(u)=1$ |
| $x=(w)+k(\pi)$ | `D.split x` 给 $x=\inf x_0+m_x\pi$ |
| $0=\partial_2((c)\cup x)=k(\bar c)\Rightarrow k=0$ | `hexp`＋`hzero`：$\mathrm{res}(\cup xu)=x_0-m_x u_1=0$ |
| $0=\partial_2((\pi u)\cup(w))=-(\bar w)$ | `hexp` 里的 `tame_pi_u` 那一项 |
| Hensel ⟹ $w=(yz)^p$ ⟹ $x=0$ | 结论 $x=m_x\cdot u\in U$，再 $U\cap U^\perp=0$ |

> **为什么 Hensel 不显式出现**：论文「$w=(yz)^p$」这一步正是 `prop:prelim-kummer-valuation`
> 的赋值分解与「$\bar w=0\Rightarrow(w)=0$」的等价，已被 `split`／`val_infl` 两条**吸收**
> 到具名假设里；Hensel 性本身是 `Hyp110` 层的事。

## 非空见证

`toyResidueCupData`：$k=\Z/3$、$V=k^2$（标准辛形式）、$V_K=k$、$\inf y=(y,0)$、$\pi=(0,1)$、
$v(x)=x_2$、$\mathrm{res}=\mathrm{id}$。**所有字段逐条机检**，且论文假设
（$(\alpha_1)\cup(\alpha_2)\ne0$ 与 $\bar v|_U\ne0$）在该模型上**可实现**（`toy_hypotheses`），
定理本身在模型上**执行**一次（`toy_vanishing`）。
-/

set_option maxHeartbeats 2000000

namespace L20261018

/-- **§2.4 工具的抽象形态（Route B 具名假设）**。

`cup` 是论文的杯积 `H¹(F,μ_p) × H¹(F,μ_p) → H²(F,μ_p)`，`res` 是二阶剩余映射
`H²(F,μ_p) → H¹(K,μ_p)`，`val` 是模 `p` 赋值 `\bar v`，`infl` 是剩余域的膨胀，
`pi` 是素元的 Kummer 类。`tame_*` 三条是驯符号公式 `eq:prelim-tame` 的三处特化。 -/
structure ResidueCupData (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V]
    (H2 : Type*) [AddCommGroup H2] [Module k H2]
    (VK : Type*) [AddCommGroup VK] [Module k VK] where
  /-- 论文的杯积 `∪`。 -/
  cup : V →ₗ[k] V →ₗ[k] H2
  /-- `prop:prelim-cup` 的斜对称性。 -/
  skew : ∀ x y, cup x y = - cup y x
  /-- 二阶剩余映射 `∂`（`H²(F,μ_p) → H¹(K,μ_p)`）。 -/
  res : H2 →ₗ[k] VK
  /-- 模 `p` 赋值 `\bar v : H¹(F,μ_p) → F_p`（`prop:prelim-kummer-valuation`）。 -/
  val : V →ₗ[k] k
  /-- 剩余域的膨胀 `H¹(K,μ_p) → H¹(F,μ_p)`（正合列的第一段）。 -/
  infl : VK →ₗ[k] V
  /-- 正合列 `0 → H¹(K,μ_p) → H¹(F,μ_p) → F_p → 0` 左端的单射性。 -/
  inj_infl : Function.Injective infl
  /-- 膨胀的像落在赋值 `0` 的层（`v ∘ inf = 0`）。 -/
  val_infl : ∀ y : VK, val (infl y) = 0
  /-- 素元的 Kummer 类 `(π)`。 -/
  pi : V
  /-- `v(π) = 1`。 -/
  val_pi : val pi = 1
  /-- 赋值分解 `x = inf x₀ + m·(π)`。 -/
  split : ∀ x : V, ∃ (x₀ : VK) (m : k), x = infl x₀ + m • pi
  /-- 驯符号：两个单位类之间的杯积剩余为 `0`（`v(a)=v(b)=0`）。 -/
  tame_uu : ∀ y z : VK, res (cup (infl y) (infl z)) = 0
  /-- 驯符号：`∂₂((unit)∪(π)) = (unit)`（`v(a)=0`、`v(b)=1`）。 -/
  tame_u_pi : ∀ y : VK, res (cup (infl y) pi) = y
  /-- 驯符号：`v(κ)=1` 时 `∂₂((κ)∪(unit)) = -(unit)`（`eq:prelim-tame` 的 `-1` 次幂）。 -/
  tame_pi_u : ∀ (κ : V), val κ = 1 → ∀ z : VK, res (cup κ (infl z)) = -z

namespace ResidueCupData

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]
variable {VK : Type*} [AddCommGroup VK] [Module k VK]

/-! ## 记号（与 `A.BiKummerData` 的 `U`／`Φ`／`U^⊥` 同形，此处按 `a₁ a₂` 参数化） -/

/-- 第一槽平面 `U = span{α₁,α₂}`（论文的 `U`）。 -/
def plane (a1 a2 : V) : Submodule k V := Submodule.span k {a1, a2}

/-- 共同杯积映射 `Φ x = (x∪a₁, x∪a₂)`。 -/
def commonCupMap (cup : V →ₗ[k] V →ₗ[k] H2) (a1 a2 : V) : V →ₗ[k] H2 × H2 where
  toFun x := (cup x a1, cup x a2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- 共同正交空间 `U^⊥ = ker Φ`。 -/
def orth (cup : V →ₗ[k] V →ₗ[k] H2) (a1 a2 : V) : Submodule k V :=
  LinearMap.ker (commonCupMap cup a1 a2)

@[simp] lemma commonCupMap_apply (cup : V →ₗ[k] V →ₗ[k] H2) (a1 a2 x : V) :
    commonCupMap cup a1 a2 x = (cup x a1, cup x a2) := rfl

lemma mem_plane_iff (a1 a2 x : V) :
    x ∈ plane (k := k) a1 a2 ↔ ∃ c1 c2 : k, c1 • a1 + c2 • a2 = x := by
  rw [plane, Submodule.mem_span_pair]

lemma mem_orth_iff (cup : V →ₗ[k] V →ₗ[k] H2) (a1 a2 x : V) :
    x ∈ orth cup a1 a2 ↔ cup x a1 = 0 ∧ cup x a2 = 0 := by
  rw [orth, LinearMap.mem_ker, commonCupMap_apply, Prod.mk_eq_zero]

/-! ## 基本引理 -/

section Basic

variable [NeZero (2 : k)]
variable (D : ResidueCupData k V H2 VK)

/-- 特征 $\ne2$ 下斜对称 ⟹ 交错（同 `A.BiKummerData.alt'`）。 -/
lemma alt (x : V) : D.cup x x = 0 := by
  have h : D.cup x x = - D.cup x x := D.skew x x
  have h2 : (2 : k) • D.cup x x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    abel
  exact (smul_eq_zero.mp h2).resolve_left (NeZero.ne (2 : k))

/-- **`U ∩ U^⊥ = 0`**（论文 3.1(1) 的同一论证，此处按 `a₁ a₂` 参数化）：
`c₁a₁+c₂a₂ ∈ U^⊥` ⟹ `c₂h = 0` 与 `c₁h = 0`（`h = a₁∪a₂ ≠ 0`）。 -/
lemma U_inf_Uperp (a1 a2 : V) (hne : D.cup a1 a2 ≠ 0) :
    plane (k := k) a1 a2 ⊓ orth D.cup a1 a2 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvU, hvP⟩ := hv
  obtain ⟨c1, c2, hvc⟩ := mem_plane_iff (k := k) a1 a2 v |>.mp hvU
  have hP := mem_orth_iff (k := k) D.cup a1 a2 v |>.mp hvP
  have h1 : D.cup (c1 • a1 + c2 • a2) a1 = 0 := by rw [hvc]; exact hP.1
  have h2 : D.cup (c1 • a1 + c2 • a2) a2 = 0 := by rw [hvc]; exact hP.2
  have e1 : D.cup (c1 • a1 + c2 • a2) a1 = -(c2 • D.cup a1 a2) := by
    simp [map_add, map_smul, D.alt a1, D.skew a1 a2, smul_neg]
  have e2 : D.cup (c1 • a1 + c2 • a2) a2 = c1 • D.cup a1 a2 := by
    simp [map_add, map_smul, D.alt a2]
  have hc2 : c2 = 0 := by
    rw [e1] at h1
    have : c2 • D.cup a1 a2 = 0 := by simpa using h1
    exact (smul_eq_zero.mp this).resolve_right hne
  have hc1 : c1 = 0 := by
    rw [e2] at h2
    exact (smul_eq_zero.mp h2).resolve_right hne
  rw [Submodule.mem_bot, ← hvc, hc1, hc2]
  simp

/-- **T3 抽象版（= `lem:ramified-vanishing` 的数学内核）**：
若 `\bar v` 在第一槽平面 `U = span{α₁,α₂}` 上非零，则 `U^⊥ = 0`。 -/
-- @source file=raw/L20261018.tex locator=label:lem:ramified-vanishing quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem vanishing (a1 a2 : V) (hne : D.cup a1 a2 ≠ 0)
    (hval : ∃ u ∈ plane (k := k) a1 a2, D.val u ≠ 0) :
    orth D.cup a1 a2 = ⊥ := by
  classical
  obtain ⟨u₀, hu₀U, hu₀ne⟩ := hval
  -- 第一步：把 `u₀` 归一化成 `v(u) = 1`
  set u : V := (D.val u₀)⁻¹ • u₀ with hu_def
  have huU : u ∈ plane (k := k) a1 a2 := Submodule.smul_mem _ _ hu₀U
  have hvalu : D.val u = 1 := by
    rw [hu_def, map_smul, smul_eq_mul, inv_mul_cancel₀ hu₀ne]
  -- 第二步：`u = inf u₁ + π`（赋值的加性给 `m = 1`）
  obtain ⟨u₁, m, hum⟩ := D.split u
  have hmval : D.val (D.infl u₁ + m • D.pi) = m := by
    rw [map_add, map_smul, D.val_infl, zero_add, D.val_pi, smul_eq_mul, mul_one]
  have hvalm : m = 1 := by
    have h : D.val u = m := by rw [hum, hmval]
    rw [hvalu] at h
    exact h.symm
  have hu_eq : u = D.infl u₁ + D.pi := by rw [hum, hvalm, one_smul]
  rw [eq_bot_iff]
  intro x hx
  -- 第三步：`x = inf x₀ + m_x·π`
  obtain ⟨x₀, mx, hxm⟩ := D.split x
  -- `x ∈ U^⊥` ⟹ `∪ x ·` 杀死整个 `U`
  have hx12 := mem_orth_iff (k := k) D.cup a1 a2 x |>.mp hx
  have hkill : ∀ v ∈ plane (k := k) a1 a2, D.cup x v = 0 := by
    intro v hv
    obtain ⟨c1, c2, rfl⟩ := mem_plane_iff (k := k) a1 a2 v |>.mp hv
    rw [map_add, map_smul, map_smul, hx12.1, hx12.2, smul_zero, smul_zero, add_zero]
  have hcu : D.cup x u = 0 := hkill u huU
  -- 第四步：两侧展开后比较剩余 —— 论文 `:1616–1623` 的两条驯符号计算
  have hexp : D.res (D.cup x u) = x₀ - mx • u₁ := by
    conv_lhs => rw [hxm, hu_eq]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    rw [D.tame_uu x₀ u₁, D.tame_u_pi x₀, D.tame_pi_u D.pi D.val_pi u₁, D.alt D.pi,
      map_zero, smul_zero, add_zero]
    module
  have hzero : D.res (D.cup x u) = 0 := by rw [hcu, map_zero]
  -- 第五步：`x₀ = m_x • u₁` ⟹ `x = m_x • u ∈ U` ⟹ `x ∈ U ∩ U^⊥ = 0`
  have hx0 : x₀ = mx • u₁ := by
    have h : x₀ - mx • u₁ = 0 := by rw [← hexp, hzero]
    exact sub_eq_zero.mp h
  have hxu : x = mx • u := by
    rw [hxm, hx0, map_smul, ← smul_add, ← hu_eq]
  have hxU : x ∈ plane (k := k) a1 a2 := by
    rw [hxu]
    exact Submodule.smul_mem _ _ huU
  have hbot : x ∈ (⊥ : Submodule k V) := by
    have h := D.U_inf_Uperp a1 a2 hne
    rw [eq_bot_iff] at h
    exact h ⟨hxU, hx⟩
  simpa using hbot

end Basic

/-! ## 非空见证（toy model：$k=\Z/3$ 上的辛平面） -/

section Toy

/-- 模型：`V = ZMod 3 × ZMod 3` 上的标准辛形式，`VK = ZMod 3`，`infl` 到第一坐标，
`pi = (0,1)`，`val` 取第二坐标，`res = id`。 -/
noncomputable def toyResidueCupData :
    ResidueCupData (ZMod 3) (ZMod 3 × ZMod 3) (ZMod 3) (ZMod 3) where
  cup := LinearMap.mk₂ (ZMod 3)
    (fun x y : ZMod 3 × ZMod 3 => x.1 * y.2 - x.2 * y.1)
    (by intro x y z; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intro c x y; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (by intro x y z; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intro c x y; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
  skew := by
    intro x y
    simp only [LinearMap.mk₂_apply]
    ring
  res := LinearMap.id
  val := LinearMap.snd (ZMod 3) (ZMod 3) (ZMod 3)
  infl := LinearMap.inl (ZMod 3) (ZMod 3) (ZMod 3)
  inj_infl := by
    intro a b h
    simpa using h
  val_infl := by
    intro y
    rfl
  pi := (0, 1)
  val_pi := rfl
  split := by
    intro x
    exact ⟨x.1, x.2, by ext <;> simp⟩
  tame_uu := by
    intro y z
    simp only [LinearMap.mk₂_apply, LinearMap.inl_apply, LinearMap.id_apply]
    ring
  tame_u_pi := by
    intro y
    simp only [LinearMap.mk₂_apply, LinearMap.inl_apply, LinearMap.id_apply]
    ring
  tame_pi_u := by
    intro κ hκ z
    simp only [LinearMap.snd_apply, LinearMap.id_apply] at hκ ⊢
    simp only [LinearMap.mk₂_apply, LinearMap.inl_apply]
    rw [hκ]
    ring

instance : NeZero (2 : ZMod 3) := ⟨by decide⟩

/-- 论文假设在 toy model 上**可实现**：`α₁ = (1,0)`、`α₂ = (0,1)` ⟹
`(α₁)∪(α₂) = 1 ≠ 0`（`hne`）且 `\bar v|_U` 非零（`hval`）。 -/
theorem toy_hypotheses :
    toyResidueCupData.cup (1, 0) (0, 1) ≠ 0 ∧
      ∃ u ∈ plane (k := ZMod 3) (1, 0) (0, 1), toyResidueCupData.val u ≠ 0 := by
  constructor
  · simp only [toyResidueCupData, LinearMap.mk₂_apply]
    decide
  · refine ⟨(0, 1), ?_, ?_⟩
    · rw [ResidueCupData.mem_plane_iff]
      exact ⟨0, 1, by simp⟩
    · simp only [toyResidueCupData, LinearMap.snd_apply]
      decide

/-- 定理在 toy model 上**执行**（非空洞性的直接展示）。 -/
theorem toy_vanishing :
    orth toyResidueCupData.cup (1, 0) (0, 1) = ⊥ := by
  refine toyResidueCupData.vanishing (1, 0) (0, 1) ?_ ?_
  · simp only [toyResidueCupData, LinearMap.mk₂_apply]
    decide
  · refine ⟨(0, 1), ?_, ?_⟩
    · rw [ResidueCupData.mem_plane_iff]
      exact ⟨0, 1, by simp⟩
    · simp only [toyResidueCupData, LinearMap.snd_apply]
      decide

end Toy

end ResidueCupData

end L20261018

#print axioms L20261018.ResidueCupData.alt
#print axioms L20261018.ResidueCupData.U_inf_Uperp
#print axioms L20261018.ResidueCupData.vanishing
#print axioms L20261018.ResidueCupData.toy_hypotheses
#print axioms L20261018.ResidueCupData.toy_vanishing
