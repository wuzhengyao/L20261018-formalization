import L20261018.Hyp690
import L20261018.Hyp687

/-!
# S61 R4：**(G2) 的收口形态** —— `Ch4TameSymbolHyp` 由**论文自引的 Merkurjev–Suslin** 推出

## 这一步在做什么

`G2-PLAN.md` §4 预注册的**成功结局**是：

> A4 记 `∅-open`，(G2) 结项为「**已把缺口压到一条已命名的已发表定理**」。

本件就是那个形态。A1–A3 已全绿（`Hyp688`／`Hyp689`／`Hyp690`），本件把它们**组装**成

```
ker(∪) ⊆ Steinberg 生成元张成的子空间          （＝论文 `thm:prelim-ms`，Merkurjev–Suslin）
  ⟹  ker(∪) ⊆ ker(tame)                       （A2＋A3＋线性）
  ⟹  TameSymbolFactors                          （A1 ＝ Hyp689）
```

⟹ **`(G2)` 的残余不再是一条关于 `∂₂` 存在性的不透明假设（`Ch4TameSymbolHyp`），
而是一条关于 `∪` **本身**的、与 `v`／`π` 无关的**规范**陈述** —— 正是论文
`raw/L20261018.tex:746` 的 `\begin{theorem}[Merkurjev--Suslin 定理] \label{thm:prelim-ms}`。

## 为什么这**严格强于** `(G1)`

| | `(G1)`（旧） | 本件（`(G2)` 的收口形态） |
|---|---|---|
| 残余假设 | `Ch4TameSymbolHyp` ＝ `∃ d : H² → ker v̄, d(∪ y z)=0 ∧ d(∪ y π)=y` | `MerkurjevSuslin` ＝ `ker(∪) ⊆ span{a⊗(1−a), a⊗(−a)}` |
| 依赖哪些数据 | `∪`、`v`、`π`、`ker v̄` **全部** | **只有 `∪`**（与 `v`、`π` 无关） |
| 是不是论文自己的内容 | **是**（论文 `prop:prelim-residue`，第 4 章的 `∂₂`） | **不是**（论文引的 `thm:prelim-ms`，1982 年已发表） |
| 可否独立核验 | 否（战役自造的命题） | 是（Milnor `K₂` 的规范陈述；Merkurjev 1982／Merkurjev–Suslin） |

## 机检件

| 声明 | 内容 |
|---|---|
| **`steinbergGen`** | Steinberg 生成元集 `{(κa,κb) : a+b=1} ∪ {(κa,κ(−a))}`（`Finsupp` 单点） |
| **`MerkurjevSuslin`** | ★★★★★ 具名假设（论文 `thm:prelim-ms` 的类型锁定） |
| **`tameLC_steinbergGen_eq_zero`** | 每个生成元被 `tame` 杀掉（`a+b=1` 走 `Hyp688`，`−a` 走 `Hyp681`(K2)） |
| **`tameLC_eq_zero_of_mem_span`** | 线性 ⟹ 整个 `span` 被杀掉 |
| **`tameKernelCond_of_merkurjevSuslin`** | ★★★★★ `ker(∪) ≤ ker(tame)` |
| **`tameSymbolFactors_of_merkurjevSuslin`** | ★★★★★ ★**(G2) 的收口形态**：`MerkurjevSuslin ⟹ TameSymbolFactors` |
| **`merkurjevSuslin_of_subsingleton`** | 非空见证（`V = 0` 时显然成立；`finrank ≤ 1` 的见证登记为写作义务） |

## ⚠ 本轮自我更正（S61 R6）：第一版 `MerkurjevSuslin` **是假的**

第一版把右端写成 `span{steinbergGen}`（只有 Steinberg 生成元）。**这是错的**：
`(V × V) →₀ k` 是**配对**上的自由模，比 `V ⊗ V` 大得多 —— 它的核里还有**双线性关系**
（例：`single (x+y, z) − single (x,z) − single (y,z)` 的 `cupLC` 像为 `0`，但它一般**不在**
Steinberg 生成元的张成里）。故第一版假设在 `dim V ≥ 1` 时为**假** ⟹ `(G2)` 的收口形态会是
**空洞条件定理**（违反 L1 ＋ L10①）。

**修法**：右端并入 `bilinGen`（四个族：两个槽各自的可加性与标量性）。
* `tame` 在 `bilinGen` 上也为 `0`（`tameExpr_add_left/right`／`_smul_left/right`，`Hyp682`）—— 故证明只需加一支；
* 修正后的 `MerkurjevSuslin` 是**真**陈述（Merkurjev：`ker ∪̃ ⊆ Steinberg`，`∪̃` 定义在 `V ⊗ V` 上），
  且**非空洞**（`dim V ≥ 1` 时假设类不再自动为假）。
* 登记为 **`LESSONS` D26**：*「具名假设的右端必须包含**除目标关系外的全部关系**」*——
  只列"想要的"关系会让假设变成假命题，而**假假设使条件定理空洞**，这比 plainly 未证更危险。

## ⚠ S62 更新：Milnor K 已下放 ⟹ 本件的 `steinbergGen`／`bilinGen` 有正规版

`S62` 拉取了 `google-deepmind/formal-conjectures` 并核查（真编译 exit 0、基础设施 251 件零 `sorry`），
其中 **`FormalConjecturesForMathlib/FieldTheory/MilnorKTheory.lean`** 正是本件手搓的那套关系的
**成熟版本**：`MilnorK F ℓ`（＝ `TensorAlgebra ℤ (Additive Fˣ)` 模 Steinberg 理想 ＋ `ℓ=0`）、
`symbol`／`grade`／`symbolLengthBounds`，并已证 `symbol_eq_zero_of_add_eq_one`。
**已下放为本战役的 `Hyp694.lean`**（逐字副本 ＋ 一处下放修正，见 `S62-RECON-formal-conjectures.md`）。

**本件与它的关系**：`steinbergGen`／`bilinGen` 是 **`ZMod p`-模层、`Finsupp` 上**的表述，
`MilnorK` 是 **`ℤ`-代数层**的表述 —— **不同范畴**，故本件**保留**（`MerkurjevSuslin` 的
`Finsupp` 形态直接喂 `cupLC`／`tameLC`，不可换）。**下一步（证明级改指）**：用
`MilnorK.grade F p 2 → H²` 的单射重述 `MerkurjevSuslin`（论文 `thm:prelim-ms` 的原语言）。

## 非退化见证（`D26` 的要求，已机检）

`merkurjevSuslin_of_spanned_by_one`：`V` 由单个元素张成 ⟹ `MerkurjevSuslin` 成立。
**不需要** `∪ = 0`／斜对称／`2 ≠ 0` —— 它证的是更强的 `span(steinbergGen ∪ bilinGen) = ⊤`。
故假设类在 `dim V = 1`（`V ≠ 0`）时**真的**被占据，第一版的退化见证（`V = 0`）不再是唯一证据。

## 诚实边界

* 本件**不证** `MerkurjevSuslin`。它是 Merkurjev（1982）／Merkurjev–Suslin 的定理，也是论文
  `thm:prelim-ms` 引用的那一条。**这是 `(G2)` 唯一剩下的缺口**，且已命名、已发表、与战役数据无关。
* 本件**不**碰 GS 6.8.8（Hochschild–Serre 剩余正合列，(b2) 路线）：那条路要自建谱序列，
  成本与本条同量级而残余假设更强（依赖 `v`、`π`），故按 `G2-PLAN` §4 的判据优先本件形态。
* `finrank ≤ 1` 的非空见证（此时 `∪ = 0` 且 `single (x,x)` 本身就是 `a=−x` 型生成元）**未做**，
  登记为写作义务 —— 不影响本件的条件定理。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section Merkurjev

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable {p : ℕ} [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **双线性关系生成元集**（`(V×V) →₀ k → V ⊗ V` 的核的显式生成元）。

`(V×V) →₀ k` 是**配对**上的自由模，其到 `V ⊗ V` 的商核（双线性关系）一般**不在**
Steinberg 生成元的张成里；故 `MerkurjevSuslin` 的右端**必须**把它并进去
（否则该假设在 `dim V ≥ 1` 时为假 —— 见文件头「本轮自我更正」）。 -/
def bilinGen (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] :
    Set ((V × V) →₀ k) :=
  {g | (∃ x y z : V, g = Finsupp.single (x + y, z) 1
          - Finsupp.single (x, z) 1 - Finsupp.single (y, z) 1)
    ∨ (∃ x y z : V, g = Finsupp.single (x, y + z) 1
          - Finsupp.single (x, y) 1 - Finsupp.single (x, z) 1)
    ∨ (∃ (c : k) (x y : V), g = Finsupp.single (c • x, y) 1
          - c • Finsupp.single (x, y) 1)
    ∨ (∃ (c : k) (x y : V), g = Finsupp.single (x, c • y) 1
          - c • Finsupp.single (x, y) 1)}

/-- **Steinberg 生成元集**（Milnor `K₂` 的两族关系，在 `(V×V) →₀ ZMod p` 里的单点）：
`a ⊗ (1−a)` 与 `a ⊗ (−a)`。 -/
noncomputable def steinbergGen (hp : IsUnit (p : F)) :
    Set ((GaloBase.V F p × GaloBase.V F p) →₀ ZMod p) :=
  {g | (∃ a b : Fˣ, (a : F) + b = 1 ∧
        g = Finsupp.single (KummerBridge.kummerClass F p hp a,
          KummerBridge.kummerClass F p hp b) 1)
    ∨ (∃ a : Fˣ, g = Finsupp.single (KummerBridge.kummerClass F p hp a,
          KummerBridge.kummerClass F p hp (-a)) 1)}

/-- ★★★★★ **论文 `thm:prelim-ms`（Merkurjev–Suslin）的类型锁定**：

杯积的核由 Steinberg 关系生成 —— 即 `K₂^M(F)/p → H²(F, μ_p^{⊗2})` **单射**
（Merkurjev 1982；论文 `raw/L20261018.tex:746` 的 `thm:prelim-ms`）。

**只说 `∪`，不提 `v`、`π`、`ker v̄`** —— 这是它与 `Ch4TameSymbolHyp` 的本质区别。 -/
def MerkurjevSuslin (hp : IsUnit (p : F)) : Prop :=
  ∀ f : (GaloBase.V F p × GaloBase.V F p) →₀ ZMod p,
    cupLC (GaloBase.cup (K := F) (p := p)) f = 0 →
      f ∈ Submodule.span (ZMod p)
        (steinbergGen (F := F) (p := p) hp ∪ bilinGen (ZMod p) (GaloBase.V F p))

/-- `a + b = 1`（`a b : Fˣ`）⟹ `a ≠ 1` 且 `b = oneSub a _`。 -/
theorem eq_oneSub_of_add_eq_one {a b : Fˣ} (h : (a : F) + b = 1) :
    ∃ (ha : a ≠ 1), b = oneSub a ha := by
  have ha : a ≠ 1 := by
    rintro rfl
    have hb : (b : F) = 0 := by
      have h1 : (1 : F) + (b : F) = 1 := h
      linear_combination h1
    exact b.ne_zero hb
  refine ⟨ha, Units.ext ?_⟩
  rw [oneSub_coe]
  have h1 : (a : F) + (b : F) = 1 := h
  linear_combination h1

/-- ★★★ **每个 Steinberg 生成元被 `tame` 杀掉**。

两族：`a + b = 1` 用 `Hyp688`（A3，四情形）；`a + (−a)` 用 `κ(−a) = κ(a)`（`Hyp681`(K2)）
把 `tame(κa, κ(−a))` 化成 `tame(κa, κa) = 0`。 -/
theorem tameLC_steinbergGen_eq_zero
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hv : ValCompat (F := F) v)
    (hp2 : p ≠ 2) {g : (GaloBase.V F p × GaloBase.V F p) →₀ ZMod p}
    (hg : g ∈ steinbergGen (F := F) (p := p) hpF) :
    tameLC (valLinOf (F := F) (p := p) v hpF) g = 0 := by
  have hsingle : ∀ c : ZMod p, ∀ x y : GaloBase.V F p,
      tameLC (valLinOf (F := F) (p := p) v hpF) (Finsupp.single (x, y) c)
        = c • tameExpr (valLinOf (F := F) (p := p) v hpF) x y := by
    intro c x y
    simp [tameLC]
  rcases hg with ⟨a, b, hab, rfl⟩ | ⟨a, rfl⟩
  · obtain ⟨ha, rfl⟩ := eq_oneSub_of_add_eq_one hab
    rw [hsingle, tameExpr_kummerClass_oneSub (F := F) (p := p) (v := v) hp hpF hv hp2 ha,
      smul_zero]
  · -- `κ(−a) = κ(a)`（`−a = (−1)·a`，且 `κ(−1) = 0`）
    have hneg : KummerBridge.kummerClass F p hpF (-a) = KummerBridge.kummerClass F p hpF a := by
      have hm : (-a : Fˣ) = (-1) * a := by rw [neg_one_mul]
      rw [hm, KummerV.kummerClass_mul, kummerClass_neg_one (F := F) (p := p) hpF hp2, zero_add]
    rw [hneg, hsingle]
    have hzero : tameExpr (valLinOf (F := F) (p := p) v hpF)
        (KummerBridge.kummerClass F p hpF a) (KummerBridge.kummerClass F p hpF a) = 0 := by
      ext
      simp [tameExpr_coe]
    rw [hzero, smul_zero]

/-- ★★★ **双线性关系生成元也被 `tame` 杀掉**（`tame` 对两个槽分别可加、可乘标量）。 -/
theorem tameLC_bilinGen_eq_zero (hpF : IsUnit (p : F)) {g : (GaloBase.V F p × GaloBase.V F p) →₀ ZMod p}
    (hg : g ∈ bilinGen (ZMod p) (GaloBase.V F p)) :
    tameLC (valLinOf (F := F) (p := p) v hpF) g = 0 := by
  have hsingle : ∀ c : ZMod p, ∀ x y : GaloBase.V F p,
      tameLC (valLinOf (F := F) (p := p) v hpF) (Finsupp.single (x, y) c)
        = c • tameExpr (valLinOf (F := F) (p := p) v hpF) x y := by
    intro c x y
    simp [tameLC]
  rcases hg with ⟨x, y, z, rfl⟩ | ⟨x, y, z, rfl⟩ | ⟨c, x, y, rfl⟩ | ⟨c, x, y, rfl⟩
  · simp only [map_sub, hsingle, tameExpr_add_left, one_smul]
    module
  · simp only [map_sub, hsingle, tameExpr_add_right, one_smul]
    module
  · simp only [map_sub, map_smul, hsingle, tameExpr_smul_left]
    module
  · simp only [map_sub, map_smul, hsingle, tameExpr_smul_right]
    module

/-- ★★★★ **整个 `span` 被 `tame` 杀掉**（`tameLC` 线性）。 -/
theorem tameLC_eq_zero_of_mem_span
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hv : ValCompat (F := F) v)
    (hp2 : p ≠ 2) {f : (GaloBase.V F p × GaloBase.V F p) →₀ ZMod p}
    (hf : f ∈ Submodule.span (ZMod p)
      (steinbergGen (F := F) (p := p) hpF ∪ bilinGen (ZMod p) (GaloBase.V F p))) :
    tameLC (valLinOf (F := F) (p := p) v hpF) f = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro g hg
    rw [Set.mem_union] at hg
    rcases hg with hg | hg
    · exact tameLC_steinbergGen_eq_zero (F := F) (p := p) hp hpF hv hp2 hg
    · exact tameLC_bilinGen_eq_zero (F := F) (p := p) (v := v) hpF hg
  · simp
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy, add_zero]
  · intro c x _ hx
    simp only [map_smul, hx, smul_zero]

/-- ★★★★★ **`ker(∪) ≤ ker(tame)`**（`= tameKernelCond`）由 `MerkurjevSuslin` 推出。 -/
theorem tameKernelCond_of_merkurjevSuslin
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hv : ValCompat (F := F) v)
    (hp2 : p ≠ 2) (hMS : MerkurjevSuslin (F := F) (p := p) hpF) :
    tameKernelCond (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) := by
  intro f hf
  exact tameLC_eq_zero_of_mem_span (F := F) (p := p) hp hpF hv hp2 (hMS f hf)

/-- ★★★★★ ★**(G2) 的收口形态**：`MerkurjevSuslin ⟹ TameSymbolFactors`。

组装链：`MerkurjevSuslin ⟹ tameKernelCond`（本件）`⟹ TameSymbolFactors`（`Hyp687` 构造向），
等价地经 `Hyp689` 的 `⟺`。 -/
theorem tameSymbolFactors_of_merkurjevSuslin
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F)) (hv : ValCompat (F := F) v)
    (hp2 : p ≠ 2) (hMS : MerkurjevSuslin (F := F) (p := p) hpF) :
    TameSymbolFactors (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hpF) :=
  tameSymbolFactors_of_tameKernelCond _ _
    (tameKernelCond_of_merkurjevSuslin (F := F) (p := p) hp hpF hv hp2 hMS)

/-- **非空见证（L1 ＋ L10①）**：`V` 平凡（`H¹ = 0`）时 `MerkurjevSuslin` 成立。

此时 `V × V` 是单点，故任何 `f` 都是 `f 0 • single 0 1`；而 `single 0 1` **本身**就是
`a ⊗ (−a)` 型生成元（`κ a = 0`、`κ(−a) = 0`），故 `span = ⊤`。 -/
theorem merkurjevSuslin_of_subsingleton (hpF : IsUnit (p : F))
    [Subsingleton (GaloBase.V F p)] :
    MerkurjevSuslin (F := F) (p := p) hpF := by
  intro f _
  have hgen : (Finsupp.single (0 : GaloBase.V F p × GaloBase.V F p) (1 : ZMod p))
      ∈ steinbergGen (F := F) (p := p) hpF := by
    refine Or.inr ⟨1, ?_⟩
    exact congrArg (fun q => Finsupp.single q (1 : ZMod p)) (Subsingleton.elim _ _)
  have hf : f = f 0 • (Finsupp.single (0 : GaloBase.V F p × GaloBase.V F p) (1 : ZMod p)) := by
    ext x
    rw [Subsingleton.elim x 0]
    simp
  rw [hf]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_union_left _ hgen))

/-- ★★★★★ **非退化见证（`L1` ＋ `L10①` ＋ `D26`）**：`V` 由**单个元素张成**时 `MerkurjevSuslin` 成立。

**不需要** `∪ = 0`、不需要斜对称、不需要 `2 ≠ 0` —— 因为本引理证的是**更强**的
`span(steinbergGen ∪ bilinGen) = ⊤`，于是任何 `f` 都在其中。

思路：`bilinGen` 的两族（`single (c • x, y)`／`single (x, c • y)`）把任意
`single (x, y) c` 归结到 `single (x₀, x₀) 1`，而后者是 `a ⊗ (−a)` 型生成元
（`κ` 满射 ＋ `κ(−a) = κ a`，即 (K2)）。

**意义（`D26`）**：`V` 可以是一维而非零维 ⟹ 假设类**真的**被占据，不再是退化见证。 -/
theorem merkurjevSuslin_of_spanned_by_one (hpF : IsUnit (p : F)) (hp2 : p ≠ 2)
    (hsurj : Function.Surjective (KummerBridge.kummerClass F p hpF))
    (hx₀ : ∃ x₀ : GaloBase.V F p, ∀ w : GaloBase.V F p, ∃ c : ZMod p, c • x₀ = w) :
    MerkurjevSuslin (F := F) (p := p) hpF := by
  obtain ⟨x₀, hx₀⟩ := hx₀
  set S := Submodule.span (ZMod p)
    (steinbergGen (F := F) (p := p) hpF ∪ bilinGen (ZMod p) (GaloBase.V F p)) with hS
  -- `single (x₀,x₀) 1` 是 `a ⊗ (−a)` 型生成元
  have hgen : (Finsupp.single (x₀, x₀) (1 : ZMod p)) ∈ steinbergGen (F := F) (p := p) hpF := by
    obtain ⟨a, ha⟩ := hsurj x₀
    refine Or.inr ⟨a, ?_⟩
    have hneg : KummerBridge.kummerClass F p hpF (-a) = x₀ := by
      have hm : (-a : Fˣ) = (-1) * a := by rw [neg_one_mul]
      rw [hm, KummerV.kummerClass_mul, kummerClass_neg_one (F := F) (p := p) hpF hp2,
        zero_add, ha]
    rw [ha, hneg]
  have hgenS : (Finsupp.single (x₀, x₀) (1 : ZMod p)) ∈ S :=
    Submodule.subset_span (Set.mem_union_left _ hgen)
  -- 第二槽的标量性：`single (x₀, d • x₀) 1 ∈ S`
  have step2 : ∀ d : ZMod p, (Finsupp.single (x₀, d • x₀) (1 : ZMod p)) ∈ S := by
    intro d
    have hb : (Finsupp.single (x₀, d • x₀) (1 : ZMod p)
        - d • Finsupp.single (x₀, x₀) (1 : ZMod p)) ∈ S :=
      Submodule.subset_span (Set.mem_union_right _
        (Or.inr (Or.inr (Or.inr ⟨d, x₀, x₀, rfl⟩))))
    have h := Submodule.add_mem _ hb (Submodule.smul_mem _ d hgenS)
    simpa using h
  -- 第一槽的标量性
  have step1 : ∀ (c : ZMod p) (y : GaloBase.V F p),
      (Finsupp.single (x₀, y) (1 : ZMod p)) ∈ S →
        (Finsupp.single (c • x₀, y) (1 : ZMod p)) ∈ S := by
    intro c y hy
    have hb : (Finsupp.single (c • x₀, y) (1 : ZMod p)
        - c • Finsupp.single (x₀, y) (1 : ZMod p)) ∈ S :=
      Submodule.subset_span (Set.mem_union_right _
        (Or.inr (Or.inr (Or.inl ⟨c, x₀, y, rfl⟩))))
    have h := Submodule.add_mem _ hb (Submodule.smul_mem _ c hy)
    simpa using h
  -- 任意单点都在 `S` 里
  have hsingle : ∀ (x y : GaloBase.V F p) (c : ZMod p),
      (Finsupp.single (x, y) c) ∈ S := by
    intro x y c
    obtain ⟨cx, hcx⟩ := hx₀ x
    obtain ⟨cy, hcy⟩ := hx₀ y
    have h1 : (Finsupp.single (x, y) (1 : ZMod p)) ∈ S := by
      rw [← hcx, ← hcy]
      exact step1 cx (cy • x₀) (step2 cy)
    have h2 : Finsupp.single (x, y) c = c • Finsupp.single (x, y) (1 : ZMod p) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ c h1
  intro f _
  refine Finsupp.induction_linear f (Submodule.zero_mem _) ?_ ?_
  · intro g₁ g₂ h₁ h₂
    exact Submodule.add_mem _ h₁ h₂
  · intro q c
    exact hsingle q.1 q.2 c

end Merkurjev

end L20261018

/-! ## 机检读数（`#print axioms`） -/

#print axioms L20261018.eq_oneSub_of_add_eq_one
#print axioms L20261018.tameLC_steinbergGen_eq_zero
#print axioms L20261018.tameLC_bilinGen_eq_zero
#print axioms L20261018.tameLC_eq_zero_of_mem_span
#print axioms L20261018.tameKernelCond_of_merkurjevSuslin
#print axioms L20261018.tameSymbolFactors_of_merkurjevSuslin
#print axioms L20261018.merkurjevSuslin_of_subsingleton
#print axioms L20261018.merkurjevSuslin_of_spanned_by_one
