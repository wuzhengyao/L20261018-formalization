import L20261018.Hyp386
import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Acyclic
import Mathlib.FieldTheory.Galois.NormalBasis

/-!
# R1301（S37 第 9 轮）：**加法 Hilbert 90（全次数）** —— GS `lemma-additive-hilbert90` 的有限层

## 定理

GS 2017（`raw/GilleSzamuely2017.tex`，label `lemma-additive-hilbert90`）的证明第一句即本轮的定理：

> We prove the triviality of $H^{i}(G,K)$ for all finite Galois extensions $K|k$ with group $G$
> and all $i>0$.

机检形态：`L/K` 有限伽罗瓦 ⟹

```
H^{n+1}(Gal(L/K), L) = 0        对**所有** n
```

（`L` 取离散拓扑；系数必须是离散模。）

## 路线（照 GS 原文）

GS 的证明是三步：**正规基定理** ⟹ `K ≅ k ⊗ ℤ[G]` 作为 `G`-模 ⟹ 后者是**余诱导**模 ⟹
`cor-coinduced-cohomology` 给出零调。本仓三步都已就位：

| 步 | 件 |
|---|---|
| 正规基 | `IsGalois.normalBasis`（mathlib `FieldTheory/Galois/NormalBasis.lean`） |
| 正规基 ⟹ 余诱导 | **本轮**：`nbLinEquiv : L ≃ₗ[ℤ] DiscreteCoind Γ ⊥ K`（`Γ`-**等变**） |
| 余诱导 ⟹ 零调 | `ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int`（**全次数**） |

## 机检件

| 声明 | 内容 |
|---|---|
| `trivialBotAction` | `⊥ ≤ G` 在任意交换群上的（唯一）作用 |
| `fB`／`mkB`／`invB` | 正规基坐标 `x ↦ (τ ↦ c_{τ⁻¹})` 与其逆（摊回正规基） |
| `invB_mkB`／`mkB_invB` | 互逆 |
| **`nbAddEquiv`** | `L ≃+ DiscreteCoind Γ ⊥ K` |
| **`nbLinEquiv`** | ★★★★★ `L ≃ₗ[ℤ] Coind_1^Γ K`（**正规基 ⟹ 余诱导**） |
| `normalBasisRepr_smul` | `repr (γ • x) ρ = repr x (γ⁻¹ * ρ)`（正规基坐标的斜变性） |
| **`nbLinEquiv_smul`** | 该等价 `Γ`-**等变** |
| **`additiveHilbert90`** | ★★★★★★ `H^{n+1}(Gal(L/K), L) = 0`（全次数） |

## 与 S2 的关系（`GS68-LEDGER.md` §B 的 G3）

`prop-units-cohomology`（GS 6.8.7）的证明里要 `H^i(Γ, λ) = 0`（`λ` = 剩余域，`Γ` 有限）。
本轮把**更一般**的版本（任意有限伽罗瓦 `L/K`、任意次数）机检了 ⟹ **G3 关闭**。
S2 的缺口表从 5 条降到 4 条（`GS68-LEDGER.md` §E）。

## 工艺（上一轮的 deadend 已闭环，见 `deadend-normalBasis-coind.md`）

上一轮卡住的**真根因**是：`DiscreteCoind`-相关的辅助定义（`mkB`／`invB`）的**隐式 `{K L}`**
在语句里留成 metavar ⟹ 实例搜索 `[IsGalois ?K ?L]` 卡住（报
`typeclass instance problem is stuck: IsGalois ?m L`）。**修法**：凡应用这些辅助定义，
显式写 `(K := K) (L := L)`。另三处：`IsLocallyConstant` 要给 `(X := …)`；
`DiscreteCoind` 的等式要给类型归属；`hb` 要以 `.toLinearMap` 形式陈述。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

instance trivialBotAction (G : Type) [Group G] (A : Type) [AddCommGroup A] :
    DistribMulAction (⊥ : Subgroup G) A where
  smul _ x := x
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

noncomputable def fB (x : L) : (L ≃ₐ[K] L) → K := fun τ => (IsGalois.normalBasis K L).repr x τ⁻¹
theorem locB (x : L) : IsLocallyConstant (X := (L ≃ₐ[K] L)) (fB x) := IsLocallyConstant.of_discrete _

noncomputable def mkB (x : L) : DiscreteCoind (L ≃ₐ[K] L) ⊥ K :=
  DiscreteCoind.mk (L ≃ₐ[K] L) ⊥ K (fB x) (locB x) (by
    intro u g
    have hu : (u : (L ≃ₐ[K] L)) = 1 := by
      have h1 : u = 1 := Subsingleton.elim _ _; rw [h1]; rfl
    rw [hu, one_mul]; rfl)

noncomputable def invB (h : DiscreteCoind (L ≃ₐ[K] L) ⊥ K) : L :=
  ∑ σ : (L ≃ₐ[K] L), h σ⁻¹ • (IsGalois.normalBasis K L) σ

theorem invB_mkB (x : L) : invB (K := K) (L := L) (mkB (K := K) (L := L) x) = x := by
  classical
  rw [invB]
  have hterm : ∀ σ : (L ≃ₐ[K] L),
      (mkB (K := K) (L := L) x) σ⁻¹ • (IsGalois.normalBasis K L) σ
        = (IsGalois.normalBasis K L).repr x σ • (IsGalois.normalBasis K L) σ := by
    intro σ
    rw [mkB, DiscreteCoind.mk_apply, fB, inv_inv]
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ)]
  exact Module.Basis.sum_repr (IsGalois.normalBasis K L) x

theorem mkB_invB (h : DiscreteCoind (L ≃ₐ[K] L) ⊥ K) :
    mkB (K := K) (L := L) (invB (K := K) (L := L) h) = h := by
  apply DiscreteCoind.ext
  intro ρ
  rw [mkB, DiscreteCoind.mk_apply, fB, invB, Module.Basis.repr_sum_self, inv_inv]

theorem mkB_add (x y : L) :
    (mkB (K := K) (L := L) (x + y) : DiscreteCoind (L ≃ₐ[K] L) ⊥ K)
      = mkB (K := K) (L := L) x + mkB (K := K) (L := L) y := by
  classical
  apply DiscreteCoind.ext
  intro ρ
  simp only [mkB, DiscreteCoind.mk_apply, DiscreteCoind.coe_add, Pi.add_apply, fB,
    map_add, Finsupp.add_apply]

noncomputable def nbAddEquiv : L ≃+ DiscreteCoind (L ≃ₐ[K] L) ⊥ K where
  toFun := mkB
  invFun := invB
  left_inv := invB_mkB
  right_inv := mkB_invB
  map_add' := mkB_add

noncomputable def nbLinEquiv : L ≃ₗ[ℤ] DiscreteCoind (L ≃ₐ[K] L) ⊥ K where
  toFun := mkB
  invFun := invB
  left_inv := invB_mkB
  right_inv := mkB_invB
  map_add' := mkB_add
  map_smul' := fun (c : ℤ) (x : L) => map_zsmul (nbAddEquiv (K := K) (L := L)) c x

/-- **正规基坐标的斜变性**：`repr (γ • x) ρ = repr x (γ⁻¹ * ρ)`。 -/
theorem normalBasisRepr_smul (γ ρ : Gal(L/K)) (x : L) :
    (IsGalois.normalBasis K L).repr (γ • x) ρ =
      (IsGalois.normalBasis K L).repr x (γ⁻¹ * ρ) := by
  classical
  have key : ((IsGalois.normalBasis K L).coord ρ).comp
      (((γ : Gal(L/K)) : L ≃ₐ[K] L).toLinearMap)
      = (IsGalois.normalBasis K L).coord (γ⁻¹ * ρ) := by
    apply Module.Basis.ext (b := IsGalois.normalBasis K L)
    intro σ
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply]
    have hb : (((γ : Gal(L/K)) : L ≃ₐ[K] L).toLinearMap) ((IsGalois.normalBasis K L) σ)
        = (IsGalois.normalBasis K L) (γ * σ) := by
      rw [IsGalois.normalBasis_apply σ, IsGalois.normalBasis_apply (γ * σ)]
      rfl
    rw [hb, Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]
    by_cases h : γ * σ = ρ
    · rw [if_pos h, if_pos (by rw [← h]; group)]
    · rw [if_neg h, if_neg (by intro h'; exact h (by rw [h']; group))]
  have h : ((IsGalois.normalBasis K L).coord ρ)
      ((((γ : Gal(L/K)) : L ≃ₐ[K] L).toLinearMap) x) = ((IsGalois.normalBasis K L).coord (γ⁻¹ * ρ)) x := by
    have hh := DFunLike.congr_fun key x
    simpa only [LinearMap.comp_apply] using hh
  simpa only [LinearMap.comp_apply, Module.Basis.coord_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.smul_def] using h


/-- ★★★★★ `nbLinEquiv` 是 `Γ`-**等变**的（正规基坐标 vs 伽罗瓦作用）。 -/
theorem nbLinEquiv_smul (γ : Gal(L/K)) (x : L) :
    nbLinEquiv (K := K) (L := L) (γ • x) = γ • nbLinEquiv (K := K) (L := L) x := by
  apply DiscreteCoind.ext
  intro ρ
  show fB (K := K) (L := L) (γ • x) ρ = fB (K := K) (L := L) x (ρ * γ)
  simp only [fB, normalBasisRepr_smul, mul_inv_rev]

/-- ★★★★★★ **加法 Hilbert 90（有限层，全次数）**：`H^{n+1}(Gal(L/K), L) = 0`。

GS `lemma-additive-hilbert90` 的有限层；`L` 取离散拓扑（系数须为离散模）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=label:lemma-additive-hilbert90 quote="We prove the triviality of $H^{i}(G,K)$ for all finite Galois extensions $K|k$ with group $G$ and all $i>0$."
theorem additiveHilbert90 [TopologicalSpace L] [DiscreteTopology L] (n : ℕ) :
    Subsingleton ↑(continuousCohomology (n + 1)
      (TauCeti.ofDiscreteModule ℤ (L ≃ₐ[K] L) L)).toModuleCat := by
  have hev : ∀ (γ : (L ≃ₐ[K] L)) (x : L),
      nbLinEquiv (K := K) (L := L) (γ • x) = γ • nbLinEquiv (K := K) (L := L) x :=
    fun γ x => nbLinEquiv_smul γ x
  have hiso : TauCeti.ofDiscreteModule ℤ (L ≃ₐ[K] L) L ≅
      TauCeti.ofDiscreteModule ℤ (L ≃ₐ[K] L) (DiscreteCoind (L ≃ₐ[K] L) ⊥ K) :=
    TauCeti.ofDiscreteModuleIso (nbLinEquiv (K := K) (L := L)) hev
  have hZ := TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int
    (L ≃ₐ[K] L) K n
  let e := (CategoryTheory.Functor.mapIso
    (TauCeti.ContinuousCohomology.continuousCohomologyFunctor ℤ (L ≃ₐ[K] L) (n + 1))
    hiso).toContinuousLinearEquiv
  refine ⟨fun a b => ?_⟩
  exact e.injective (@Subsingleton.elim _ hZ (e a) (e b))

end L20261018

#print axioms L20261018.invB_mkB
#print axioms L20261018.mkB_invB
#print axioms L20261018.normalBasisRepr_smul
#print axioms L20261018.nbLinEquiv_smul
#print axioms L20261018.additiveHilbert90
