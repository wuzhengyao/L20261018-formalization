import L20261018.Ch2.Kummer.Step031_t1_model_comparison

/-!
# R1091（**T1 第六归约：`bridgeKc` 侧也写成 `muP.OfDiscrete ∘ explicitMap1`** —— 两侧同形）

接 R1090（战役侧 `kummerClass a = muP.OfDiscrete (explicitMap1 id e_c (kummerMap a))`），
本轮把 **`bridgeKc` 侧**也搬到**同一模型 `muP`** 上：

```
bridgeKc hζ a = muP.OfDiscrete ( explicitMap1 id (down ∘ μ) (kummerMap a) )
```

其中 `down := GaloTrivialFp.downCLM`（`ULift (ZMod p) → ZMod p`，底层就是 `trivialFpEquiv`）。

⟹ **两侧同为 `muP.OfDiscrete ∘ explicitMap1 id (系数映射)`**；`OfDiscrete` 是**加性等价**，
故 **T1 ⟺ 两条系数映射 `down ∘ μ` 与 `e_c`（在一维 `KummerCoeff` 上）只差非零标量** —— 即 `Hyp206`。

| 声明 | 内容 |
|---|---|
| **`downHom`** | `downCLM` 作为 `→+[G_a]`（等变性用库内 `GaloTrivialFp.down_intertwining`） |
| **`explicitMap1_comp_coeff`** | 群变换后接系数映射的复合律：`explicitCoeff1 q (explicitMap1 φ f x) = explicitMap1 φ (q ∘ f) x` |
| **`bridgeKc_eq_muP`** | ★ `bridgeKc hζ a = muP.OfDiscrete (explicitMap1 id (down ∘ μ) (kummerMap a))` |
-/

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ContCohomology

namespace L20261018

/-! ### 1. 复合律（群变换之后接系数映射） -/

section CompCoeff

variable {G : Type} [Monoid G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {H : Type} [Monoid H] [TopologicalSpace H]
  {N : Type} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction H N] [ContinuousSMul H N]
  {P : Type} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
  [DistribMulAction H P] [ContinuousSMul H P]

/-- **复合律**：群变换（`φ`）之后再作系数映射 `q`，等于沿 `φ` 拉回时直接用 `q ∘ f`。 -/
theorem explicitMap1_comp_coeff (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hef : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (q : N →+[H] P) (hq : Continuous q) (x : H1 G M) :
    explicitCoeff1 H N q hq
        (explicitMap1 G M H N φ f hf hef x)
      = explicitMap1 G M H P φ (q.toAddMonoidHom.comp f)
          (hq.comp hf)
          (fun h m => by
            show q (f (φ h • m)) = h • q (f m)
            rw [hef h m, map_smul q h (f m)]) x := by
  have hkey := explicitMap1_comp
    (G := G) (M := M) (H := H) (N := N)
    (φ := φ) (f := f) (hf := hf) (hequiv := hef)
    (K := H) (P := P)
    (ψ := ContinuousMonoidHom.id H) (q := q.toAddMonoidHom)
    (hq := hq) (hequivq := map_smul q)
  have hid : φ.comp (ContinuousMonoidHom.id H) = φ := by
    refine ContinuousMonoidHom.ext fun y => ?_
    rfl
  rw [explicitCoeff1_eq_explicitMap1]
  exact (congrArg (fun g => g x)
    ((explicitMap1_congr_of_eq _ _ _ _ _ _ _ _ hid rfl).symm.trans hkey)).symm

end CompCoeff

/-! ### 2. `bridgeKc` 侧搬到 `muP` -/

section BridgeMuP

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **`trivialFp` 的载体 → `muP` 的载体**（`ULift (ZMod p) → ZMod p`，底层即 `trivialFpEquiv`），
作为 `G_a`-等变加法映射（等变性 = 库内 `GaloTrivialFp.down_intertwining`）。 -/
noncomputable def downHom :
    (TauCeti.trivialFp p (AbsoluteGaloisGroup F)).V →+[AbsoluteGaloisGroup F]
      (GaloBase.muP F p).V :=
  { (GaloTrivialFp.downCLM F p).toAddMonoidHom with
    map_smul' := fun g m => by
      have h := DFunLike.congr_fun (GaloTrivialFp.down_intertwining F p g) m
      simpa using h }

/-- ★ **`bridgeKc` 侧也用同一模型 `muP`**。 -/
theorem bridgeKc_eq_muP (hζ : IsPrimitiveRoot ζ p) (a : Fˣ) :
    bridgeKc (F := F) p hζ a
      = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
          (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
            (AbsoluteGaloisGroup F) (GaloBase.muP F p).V
            (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
            ((downHom (F := F) (p := p)).toAddMonoidHom.comp
              (muHomAbs (F := F) (p := p) hζ))
            continuous_of_discreteTopology
            (fun g m => by
              show (downHom (F := F) (p := p))
                    ((muHomAbs (F := F) (p := p) hζ) (g • m))
                  = g • (downHom (F := F) (p := p))
                    ((muHomAbs (F := F) (p := p) hζ) m)
              rw [muHomAbs_equivariant (F := F) (p := p) hζ g m,
                map_smul (downHom (F := F) (p := p)) g _])
            (TauCeti.kummerMap F p hζ.neZero'.out.isUnit a).toAdd) := by
  rw [bridgeKc_eq_final (F := F) (p := p) hζ a]
  rw [coeffMap_ofDiscrete (X := TauCeti.trivialFp p (AbsoluteGaloisGroup F))
    (Y := GaloBase.muP F p) (F := (GaloTrivialFp.iso F p).hom)
    (f := downHom (F := F) (p := p)) (hF := fun m => rfl)]
  congr 1

end BridgeMuP

end L20261018

#print axioms L20261018.explicitMap1_comp_coeff
#print axioms L20261018.bridgeKc_eq_muP
