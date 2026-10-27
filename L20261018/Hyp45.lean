import L20261018.Hyp44
import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp
import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive

/-!
# ① 收口：`cupFp` 与 `GaloBase.cup` 是同一个杯积（载体搬运）

`Hyp44.exists_cupFp_ne_zero` 在 `cupFp`（系数载体 `trivialFp p G`，即 `ULift (ZMod p)`）上给出
真实局部域的非零 Kummer 杯积。论文的 `GaloBase.cup` 用的是 `muP`（载体直接是 `ZMod p`）。
两者只差一个宇宙提升：

    trivialFp p G = TopRep.of (ContRepresentation.trivial (ZMod p) G (ULift.{u} (ZMod p)))
    muP K p       = TopRep.of (ContRepresentation.trivial (ZMod p) G (ZMod p))

本文件构造它们的 `TopRep` 同构。平凡表示下 `ContIntertwiningMap` 的等变性自动成立，
所以只需把 `ULift.moduleEquiv` 提升为连续线性映射。

（`muP` 缺 `DiscreteTopology` 实例——它的定义里用 `letI` 局部引入，实例搜索不会展开——
故在此按 `trivialFp` 的同款手法补一条，见 `TrivialFp.lean:102`。）

## 主结果

* `GaloTrivialFp.downCLM` / `upCLM`：载体等价的连续线性映射形式。
* `GaloTrivialFp.iso`：**`trivialFp p G ≅ muP K p`**（`TopRep` 同构）。
-/

open TauCeti ContCohomology TopRep

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GaloTrivialFp

universe u

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime]

/-- `muP.V` 是 `ZMod p`，故可离散。`muP` 的定义把这个实例用 `letI` 局部引入，
实例搜索不会展开，故在此补一条（同 `TrivialFp.lean:102` 的手法）。 -/
instance : DiscreteTopology (GaloBase.muP K p).V := ZMod.instDiscreteTopology

/-- 载体等价的向下连续线性映射 `ULift (ZMod p) → ZMod p`。 -/
noncomputable def downCLM : (TauCeti.trivialFp p (AbsoluteGaloisGroup K)).V →L[ZMod p]
    (GaloBase.muP K p).V where
  toLinearMap := (trivialFpEquiv p (AbsoluteGaloisGroup K)).toLinearMap
  cont := continuous_of_discreteTopology

/-- 载体等价的向上连续线性映射 `ZMod p → ULift (ZMod p)`。 -/
noncomputable def upCLM : (GaloBase.muP K p).V →L[ZMod p]
    (TauCeti.trivialFp p (AbsoluteGaloisGroup K)).V where
  toLinearMap := (trivialFpEquiv p (AbsoluteGaloisGroup K)).symm.toLinearMap
  cont := continuous_of_discreteTopology

/-- 向下映射的等变性（平凡表示，自动）。 -/
theorem down_intertwining (g : AbsoluteGaloisGroup K) :
    (downCLM K p).comp ((TauCeti.trivialFp p (AbsoluteGaloisGroup K)).ρ g)
      = ((GaloBase.muP K p).ρ g).comp (downCLM K p) := by
  ext x
  rfl

/-- 向上映射的等变性。 -/
theorem up_intertwining (g : AbsoluteGaloisGroup K) :
    (upCLM K p).comp ((GaloBase.muP K p).ρ g)
      = ((TauCeti.trivialFp p (AbsoluteGaloisGroup K)).ρ g).comp (upCLM K p) := by
  ext x
  rfl

/-- **`trivialFp p G` 与 `muP K p` 作为 `TopRep` 同构。** -/
noncomputable def iso :
    TauCeti.trivialFp p (AbsoluteGaloisGroup K) ≅ GaloBase.muP K p where
  hom := TopRep.ofHom ⟨downCLM K p, down_intertwining K p⟩
  inv := TopRep.ofHom ⟨upCLM K p, up_intertwining K p⟩
  hom_inv_id := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    change (trivialFpEquiv p (AbsoluteGaloisGroup K)).symm
      ((trivialFpEquiv p (AbsoluteGaloisGroup K)) x) = x
    exact LinearEquiv.symm_apply_apply _ x
  inv_hom_id := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    change (trivialFpEquiv p (AbsoluteGaloisGroup K))
      ((trivialFpEquiv p (AbsoluteGaloisGroup K)).symm x) = x
    exact LinearEquiv.apply_symm_apply _ x

/-- **上同调层的加法等价**：`cohomFp`（`trivialFp` 载体）与 `continuousCohomology`（`muP` 载体）。 -/
noncomputable def cohomEquiv (d : ℕ) :
    TauCeti.cohomFp p (AbsoluteGaloisGroup K) d ≃+
      ↥(continuousCohomology d (GaloBase.muP K p)).toModuleCat :=
  ((TauCeti.ContinuousCohomology.continuousCohomologyFunctor (ZMod p) (AbsoluteGaloisGroup K) d).mapIso
    (iso K p)).toContinuousLinearEquiv.toAddEquiv

end GaloTrivialFp
