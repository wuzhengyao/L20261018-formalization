import L20261018.Infra.Cohomology.Boundary.Step026_dimension_shift_from_long_exact
import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete
import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# S41 R4（动作 V2c ＋ V2b→V2a）：**GS (6.14) 的余诱导短正合列** ＋ **`H¹(G,C) ≃+ H²(G,A)`**

## 本件在 GS §6.8 的哪一格

GS **Construction 6.8.1**（`raw/GilleSzamuely2017.tex:9475`）的起点是

```
0 → A → M^G(A) → C → 0                                        (6.14)
```

本件把它**造出来**（不是在假设里），取

* `M^G(A) := DiscreteCoind G ⊥ A`（= 局部常值映射 `G → A`，右平移作用）—— GS 的**余诱导模**；
* `incl := DiscreteCoind.unit`（`a ↦ (g ↦ g • a)`，`DiscreteCoind.unit_injective` 供单射性）；
* `C := DiscreteCoind G ⊥ A ⧸ range(incl)`（`proj := QuotientAddGroup.mk'`）。

再把这列喂给 `Hyp492.deltaAddEquiv_of_subsingleton`（`n = 1`），并用库内的
**`subsingleton_continuousCohomology_discreteCoind_bot_int`**（`Coinduced/Acyclic.lean:301`，
一个 **instance**：`Subsingleton (Hⁿ⁺¹(G, DiscreteCoind G ⊥ A))`）供给零调性，即得

```
H¹(G, C) ≃+ H²(G, A)                                          (6.15) 的一半
```

## 机检件

| 声明 | 内容 |
|---|---|
| `coindCoker` | `C = DiscreteCoind G ⊥ A ⧸ (unit).range`（含 `G`-作用与连续作用，用库内 `quotientDistribMulAction`） |
| **`coindShortExactCoker`** | ★★★★ **GS (6.14)**：`DiscreteShortExact G A (DiscreteCoind G ⊥ A) C` |
| **`h1_coker_addEquiv_h2`** | ★★★★★ **`H¹(G, C) ≃+ H²(G, A)`**（= (6.15) 在 `i = 2` 的实例） |

## 依赖链（全部库内件）

```
DiscreteCoind.unit（余诱导单位，单射 ＋ 等变）        -- Coinduced/Discrete.lean:445,462
AddSubgroup.quotientDistribMulAction(_continuousSMul)  -- Topology/Algebra/GroupAction/QuotientAddGroup.lean
subsingleton_continuousCohomology_discreteCoind_bot_int -- Coinduced/Acyclic.lean:301（instance）
Hyp492.deltaAddEquiv_of_subsingleton                    -- R3
```

## 诚实边界

* 本件**只到 `H¹(G,C)`**。`C` 的**显式描述**（`C^H` 与 `H¹(H,A)` 的关系）与
  `H¹(G/H, C^H) ≅ H¹(G,C)`（V2e）**未做** —— 后者需要 **`H¹(H,C) = 0`**，即 **`H²(H,μ_p)=0`**
  （`cd_ℓ(inertia) ≤ 1`，GS A.6.9）。这是新路线**唯一需要新数学的载体层**，见 `S41-STATUS.md` §4.6。
- 本件**不**触及 `KnrResidueObligation`。
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

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

-- 把 `⊥` 在 `A` 上的作用钉到库内 `unit` 用的那一个（避免与另一条同名平凡作用的实例冲突）
local instance botActionPinned : DistribMulAction (⊥ : Subgroup G) A :=
  Subgroup.instDistribMulActionSubtypeMem ⊥

/-- 余诱导嵌入的像（`G`-稳定的加法子群）。 -/
noncomputable def coindRange : AddSubgroup (TauCeti.DiscreteCoind G ⊥ A) :=
  ((TauCeti.DiscreteCoind.unit G ⊥ A).toAddMonoidHom).range

/-- 该子群是 `G`-稳定的（`unit` 等变）。 -/
theorem coindRange_stable (g : G) {x : TauCeti.DiscreteCoind G ⊥ A} (hx : x ∈ coindRange (A := A)) :
    g • x ∈ coindRange (G := G) (A := A) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨g • a, (TauCeti.DiscreteCoind.unit G ⊥ A).map_smul' g a⟩

/-- ★★★★ **GS (6.14) 的商 `C`**：`C = Coind_1^G A ⧸ im(unit)`，带 `G`-作用与连续作用。 -/
noncomputable abbrev coindCoker : Type :=
  TauCeti.DiscreteCoind G ⊥ A ⧸ coindRange (G := G) (A := A)

/-- `G` 在 `C` 上的作用（商作用，库内 `quotientDistribMulAction`）。 -/
noncomputable instance coindCokerAction : DistribMulAction G (coindCoker (G := G) (A := A)) :=
  AddSubgroup.quotientDistribMulAction _ (fun g _ hx => coindRange_stable (G := G) (A := A) g hx)

/-- 该作用连续（库内 `quotientDistribMulAction_continuousSMul`）。 -/
noncomputable instance coindCokerContinuousSMul :
    ContinuousSMul G (coindCoker (G := G) (A := A)) :=
  AddSubgroup.quotientDistribMulAction_continuousSMul _ (fun g _ hx => coindRange_stable g hx)

/-- 商是离散的（`Coind_1^G A` 已离散）。 -/
instance coindCokerDiscrete : DiscreteTopology (coindCoker (G := G) (A := A)) := by
  unfold coindCoker
  infer_instance

/-- ★★★★★ **GS (6.14)**：`0 → A → Coind_1^G A → C → 0`（`DiscreteShortExact` 载体）。 -/
noncomputable def coindShortExactCoker :
    DiscreteShortExact G A (TauCeti.DiscreteCoind G ⊥ A) (coindCoker (G := G) (A := A)) where
  incl := (TauCeti.DiscreteCoind.unit G ⊥ A).toAddMonoidHom
  proj := QuotientAddGroup.mk' (coindRange (G := G) (A := A))
  incl_equivariant g a := (TauCeti.DiscreteCoind.unit G ⊥ A).map_smul' g a
  proj_equivariant g x :=
    (AddSubgroup.quotientDistribMulAction_smul_mk (coindRange (G := G) (A := A))
      (fun g _ hx => coindRange_stable (G := G) (A := A) g hx) g x).symm
  incl_injective := TauCeti.DiscreteCoind.unit_injective
  proj_surjective := QuotientAddGroup.mk'_surjective _
  exact x := QuotientAddGroup.eq_zero_iff (N := coindRange (G := G) (A := A)) (x := x)

/-- ★★★★★ **(6.15) 在 `i = 2` 的实例**：`H¹(G, C) ≃+ H²(G, A)`。

由 `Hyp492.deltaAddEquiv_of_subsingleton`（`n = 1`）＋ 库内零调性 instance
`subsingleton_continuousCohomology_discreteCoind_bot_int`。 -/
noncomputable def h1_coker_addEquiv_h2 :
    ↑(continuousCohomology 1 (TauCeti.ofDiscreteModule ℤ G
        (coindCoker (G := G) (A := A)))).toModuleCat ≃+
      ↑(continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ G A)).toModuleCat :=
  deltaAddEquiv_of_subsingleton (coindShortExactCoker (G := G) (A := A)) 1
    (TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int G A 0)
    (TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int G A 1)

end L20261018

#print axioms L20261018.coindRange_stable
#print axioms L20261018.coindShortExactCoker
#print axioms L20261018.h1_coker_addEquiv_h2
