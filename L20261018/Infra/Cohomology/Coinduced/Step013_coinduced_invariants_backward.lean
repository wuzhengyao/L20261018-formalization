import L20261018.Infra.Cohomology.Coinduced.Step012_coinduced_invariants_forward

/-!
# S65 R1：分片 **4a** —— GS `lemma-coinduced-invariants` 的**反向侧 ＋ 打包**

补完 `Hyp726`（前进侧）为一条完整的**加法等价**：

```
coindBotInvariantsEquiv : ↥((Coind_⊥^G A)^I) ≃+ DiscreteCoind (G ⧸ I) ⊥ A
```

（`I` 正规、`(·)^I` 是**右平移**作用下的不动元。）

## 数学内容

`Coind_⊥^G A` = 局部常值函数 `G → A`；`I`-不动元 ＝ 在**右** `I`-轨道 `{x · i}` 上常值的函数。
而 `x · i` 与 `x` 落在**同一个左陪集** `x I` 里（`i I = I`）⟹ 这样的函数恰是 `G ⧸ I` 上的函数。
故 `(Coind_⊥^G A)^I ≅ (G ⧸ I → A) = Coind_⊥^{G⧸I} A`（局部常值性随之）。

| 声明 | 内容 |
|---|---|
| `coindRevFun` / `coindRevFun_isLocallyConstant` | `F ↦ F ∘ mk`（`mk` 连续 ＋ 离散靶） |
| `coindRev` | `F ↦ F ∘ mk` 打包成 `DiscreteCoind G ⊥ A` |
| `coindRev_mem` | 它落在**右** `I`-不动元里（`mk (g * i) = mk g`） |
| `coindRevInv` / `coindFwd` | 两个方向的 `↥((·)^I) →/← DiscreteCoind (G⧸I) ⊥ A` |
| **`coindBotInvariantsEquiv`** | ★ 加法等价 |

## 实例坑（`D45`）

`DiscreteCoind (G ⧸ I) ⊥ A` 需要 `DistribMulAction (↥(⊥ : Subgroup (G ⧸ I))) A`——
`A` 只有 `G`-作用，**不能**合成。用 `Hyp387.trivialBotAction`（全局实例，`smul _ x := x`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

universe u v

/-- `⊥ ≤ H` 在任意加法交换群上的**唯一**（平凡）作用。

⚠ **为什么不复用 `Hyp387.trivialBotAction`**：那条是 **`Type` 宇宙单态**（`G : Type`），在
`G ⧸ I : Type u` 上无法使用（实弹：`Application type mismatch`）；更糟的是它是**默认优先级**的全局实例，
在 `G : Type` 的文件里会**静默顶掉** `DiscreteCoind G ⊥ A` 的**真**作用实例 ⟹ 本件**不 import `Hyp387`**。
⚠ **低优先级**（`priority := 10`）：仅在"派生作用不存在"时被选中（`D41` 型钻石规避）。 -/
instance (priority := 10) trivialBotActionU (H : Type u) [Group H] (A : Type v) [AddCommGroup A] :
    DistribMulAction (⊥ : Subgroup H) A where
  smul _ x := x
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G]
variable (I : Subgroup G) [I.Normal]
variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A]

/-! ## 1 反向映射 -/

/-- 反向映射的函数部分：`F ↦ F ∘ mk`。 -/
noncomputable def coindRevFun (F : DiscreteCoind (G ⧸ I) ⊥ A) : G → A :=
  fun g => F (Quotient.mk (QuotientGroup.leftRel I) g)

theorem coindRevFun_isLocallyConstant (F : DiscreteCoind (G ⧸ I) ⊥ A) :
    IsLocallyConstant (coindRevFun (I := I) F) :=
  (DiscreteCoind.isLocallyConstant F).comp_continuous continuous_quotient_mk'

/-- 反向映射打包成 `DiscreteCoind G ⊥ A`（`⊥`-条件空洞：`u = 1`）。 -/
noncomputable def coindRev (F : DiscreteCoind (G ⧸ I) ⊥ A) : DiscreteCoind G ⊥ A :=
  DiscreteCoind.mk G ⊥ A (coindRevFun (I := I) F) (coindRevFun_isLocallyConstant (I := I) F)
    (fun u g => by
      have hu : (u : G) = 1 := Subgroup.mem_bot.mp u.2
      simp only [coindRevFun, Subgroup.smul_def, hu, one_mul, one_smul])

/-- 左陪集不区分右乘 `I`：`mk (g * i) = mk g`。 -/
theorem mk_mul_coe_I (g : G) (i : ↥I) :
    (Quotient.mk (QuotientGroup.leftRel I) (g * (i : G)) : G ⧸ I)
      = Quotient.mk (QuotientGroup.leftRel I) g :=
  Quotient.sound (QuotientGroup.leftRel_apply.mpr (by
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using I.inv_mem i.2))

/-- 反向映射落在**右** `I`-不动元里。 -/
theorem coindRev_mem (F : DiscreteCoind (G ⧸ I) ⊥ A) :
    coindRev (I := I) F ∈ FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A) := by
  rw [FixedPoints.mem_addSubgroup]
  intro i
  refine DiscreteCoind.ext fun g => ?_
  show coindRevFun (I := I) F (g * (i : G)) = coindRevFun (I := I) F g
  exact congrArg F (mk_mul_coe_I (I := I) g i)

/-- 反向映射的值域限定到不动元子模。 -/
noncomputable def coindRevInv (F : DiscreteCoind (G ⧸ I) ⊥ A) :
    ↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A)) :=
  ⟨coindRev (I := I) F, coindRev_mem (I := I) F⟩

/-! ## 2 前进方向（`Hyp726` 的 `coindInvFun` 打包） -/

/-- 前进映射打包成 `DiscreteCoind (G ⧸ I) ⊥ A`。 -/
noncomputable def coindFwd (f : ↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A))) :
    DiscreteCoind (G ⧸ I) ⊥ A :=
  DiscreteCoind.mk (G ⧸ I) ⊥ A (coindInvFun (I := I) f)
    (coindInvFun_isLocallyConstant (I := I) f)
    (fun u q => by
      have hu : (u : G ⧸ I) = 1 := Subgroup.mem_bot.mp u.2
      rw [hu, one_mul]
      rfl)

/-! ## 3 往返两条 -/

theorem coindRevInv_coindFwd
    (f : ↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A))) :
    coindRevInv (I := I) (coindFwd (I := I) f) = f := by
  refine Subtype.ext ?_
  refine DiscreteCoind.ext fun g => ?_
  show coindInvFun (I := I) f (Quotient.mk (QuotientGroup.leftRel I) g)
      = (f : DiscreteCoind G ⊥ A) g
  rfl

theorem coindFwd_coindRevInv (F : DiscreteCoind (G ⧸ I) ⊥ A) :
    coindFwd (I := I) (coindRevInv (I := I) F) = F := by
  refine DiscreteCoind.ext fun q => ?_
  induction q using Quotient.inductionOn with
  | _ g =>
    show coindInvFun (I := I) (coindRevInv (I := I) F)
        (Quotient.mk (QuotientGroup.leftRel I) g) = F (Quotient.mk (QuotientGroup.leftRel I) g)
    rfl

/-! ## 4 打包成加法等价 -/

/-- ★ **分片 4a（机检形态）**：`I` 正规时
`↥((Coind_⊥^G A)^I) ≃+ DiscreteCoind (G ⧸ I) ⊥ A`（右平移不动元 ≅ 商上的局部常值函数）。 -/
noncomputable def coindBotInvariantsEquiv :
    ↥(FixedPoints.addSubgroup (↥I) (DiscreteCoind G ⊥ A)) ≃+ DiscreteCoind (G ⧸ I) ⊥ A where
  toFun := coindFwd (I := I)
  invFun := coindRevInv (I := I)
  left_inv := coindRevInv_coindFwd (I := I)
  right_inv := coindFwd_coindRevInv (I := I)
  map_add' f g := by
    refine DiscreteCoind.ext fun q => ?_
    induction q using Quotient.inductionOn with
    | _ x => rfl

end L20261018

#print axioms L20261018.coindRev
#print axioms L20261018.coindRev_mem
#print axioms L20261018.coindFwd
#print axioms L20261018.coindBotInvariantsEquiv
