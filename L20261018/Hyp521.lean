import Hyp520
import TauCeti.RingTheory.RootsOfUnity.ZMod

/-!
# S43 R26（**GMS (7.3) 第二等号**）：`Hom(I, μ_p) ≅ ℤ/p` —— B1 的精确 1 维

## 上一轮的状态

`Hyp520` 给了 `Finite (H¹(I, μ_p))` ＋ `Nat.card ≤ p`（单射 `f ↦ f ζ` 进 `μ_p ≅ ℤ/p`）。
本轮把上界升成**等号**，即 GMS (7.3) 的第二等号：

> `\operatorname{Hom}(I,\mu_{n}) = \operatorname{Hom}(I_{t},\mu_{n}) = \mathbf{Z}/n\mathbf{Z}`（`raw/gms.tex:402`）

## 机制：显式截面

取 `ζ` 有**原始分量**（`PrimeToPTateModule.exists_forall_isPrimitiveRoot_proj`）。
于是 `ζ_p := proj_p ζ` 是**原始** `p` 次单位根，TauCeti 的
`IsPrimitiveRoot.zmodEquivRootsOfUnity : ZMod p ≃+ Additive μ_p`（`RootsOfUnity/ZMod.lean:118`）
给出 `ZMod p ≅ μ_p`。

对每个 `c : ZMod p` 定义

```
f_c (x) := ofAdd ( (zmodEquivRootsOfUnity hζ_p).symm (proj_p x) * c )      -- 乘法在 ZMod p 中
```

* `f_c` 是**乘法同态**（`e.symm` 加法、`· * c` 分配）；
* **连续**（经 `proj_p` 分解，而 `proj_p` 局部常值 —— `isLocallyConstant_proj`）；
* `f_c ζ = ofAdd (1 * c) = ofAdd c`（因 `e 1 = ζ_p` 恰是 `proj_p ζ`）。

⟹ `ev : Hom_cont(M, μ_p) → μ_p, f ↦ f ζ` **满射**（每个 `ofAdd c` 都是某个 `f_c` 的像）
⟹ 与 `Hyp520` 的单射合起来是**双射** ⟹ `Nat.card = p`。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`exists_primitiveComponents`** | 存在具原始分量的拓扑生成元 `ζ` |
| **`shiftedHom`** | 显式截面 `c ↦ f_c` |
| **`hom_cont_eval_surjective`**／**`hom_cont_eval_bijective`** | ★★★★★ `ev` 满射／双射 |
| **`natCard_hom_cont_tameModel_zmod_eq`** | ★★★★★ **`Nat.card (Hom_cont(M, μ_p)) = p`** |
| **`hom_cont_tameModel_equiv`**／**`hom_cont_inertiaLoc_equiv`** | ★★★★★ **GMS (7.3) 第二等号**（模型层／战役载体） |

## 诚实边界

* 系数是**平凡作用**下的 `μ_p`。论文的 `∂₂` 需要的是「`H¹(I,μ_p)` 由 `res_I(π)` 生成」——
  因 **`μ_p ⊂ F^{ur}`（`p ∤ char κ`）⟹ 惯性群在 `μ_p` 上作用平凡**，故平凡作用即论文所用系数；
  但 `res_I(π)` 与本节生成元（tame 特征在 `p` 层的投影）的**同一是下一步**。
* `C2`（Hensel → 完备）**未做**，见 `S43-STATUS.md` §1.9 的裁定。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti
open scoped TauCeti.zHat

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- ★★★★ **存在具原始分量的拓扑生成元**：`ζ ∈ M` 使每一层的分量都是原始单位根，且
`closedZpowers ζ = ⊤`（`PrimeToPTateModule.exists_forall_isPrimitiveRoot_proj` ＋
`topologicalClosure_zpowers_eq_top`）。 -/
theorem exists_primitiveComponents :
    ∃ ζ : TameModel F,
      (∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
        IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
          (AlgebraicClosure F)ˣ) (↑m)) ∧
      closedZpowers ζ = ⊤ := by
  have hpκ : (residueChar F).Prime :=
    CharP.prime_ringChar (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer)
  -- 每层都有原始单位根
  have hE : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      ∃ ζ : AlgebraicClosure F, IsPrimitiveRoot ζ (↑m) := by
    intro m
    haveI : NeZero ((↑m : ℕ) : F) :=
      ⟨natCast_ne_zero_of_isUnit (IsLocalRing.isUnit_natCast_iff_not_dvd.2
        (hpκ.coprime_iff_not_dvd.1 m.2.2.symm))⟩
    exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure F) (↑m)
  obtain ⟨ζ, hζ⟩ := PrimeToPTateModule.exists_forall_isPrimitiveRoot_proj
    (p := residueChar F) (E := AlgebraicClosure F) (X := TameModel F)
    continuous_id (fun m => proj_surjective_primeToPTateModule m) hE
  refine ⟨ζ, hζ, ?_⟩
  rw [closedZpowers_def]
  simpa using PrimeToPTateModule.topologicalClosure_zpowers_eq_top hζ

namespace OneDim

variable (p : ℕ) [Fact p.Prime]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]

/-- 层 `p` 的指标（`p ≠ 0`，且 `p` 与 `residueChar F = q` 互素）。 -/
noncomputable abbrev levelP (hpq : p ≠ q) : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)} :=
  ⟨p, (Fact.out : Nat.Prime p).ne_zero, by
    have hres : residueChar F = q := ringChar.eq _ q
    rw [hres]
    exact (Nat.coprime_primes Fact.out Fact.out).mpr hpq⟩

/-- ★★★★★ **显式截面**：`c : ZMod p ↦ (x ↦ ofAdd (e.symm (proj_p x) * c))`。 -/
noncomputable def shiftedHom (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (c : ZMod p) : TameModel F →ₜ* Multiplicative (ZMod p) :=
  { toMonoidHom :=
      { toFun := fun x => Multiplicative.ofAdd
          ((hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity.symm
            (Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) x)) * c)
        map_one' := by simp
        map_mul' := fun x y => by
          have hkey : (hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity.symm
                (Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) (x * y))) * c
              = (hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity.symm
                  (Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) x)) * c
                + (hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity.symm
                  (Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) y)) * c := by
            rw [map_mul (PrimeToPTateModule.proj (levelP (F := F) p q hpq)) x y]
            rw [show Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) x *
                PrimeToPTateModule.proj (levelP (F := F) p q hpq) y)
              = Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) x)
                + Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) y) from rfl]
            rw [AddEquiv.map_add, add_mul]
          show Multiplicative.ofAdd
              ((hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity.symm
                (Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) (x * y))) * c)
            = Multiplicative.ofAdd
                ((hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity.symm
                  (Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) x)) * c)
              * Multiplicative.ofAdd
                ((hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity.symm
                  (Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) y)) * c)
          rw [hkey, ofAdd_add] }
    continuous_toFun :=
      (PrimeToPTateModule.isLocallyConstant_proj (levelP (F := F) p q hpq)).comp
        (fun y => Multiplicative.ofAdd
          ((hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity.symm
            (Additive.ofMul y) * c)) |>.continuous }

/-- **截面的值在 `ζ` 上**：`f_c ζ = ofAdd (u * c)`，其中 `u := e.symm (proj_p ζ)`。 -/
theorem shiftedHom_apply_zeta (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (c : ZMod p) : shiftedHom (F := F) p q hpq ζ hζ c ζ
      = Multiplicative.ofAdd
        ((hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity.symm
          (Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) ζ)) * c) :=
  rfl

/-- **`u := e.symm (proj_p ζ)` 非零**：否则 `proj_p ζ = 1`，与它是原始单位根矛盾。 -/
theorem u_ne_zero (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m)) :
    (hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity.symm
        (Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) ζ)) ≠ 0 := by
  haveI hne : NeZero (levelP (F := F) p q hpq).1 :=
    ⟨(levelP (F := F) p q hpq).2.1⟩
  intro h
  have h1 : (hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity
      ((hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity.symm
        (Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) ζ)))
      = Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) ζ) :=
    AddEquiv.apply_symm_apply _ _
  rw [h, map_zero] at h1
  have h2 : PrimeToPTateModule.proj (levelP (F := F) p q hpq) ζ = 1 :=
    Additive.ofMul.injective h1.symm
  -- 引到 `Eˣ` 后与 `orderOf = p ≠ 1` 矛盾
  have h3 : ((PrimeToPTateModule.proj (levelP (F := F) p q hpq) ζ :
      ↥(rootsOfUnity (levelP (F := F) p q hpq).1 (AlgebraicClosure F))) : (AlgebraicClosure F)ˣ)
      = 1 := by
    simpa using congrArg Subtype.val h2
  have h4 : orderOf ((PrimeToPTateModule.proj (levelP (F := F) p q hpq) ζ :
      ↥(rootsOfUnity (levelP (F := F) p q hpq).1 (AlgebraicClosure F))) : (AlgebraicClosure F)ˣ)
      = (levelP (F := F) p q hpq).1 := ((hζ _).eq_orderOf).symm
  rw [h3, orderOf_one] at h4
  exact (Fact.out : Nat.Prime p).ne_one h4.symm

/-- ★★★★★ **求值 `f ↦ f ζ` 满射**（用 `u` 可逆：`c := u⁻¹ * y.toAdd`）。 -/
theorem hom_cont_eval_surjective (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m)) :
    Function.Surjective (fun f : TameModel F →ₜ* Multiplicative (ZMod p) => f ζ) := by
  intro y
  refine ⟨shiftedHom (F := F) p q hpq ζ hζ
    (((hζ (levelP (F := F) p q hpq)).zmodEquivRootsOfUnity.symm
      (Additive.ofMul (PrimeToPTateModule.proj (levelP (F := F) p q hpq) ζ)))⁻¹
      * Multiplicative.toAdd y), ?_⟩
  show shiftedHom (F := F) p q hpq ζ hζ _ ζ = y
  rw [shiftedHom_apply_zeta]
  rw [mul_inv_cancel_left₀ (u_ne_zero (F := F) p q hpq ζ hζ)]
  simp

/-- ★★★★★ **求值 `f ↦ f ζ` 双射**。 -/
theorem hom_cont_eval_bijective (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤) :
    Function.Bijective (fun f : TameModel F →ₜ* Multiplicative (ZMod p) => f ζ) :=
  ⟨hom_cont_eval_injective p ζ hgen, hom_cont_eval_surjective p q hpq ζ hζ⟩

/-- ★★★★★ **GMS (7.3) 第二等号（模型层）**：`Nat.card (Hom_cont(M, μ_p)) = p`。 -/
theorem natCard_hom_cont_tameModel_zmod_eq (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤) :
    Nat.card (TameModel F →ₜ* Multiplicative (ZMod p)) = p := by
  refine le_antisymm (natCard_hom_cont_tameModel_zmod_le p ζ hgen) ?_
  haveI hfin : Finite (TameModel F →ₜ* Multiplicative (ZMod p)) :=
    finite_hom_cont_tameModel_zmod p ζ hgen
  have hsurj := hom_cont_eval_surjective (F := F) p q hpq ζ hζ
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, ZMod.card]
  have hle : Nat.card (Multiplicative (ZMod p))
      ≤ Nat.card (TameModel F →ₜ* Multiplicative (ZMod p)) :=
    Nat.card_le_card_of_surjective _ hsurj
  rwa [hcard] at hle

/-- ★★★★★ **GMS (7.3) 第二等号（模型层）的等价形态**。 -/
noncomputable def hom_cont_tameModel_equiv (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤) :
    (TameModel F →ₜ* Multiplicative (ZMod p)) ≃ Multiplicative (ZMod p) :=
  Equiv.ofBijective _ (hom_cont_eval_bijective (F := F) p q hpq ζ hζ hgen)


/-- ★★★★★ **GMS (7.3) 第二等号（战役载体）**：`Hom_cont(inertiaLoc, μ_p) ≃ ℤ/p`。 -/
noncomputable def hom_cont_inertiaLoc_equiv (hpq : p ≠ q) (ζ : TameModel F)
    (hζ : ∀ m : {m : ℕ // m ≠ 0 ∧ m.Coprime (residueChar F)},
      IsPrimitiveRoot ((PrimeToPTateModule.proj m ζ : ↥(rootsOfUnity (↑m) (AlgebraicClosure F))) :
        (AlgebraicClosure F)ˣ) (↑m))
    (hgen : closedZpowers ζ = ⊤) :
    (↥(inertiaLoc F) →ₜ* Multiplicative (ZMod p)) ≃ Multiplicative (ZMod p) :=
  (InertiaTame.equivInertiaLocInertia (F := F) p).trans
    ((InertiaTame.equivTameInertia (F := F) p q hpq).symm.trans
      ((equivTameModelInertia (F := F) p).symm.trans
        (hom_cont_tameModel_equiv (F := F) p q hpq ζ hζ hgen)))

end OneDim

end L20261018

#print axioms L20261018.exists_primitiveComponents
#print axioms L20261018.OneDim.shiftedHom
#print axioms L20261018.OneDim.shiftedHom_apply_zeta
#print axioms L20261018.OneDim.hom_cont_eval_surjective
#print axioms L20261018.OneDim.hom_cont_eval_bijective
#print axioms L20261018.OneDim.natCard_hom_cont_tameModel_zmod_eq
#print axioms L20261018.OneDim.hom_cont_tameModel_equiv
#print axioms L20261018.OneDim.hom_cont_inertiaLoc_equiv
