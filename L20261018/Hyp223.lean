import Hyp222
import Hyp206

/-!
# R1092（**★ T1 收口**）

R1087–R1091 已把 T1 的两侧压成**完全同形**（同一模型 `muP`、同一 `muP.OfDiscrete`、同一 `kummerMap a`）：

| 侧 | 形态 | 系数映射 |
|---|---|---|
| 战役侧（`Hyp221.kummerClass_eq_muP`） | `muP.OfDiscrete (explicitMap1 id e_c (kummerMap a))` | `e_c` |
| `bridgeKc` 侧（`Hyp222.bridgeKc_eq_muP`） | `muP.OfDiscrete (explicitMap1 id (down ∘ μ) (kummerMap a))` | `down ∘ μ` |

本文件把最后一层收掉：

1. `muP.OfDiscrete` 是**加法等价**（单射）；
2. 两条系数映射都是 `KummerCoeff`（**一维**）→ `muP.V` 的**非零**线性映射 ⟹ 只差非零标量 `c`（`Hyp206`）；
3. `explicitMap1` 的 **`k`-标量线性性**（`Hyp218`）把标量推出；`AddEquiv.map_nsmul` 与
   `Nat.cast_smul_eq_nsmul` 把 `ℕ`-标量换成 `ZMod p`-标量。

⟹ **(T1)** `∃ c : ZMod p, c ≠ 0 ∧ ∀ a, KummerBridge.kummerClass F p hp a = c • bridgeKc hζ a`。

| 声明 | 内容 |
|---|---|
| **`coeff_scalar`** | `∃ c ≠ 0, ∀ x, e_c x = c • (down ∘ μ) x`（一维 ＋ 非零） |
| **`t1_closed_of_hζ`** | ★ **(T1)**（`hp := hζ.neZero'.out.isUnit`） |
| **`t1_closed`** | ★ **(T1)**（任意 `hp : IsUnit (p : F)`，由 `IsUnit` 的证明无关性） |
-/

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ContCohomology ValuativeRel IsLocalRing

namespace L20261018

section T1Closed

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `muP` 的载体是离散的，故 `G_a`-作用连续（作用平凡）。 -/
instance instContinuousSMulMuPH223 : ContinuousSMul (AbsoluteGaloisGroup F) (GaloBase.muP F p).V where
  continuous_smul := by
    have h : Continuous fun q : AbsoluteGaloisGroup F × (GaloBase.muP F p).V => q.2 :=
      continuous_snd
    exact h

/-- `ZMod p`-标量与 `ℕ`-标量（取 `val`）一致。 -/
theorem zmod_smul_eq_val_nsmul (c : ZMod p) (y : (GaloBase.muP F p).V) :
    c • y = c.val • y := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) c.val y, ZMod.natCast_rightInverse c]

/-- **两条系数映射只差非零标量**（一维 `KummerCoeff` ＋ 两者皆非零）。 -/
theorem coeff_scalar (hζ : IsPrimitiveRoot ζ p) :
    ∃ c : ZMod p, c ≠ 0 ∧ ∀ x : KummerCoeff F p,
      (eCoeffHom (F := F) p hζ.neZero'.out.isUnit) x
        = c • ((downHom (F := F) (p := p)).toAddMonoidHom.comp
            (muHomAbs (F := F) (p := p) hζ)) x := by
  classical
  have hfr : Module.finrank (ZMod p) (KummerCoeff F p) = 1 :=
    TauCeti.finrank_kummerCoeff hζ.neZero'.out.isUnit
  have hfr2 : Module.finrank (ZMod p) (GaloBase.muP F p).V = 1 := Module.finrank_self (ZMod p)
  haveI : Nontrivial (KummerCoeff F p) :=
    Module.nontrivial_of_finrank_pos (R := ZMod p) (by rw [hfr]; norm_num)
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : KummerCoeff F p)
  -- 两条线性映射
  set f : KummerCoeff F p →ₗ[ZMod p] (GaloBase.muP F p).V :=
    (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).toAddMonoidHom.toZModLinearMap p with hf
  set g : KummerCoeff F p →ₗ[ZMod p] (GaloBase.muP F p).V :=
    ((downHom (F := F) (p := p)).toAddMonoidHom.comp
      (muHomAbs (F := F) (p := p) hζ)).toZModLinearMap p with hg
  have hf0 : f ≠ 0 := by
    intro h0
    have h1 : f x₀ = f 0 := by rw [h0]; rfl
    have h1' : (KummerBridge.kummerCoeffLinearEquiv F p hζ.neZero'.out.isUnit) x₀
        = (KummerBridge.kummerCoeffLinearEquiv F p hζ.neZero'.out.isUnit) 0 := h1
    exact hx₀ ((KummerBridge.kummerCoeffLinearEquiv F p
      hζ.neZero'.out.isUnit).injective h1')
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 : g x₀ = 0 := by rw [h0]; rfl
    have h2 : (TauCeti.trivialFpEquiv p (AbsoluteGaloisGroup F))
        ((ClassFieldTheory.muNRepEquivTrivialFp (n := p) (F := F) hζ) x₀) = 0 := by
      have h1' : (downHom (F := F) (p := p))
          ((muHomAbs (F := F) (p := p) hζ) x₀) = 0 := h1
      exact h1'
    have h3 : (ClassFieldTheory.muNRepEquivTrivialFp (n := p) (F := F) hζ) x₀ = 0 :=
      (TauCeti.trivialFpEquiv p (AbsoluteGaloisGroup F)).injective (by rw [h2]; rfl)
    refine hx₀ ((ClassFieldTheory.muNRepEquivTrivialFp (n := p) (F := F) hζ).injective ?_)
    rw [h3]
    exact (map_zero _).symm
  obtain ⟨c, hc, hco⟩ := L20261018.exists_smul_eq_of_finrank_eq_one (K := ZMod p)
    (M := KummerCoeff F p) (N := (GaloBase.muP F p).V) hfr hfr2 hf0 hg0
  exact ⟨c, hc, fun x => hco x⟩

/-- ★ **(T1)**：`∃ c : ZMod p, c ≠ 0 ∧ ∀ a, KummerBridge.kummerClass F p hp a = c • bridgeKc hζ a`
（`hp := hζ.neZero'.out.isUnit`）。 -/
theorem t1_closed_of_hζ (hζ : IsPrimitiveRoot ζ p) :
    ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ,
      KummerBridge.kummerClass F p hζ.neZero'.out.isUnit a = c • bridgeKc (F := F) p hζ a := by
  obtain ⟨c, hc, hco⟩ := coeff_scalar (F := F) (p := p) hζ
  have hns : ∀ x : KummerCoeff F p,
      (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).toAddMonoidHom x
        = c.val • ((downHom (F := F) (p := p)).toAddMonoidHom.comp
            (muHomAbs (F := F) (p := p) hζ)) x := by
    intro x
    rw [show (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).toAddMonoidHom x
        = (eCoeffHom (F := F) p hζ.neZero'.out.isUnit) x from rfl, hco x]
    exact zmod_smul_eq_val_nsmul (F := F) (p := p) c _
  have hpt : ∀ x : H1 (AbsoluteGaloisGroup F) (KummerCoeff F p),
      explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (AbsoluteGaloisGroup F)
          (ZMod p) (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
          (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).toAddMonoidHom
          continuous_of_discreteTopology
          (fun g m => (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).map_smul g m) x
        = c.val • explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
            (AbsoluteGaloisGroup F) (ZMod p)
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
                map_smul (downHom (F := F) (p := p)) g _]) x := by
    intro x
    exact congrArg (fun f => f x) (explicitMap1_eq_nsmul
      (φ := ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
      (f := (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).toAddMonoidHom)
      (g := (downHom (F := F) (p := p)).toAddMonoidHom.comp
        (muHomAbs (F := F) (p := p) hζ))
      (hf := continuous_of_discreteTopology) (hg := continuous_of_discreteTopology)
      (hef := fun g m => (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).map_smul g m)
      (heg := fun g m => by
        show (downHom (F := F) (p := p)) ((muHomAbs (F := F) (p := p) hζ) (g • m))
            = g • (downHom (F := F) (p := p)) ((muHomAbs (F := F) (p := p) hζ) m)
        rw [muHomAbs_equivariant (F := F) (p := p) hζ g m,
          map_smul (downHom (F := F) (p := p)) g _])
      (k := c.val) (hk := hns))
  refine ⟨((c.val : ℕ) : ZMod p), ?_, fun a => ?_⟩
  · rw [show ((c.val : ℕ) : ZMod p) = c from ZMod.natCast_rightInverse c]
    exact hc
  · have hx0 : (TauCeti.kummerMap F p hζ.neZero'.out.isUnit a).toAdd
        = (TauCeti.kummerMap F p hζ.neZero'.out.isUnit a).toAdd := rfl
    calc KummerBridge.kummerClass F p hζ.neZero'.out.isUnit a
        = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
            (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
              (AbsoluteGaloisGroup F) (ZMod p)
              (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
              (eCoeffHom (F := F) p hζ.neZero'.out.isUnit) continuous_of_discreteTopology
              (fun g m => (eCoeffHom (F := F) p hζ.neZero'.out.isUnit).map_smul g m)
              (TauCeti.kummerMap F p hζ.neZero'.out.isUnit a).toAdd) :=
          kummerClass_eq_muP (F := F) (p := p) hζ.neZero'.out.isUnit a
      _ = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
            (c.val • explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
              (AbsoluteGaloisGroup F) (ZMod p)
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
          exact congrArg (fun y =>
            (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete y) (hpt _)
      _ = c.val • (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
            (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
              (AbsoluteGaloisGroup F) (ZMod p)
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
              (TauCeti.kummerMap F p hζ.neZero'.out.isUnit a).toAdd) :=
          map_nsmul _ _ _
      _ = c.val • bridgeKc (F := F) p hζ a := by
          rw [bridgeKc_eq_muP (F := F) (p := p) hζ a]
          rfl
      _ = ((c.val : ℕ) : ZMod p) • bridgeKc (F := F) p hζ a :=
          (Nat.cast_smul_eq_nsmul (ZMod p) c.val (bridgeKc (F := F) p hζ a)).symm

/-- ★ **(T1)**（任意 `hp : IsUnit (p : F)`）：由 `IsUnit` 的证明无关性从 `t1_closed_of_hζ` 得。 -/
theorem t1_closed (hp : IsUnit (p : F)) (hζ : IsPrimitiveRoot ζ p) :
    ∃ c : ZMod p, c ≠ 0 ∧ ∀ a : Fˣ,
      KummerBridge.kummerClass F p hp a = c • bridgeKc (F := F) p hζ a := by
  obtain ⟨c, hc, hco⟩ := t1_closed_of_hζ (F := F) (p := p) hζ
  have hpp : hp = hζ.neZero'.out.isUnit := Subsingleton.elim _ _
  subst hpp
  exact ⟨c, hc, hco⟩

section R1

variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- ★★ **(R1) 无条件收口**：`residuePhi` 单射（论文假设下），**T1 假设已被机检消去**。 -/
theorem residuePhi_injective_of_t1
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hζ : IsPrimitiveRoot ζ p)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Function.Injective (residuePhi (GaloBase.cup (K := F) (p := p))
      (valLinOf (F := F) (p := p) v hζ.neZero'.out.isUnit)
      (KummerBridge.kummerClass F p hζ.neZero'.out.isUnit π)) :=
  residuePhi_injective_of_bridgeKc (F := F) (p := p) hp hζ
    (t1_closed_of_hζ (F := F) (p := p) hζ) hv hπ hp2

end R1

end T1Closed

end L20261018

#print axioms L20261018.coeff_scalar
#print axioms L20261018.t1_closed_of_hζ
#print axioms L20261018.t1_closed
#print axioms L20261018.residuePhi_injective_of_t1
