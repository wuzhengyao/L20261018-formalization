import Mathlib
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Graded.Comm

set_option maxHeartbeats 1000000

open LinearMap Submodule
open scoped Cardinal

namespace L20261018

/-- The abstract bi-Kummer data: a bilinear, alternating, skew-symmetric cup
product and two first-slot classes with nonvanishing cup product. -/
structure BiKummerData (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    (H2 : Type*) [AddCommGroup H2] [Module k H2] where
  cup : V →ₗ[k] V →ₗ[k] H2
  a1 : V
  a2 : V
  hne : cup a1 a2 ≠ 0
  skew : ∀ x y, cup x y = - cup y x

namespace BiKummerData

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]
variable {W : Type*} [AddCommGroup W] [Module k W]

variable [NeZero (2 : k)]

variable (B : BiKummerData k V H2)

/-- In characteristic `≠ 2`, skew-symmetry forces alternation:
`x ∪ x = -(x ∪ x)` hence `2 • (x ∪ x) = 0`. -/
lemma alt' (x : V) : B.cup x x = 0 := by
  have h : B.cup x x = - B.cup x x := B.skew x x
  have h2 : (2 : k) • B.cup x x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    abel
  exact (smul_eq_zero.mp h2).resolve_left (NeZero.ne (2 : k))

/-- The plane `U` spanned by the two first-slot classes. -/
def U : Submodule k V := Submodule.span k {B.a1, B.a2}

/-- The common cup-product map `Φ x = (x ∪ a₁, x ∪ a₂)`. -/
def Phi : V →ₗ[k] H2 × H2 where
  toFun x := (B.cup x B.a1, B.cup x B.a2)
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

/-- The common orthogonal space `U^⊥ = ker Φ`. -/
def Uperp : Submodule k V := LinearMap.ker B.Phi

@[simp] lemma Phi_apply (x : V) : B.Phi x = (B.cup x B.a1, B.cup x B.a2) := rfl

@[simp] lemma cup_a1_a1 : B.cup B.a1 B.a1 = 0 := B.alt' B.a1

@[simp] lemma cup_a2_a2 : B.cup B.a2 B.a2 = 0 := B.alt' B.a2

@[simp] lemma cup_a2_a1 : B.cup B.a2 B.a1 = - B.cup B.a1 B.a2 := B.skew _ _

lemma mem_U_iff (x : V) : x ∈ B.U ↔ ∃ c1 c2 : k, c1 • B.a1 + c2 • B.a2 = x := by
  rw [BiKummerData.U, Submodule.mem_span_pair]

lemma mem_Uperp_iff (x : V) : x ∈ B.Uperp ↔ B.cup x B.a1 = 0 ∧ B.cup x B.a2 = 0 := by
  rw [BiKummerData.Uperp, LinearMap.mem_ker, B.Phi_apply, Prod.mk_eq_zero]

/-- Lemma 3.1 (1): `U ∩ U^⊥ = 0`. -/
theorem lemma_3_1_1 : B.U ⊓ B.Uperp = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvU, hvP⟩ := hv
  obtain ⟨c1, c2, hvc⟩ := B.mem_U_iff v |>.mp hvU
  have hP := B.mem_Uperp_iff v |>.mp hvP
  have h1 : B.cup (c1 • B.a1 + c2 • B.a2) B.a1 = 0 := by rw [hvc]; exact hP.1
  have h2 : B.cup (c1 • B.a1 + c2 • B.a2) B.a2 = 0 := by rw [hvc]; exact hP.2
  have e1 : B.cup (c1 • B.a1 + c2 • B.a2) B.a1 = -(c2 • B.cup B.a1 B.a2) := by
    simp [map_add, map_smul]
  have e2 : B.cup (c1 • B.a1 + c2 • B.a2) B.a2 = c1 • B.cup B.a1 B.a2 := by
    simp [map_add, map_smul]
  have hc2 : c2 = 0 := by
    rw [e1] at h1
    have : c2 • B.cup B.a1 B.a2 = 0 := by simpa using h1
    exact (smul_eq_zero.mp this).resolve_right B.hne
  have hc1 : c1 = 0 := by
    rw [e2] at h2
    exact (smul_eq_zero.mp h2).resolve_right B.hne
  rw [Submodule.mem_bot]
  rw [← hvc, hc1, hc2]
  simp

/-- Lemma 3.1 (2): the restriction of `res` to `U^⊥` is injective,
provided `ker res = U` (the bi-Kummer kernel computation). -/
theorem lemma_3_1_2 (res : V →ₗ[k] W) (hker : LinearMap.ker res = B.U) :
    Function.Injective (fun x : B.Uperp => res x.val) := by
  intro x y hxy
  apply Subtype.ext
  have hsub : res (x.val - y.val) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  have hmem : x.val - y.val ∈ B.U := by
    rw [← hker]; exact LinearMap.mem_ker.mpr hsub
  have hmem2 : x.val - y.val ∈ B.Uperp := B.Uperp.sub_mem x.2 y.2
  have : x.val - y.val ∈ B.U ⊓ B.Uperp := ⟨hmem, hmem2⟩
  rw [B.lemma_3_1_1, Submodule.mem_bot] at this
  exact sub_eq_zero.mp this

/-- `Φ a₁ = (0, h)` and `Φ a₂ = (-h, 0)`. -/
lemma Phi_a1 : B.Phi B.a1 = (0, B.cup B.a1 B.a2) := by
  simp [B.Phi_apply]

lemma Phi_a2 : B.Phi B.a2 = (-B.cup B.a1 B.a2, 0) := by
  simp [B.Phi_apply]

lemma linearIndependent_Phi : LinearIndependent k ![(B.Phi B.a1), (B.Phi B.a2)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : g 0 • B.Phi B.a1 + g 1 • B.Phi B.a2 = 0 := by
    simpa [Fin.sum_univ_two] using hg
  rw [Phi_a1, Phi_a2] at hg'
  have h0 : g 0 = 0 := by
    have h := congrArg Prod.snd hg'
    have h' : g 0 • B.cup B.a1 B.a2 = 0 := by simpa using h
    exact (smul_eq_zero.mp h').resolve_right B.hne
  have h1 : g 1 = 0 := by
    have h := congrArg Prod.fst hg'
    have h' : g 1 • B.cup B.a1 B.a2 = 0 := by simpa using h
    exact (smul_eq_zero.mp h').resolve_right B.hne
  fin_cases i
  · exact h0
  · exact h1

/-- Lemma 3.1 (3): `rank Φ ≥ 2`. -/
theorem lemma_3_1_3 : (2 : Cardinal) ≤ Module.rank k ↥B.Phi.range := by
  have hLI : LinearIndependent k (fun i : Fin 2 => ![(B.Phi B.a1), (B.Phi B.a2)] i) :=
    B.linearIndependent_Phi
  have hfr : Module.finrank k ↥(Submodule.span k
      (Set.range (fun i : Fin 2 => ![(B.Phi B.a1), (B.Phi B.a2)] i))) = 2 := by
    rw [finrank_span_eq_card hLI]
    simp
  haveI : Module.Finite k ↥(Submodule.span k
      (Set.range (fun i : Fin 2 => ![(B.Phi B.a1), (B.Phi B.a2)] i))) :=
    Module.Finite.of_fg (Submodule.fg_span (Set.finite_range _))
  have hrank : Module.rank k ↥(Submodule.span k
      (Set.range (fun i : Fin 2 => ![(B.Phi B.a1), (B.Phi B.a2)] i))) = (2 : Cardinal) := by
    have h := Module.finrank_eq_rank k ↥(Submodule.span k
      (Set.range (fun i : Fin 2 => ![(B.Phi B.a1), (B.Phi B.a2)] i)))
    rw [hfr] at h
    simpa using h.symm
  have hle : Submodule.span k
      (Set.range (fun i : Fin 2 => ![(B.Phi B.a1), (B.Phi B.a2)] i)) ≤ B.Phi.range := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨B.a1, rfl⟩
    · exact ⟨B.a2, rfl⟩
  calc (2 : Cardinal)
      = Module.rank k ↥(Submodule.span k
          (Set.range (fun i : Fin 2 => ![(B.Phi B.a1), (B.Phi B.a2)] i))) := hrank.symm
    _ ≤ Module.rank k ↥B.Phi.range := Submodule.rank_mono hle


lemma range_fin2 {M : Type*} (a b : M) :
    Set.range (fun i : Fin 2 => ![a, b] i) = ({a, b} : Set M) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- If `rank Φ = 2`, then `V = U + U^⊥`. -/
theorem sup_U_Uperp_eq_top (hrank : Module.rank k ↥B.Phi.range = (2 : Cardinal)) :
    B.U ⊔ B.Uperp = ⊤ := by
  have hLI : LinearIndependent k (fun i : Fin 2 => ![(B.Phi B.a1), (B.Phi B.a2)] i) :=
    B.linearIndependent_Phi
  have hfrS : Module.finrank k ↥(Submodule.span k
      (Set.range (fun i : Fin 2 => ![(B.Phi B.a1), (B.Phi B.a2)] i))) = 2 := by
    rw [finrank_span_eq_card hLI]
    simp
  have hle : Submodule.span k
      (Set.range (fun i : Fin 2 => ![(B.Phi B.a1), (B.Phi B.a2)] i)) ≤ B.Phi.range := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨B.a1, rfl⟩
    · exact ⟨B.a2, rfl⟩
  haveI hfin : Module.Finite k ↥B.Phi.range := Module.finite_of_rank_eq_nat hrank
  have hfrR : Module.finrank k ↥B.Phi.range = 2 := by
    rw [show Module.finrank k ↥B.Phi.range
        = Cardinal.toNat (Module.rank k ↥B.Phi.range) from rfl, hrank]
    simp
  have hS : Submodule.span k
      (Set.range (fun i : Fin 2 => ![(B.Phi B.a1), (B.Phi B.a2)] i)) = B.Phi.range :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfrS, hfrR])
  rw [eq_top_iff]
  intro v _
  have hv : B.Phi v ∈ B.Phi.range := ⟨v, rfl⟩
  rw [← hS] at hv
  rw [range_fin2] at hv
  obtain ⟨c1, c2, hc⟩ := Submodule.mem_span_pair.mp hv
  have hwPhi : B.Phi (v - (c1 • B.a1 + c2 • B.a2)) = 0 := by
    rw [map_sub, map_add, map_smul, map_smul, hc.symm]
    simp
  have hw : v - (c1 • B.a1 + c2 • B.a2) ∈ B.Uperp :=
    LinearMap.mem_ker.mpr hwPhi
  have hu : c1 • B.a1 + c2 • B.a2 ∈ B.U := B.mem_U_iff _ |>.mpr ⟨c1, c2, rfl⟩
  exact Submodule.mem_sup.mpr ⟨_, hu, _, hw, by abel⟩

lemma exists_decomp_of_sup_eq_top (htop : B.U ⊔ B.Uperp = ⊤) (x : V) :
    ∃ u ∈ B.U, ∃ w ∈ B.Uperp, u + w = x := by
  have hx : x ∈ B.U ⊔ B.Uperp := by rw [htop]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hx
  exact ⟨u, hu, w, hw, huw⟩

/-- Theorem 3.2, reduction step: if `rank Φ = 2`, then
`a₁ ∪ b₁ + a₂ ∪ b₂` lies in the line spanned by `a₁ ∪ a₂`. -/
theorem theorem_3_2_reduction (hrank : Module.rank k ↥B.Phi.range = (2 : Cardinal))
    (b1 b2 : V) :
    ∃ c : k, B.cup B.a1 b1 + B.cup B.a2 b2 = c • B.cup B.a1 B.a2 := by
  have htop := B.sup_U_Uperp_eq_top hrank
  obtain ⟨u1, hu1, w1, hw1, hb1⟩ := B.exists_decomp_of_sup_eq_top htop b1
  obtain ⟨u2, hu2, w2, hw2, hb2⟩ := B.exists_decomp_of_sup_eq_top htop b2
  obtain ⟨s1, t1, hue1⟩ := B.mem_U_iff u1 |>.mp hu1
  obtain ⟨s2, t2, hue2⟩ := B.mem_U_iff u2 |>.mp hu2
  have hw1p := B.mem_Uperp_iff w1 |>.mp hw1
  have hw2p := B.mem_Uperp_iff w2 |>.mp hw2
  have hw1' : B.cup B.a1 w1 = 0 := by
    rw [B.skew, hw1p.1, neg_zero]
  have hw2' : B.cup B.a2 w2 = 0 := by
    rw [B.skew, hw2p.2, neg_zero]
  have e1 : B.cup B.a1 b1 = t1 • B.cup B.a1 B.a2 := by
    rw [← hb1, map_add, hw1', add_zero, ← hue1, map_add, map_smul, map_smul]
    simp
  have e2 : B.cup B.a2 b2 = -(s2 • B.cup B.a1 B.a2) := by
    rw [← hb2, map_add, hw2', add_zero, ← hue2, map_add, map_smul, map_smul]
    simp
  refine ⟨t1 - s2, ?_⟩
  rw [e1, e2, sub_smul]
  abel

/-- Theorem 3.2 (1): if `rank Φ = 2`, then `ind D ≤ p`, where `ind` is any
index function that is `≤ p` on the line spanned by `a₁ ∪ a₂`. -/
theorem theorem_3_2_1 (p : ℕ) (ind : H2 → ℕ)
    (hind : ∀ x ∈ Submodule.span k ({B.cup B.a1 B.a2} : Set H2), ind x ≤ p)
    (hrank : Module.rank k ↥B.Phi.range = (2 : Cardinal)) (b1 b2 : V) :
    ind (B.cup B.a1 b1 + B.cup B.a2 b2) ≤ p := by
  obtain ⟨c, hc⟩ := B.theorem_3_2_reduction hrank b1 b2
  rw [hc]
  exact hind _ (Submodule.smul_mem _ c (Submodule.subset_span (by simp)))

/-- Theorem 3.2 (2): `ind D = p²` forces `rank Φ ≥ 3`. -/
theorem theorem_3_2_2 (p : ℕ) (hp : 1 < p) (ind : H2 → ℕ)
    (hind : ∀ x ∈ Submodule.span k ({B.cup B.a1 B.a2} : Set H2), ind x ≤ p)
    (b1 b2 : V)
    (hD : ind (B.cup B.a1 b1 + B.cup B.a2 b2) = p ^ 2) :
    (3 : Cardinal) ≤ Module.rank k ↥B.Phi.range := by
  by_contra h3
  have hlt : Module.rank k ↥B.Phi.range < (3 : Cardinal) := not_le.mp h3
  have hlt3 : Module.rank k ↥B.Phi.range < ((2 : ℕ) : Cardinal) + 1 := by
    rw [show ((2 : ℕ) : Cardinal) + 1 = (3 : Cardinal) by norm_num]
    exact hlt
  have hle2 : Module.rank k ↥B.Phi.range ≤ (2 : Cardinal) :=
    (Cardinal.lt_natCast_add_one_iff (n := 2)).mp hlt3
  have hge2 := B.lemma_3_1_3
  have hrank : Module.rank k ↥B.Phi.range = (2 : Cardinal) := le_antisymm hle2 hge2
  have hle := B.theorem_3_2_1 p ind hind hrank b1 b2
  have hpp : p < p ^ 2 := by nlinarith [sq_nonneg (p : ℤ)]
  omega



/-- Lemma 3.3 (1), conditional on the named hypothesis `hNrd`: the reduced norm
of `D` contains the norm image of the maximal subfield `E`
(`N_{E/F}(E^×) ⊆ Nrd(D^×)`, the input from `prop:prelim-splitting`). -/
theorem lemma_3_3_1
    {WE : Type*} [AddCommGroup WE] [Module k WE]
    (cor : WE →ₗ[k] V) (S : Submodule k V)
    (hNrd : ∀ w, cor w ∈ S) : LinearMap.range cor ≤ S := by
  rintro _ ⟨w, rfl⟩
  exact hNrd w

/-- Lemma 3.3 (2), conditional on the projection formula: the composite norm
image `N = cor H¹(E)` lies in `U^⊥`. -/
theorem lemma_3_3_2
    {WE H2E : Type*} [AddCommGroup WE] [Module k WE]
    [AddCommGroup H2E] [Module k H2E]
    (cor : WE →ₗ[k] V) (resE : V →ₗ[k] WE)
    (hres1 : resE B.a1 = 0) (hres2 : resE B.a2 = 0)
    (cupE : WE →ₗ[k] WE →ₗ[k] H2E) (cor2 : H2E →ₗ[k] H2)
    (hproj : ∀ w v, B.cup (cor w) v = cor2 (cupE w (resE v))) :
    cor.range ≤ B.Uperp := by
  rintro n ⟨w, rfl⟩
  rw [B.mem_Uperp_iff]
  constructor
  · rw [hproj, hres1, map_zero, map_zero]
  · rw [hproj, hres2, map_zero, map_zero]

/-- Lemma 3.3 (3), in the form `U^⊥ ⊆ R`, where `R` is the kernel of cupping
with `[D] = a₁ ∪ b₁ + a₂ ∪ b₂`.  The inputs are the coherence of the degree-1
triple product with the `H²`-cup and its cyclic symmetry (both standard for
cup products of degree-1 classes). -/
theorem lemma_3_3_3
    {H3 : Type*} [AddCommGroup H3] [Module k H3]
    (cupH : V →ₗ[k] H2 →ₗ[k] H3) (cup3 : V →ₗ[k] V →ₗ[k] V →ₗ[k] H3)
    (b1 b2 : V)
    (hcoh : ∀ x y z, cupH x (B.cup y z) = cup3 x y z)
    (hcyc : ∀ x y z, cup3 x y z = cup3 z x y) :
    B.Uperp ≤ LinearMap.ker (cupH.flip (B.cup B.a1 b1 + B.cup B.a2 b2)) := by
  intro v hv
  have hP := B.mem_Uperp_iff v |>.mp hv
  rw [LinearMap.mem_ker, LinearMap.flip_apply, map_add, hcoh v B.a1 b1, hcoh v B.a2 b2]
  rw [hcyc v B.a1 b1, hcyc v B.a2 b2, ← hcoh b1 v B.a1, ← hcoh b2 v B.a2, hP.1, hP.2]
  simp


/-- Theorem 3.5 (2): if `N ⊆ U^⊥`, then
`0 → U^⊥/N → V/(U+N) → V/(U+U^⊥) → 0`. -/
-- @source file=raw/L20261018.tex locator=label:thm:hs-tate-exact-sequences quote="包含映射与商映射诱导自然短正合列"
theorem theorem_3_5_2 (N : Submodule k V) (hNU : N ≤ B.Uperp) :
    ∃ (j : (B.Uperp ⧸ N.comap B.Uperp.subtype) →ₗ[k] (V ⧸ (B.U + N)))
      (q : (V ⧸ (B.U + N)) →ₗ[k] (V ⧸ (B.U + B.Uperp))),
      Function.Injective j ∧ Function.Surjective q ∧ LinearMap.range j = LinearMap.ker q := by
  let N' : Submodule k B.Uperp := N.comap B.Uperp.subtype
  let f : B.Uperp →ₗ[k] V ⧸ (B.U + N) := (B.U + N).mkQ.comp B.Uperp.subtype
  have hf : N' ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (x : V) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have hxN : (x : V) ∈ N := by
      simpa [N'] using hx
    exact Submodule.mem_sup.mpr ⟨0, B.U.zero_mem, x.val, hxN, by simp⟩
  let j : (B.Uperp ⧸ N') →ₗ[k] (V ⧸ (B.U + N)) := Submodule.liftQ N' f hf
  let g : V →ₗ[k] V ⧸ (B.U + B.Uperp) := (B.U + B.Uperp).mkQ
  have hgle : B.U + N ≤ B.U + B.Uperp := by
    simpa using (sup_le_sup_left hNU B.U)
  have hg : B.U + N ≤ LinearMap.ker g := by
    intro x hx
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk x = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hgle hx
  let q : (V ⧸ (B.U + N)) →ₗ[k] (V ⧸ (B.U + B.Uperp)) := Submodule.liftQ (B.U + N) g hg
  have hj : ∀ x : B.Uperp, j (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x : V) := by
    intro x
    simp [j, f, Submodule.liftQ_apply]
  have hq : ∀ v : V, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
    intro v
    simp [q, g, Submodule.liftQ_apply]
  refine ⟨j, q, ?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := (Submodule.Quotient.mk_surjective _) z
    rw [Submodule.mem_bot]
    rw [LinearMap.mem_ker] at hz
    rw [hj] at hz
    have hx : (x : V) ∈ B.U + N := by
      simpa [Submodule.Quotient.mk_eq_zero] using hz
    obtain ⟨u, hu, n, hn, hun⟩ := Submodule.mem_sup.mp hx
    have hu' : u ∈ B.Uperp := by
      have hux : u = (x : V) - n := by rw [← hun]; abel
      rw [hux]
      exact B.Uperp.sub_mem x.2 (hNU hn)
    have hu0 : u = 0 := by
      have : u ∈ B.U ⊓ B.Uperp := ⟨hu, hu'⟩
      rw [B.lemma_3_1_1, Submodule.mem_bot] at this
      exact this
    have hxN : (x : V) ∈ N := by
      rw [← hun, hu0, zero_add]
      exact hn
    rw [Submodule.Quotient.mk_eq_zero]
    simpa [N'] using hxN
  · intro y
    obtain ⟨v, rfl⟩ := (Submodule.Quotient.mk_surjective _) y
    exact ⟨Submodule.Quotient.mk v, by rw [hq]⟩
  · apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := (Submodule.Quotient.mk_surjective _) z
      rw [LinearMap.mem_ker, hj, hq]
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup.mpr ⟨0, B.U.zero_mem, (x : V), x.2, by simp⟩
    · intro y hy
      obtain ⟨v, rfl⟩ := (Submodule.Quotient.mk_surjective _) y
      rw [LinearMap.mem_ker] at hy
      rw [hq] at hy
      have hv : v ∈ B.U + B.Uperp := by
        simpa [Submodule.Quotient.mk_eq_zero] using hy
      obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hv
      refine ⟨Submodule.Quotient.mk ⟨w, hw⟩, ?_⟩
      rw [hj]
      rw [Submodule.Quotient.eq]
      rw [← huw]
      have : (w : V) - (u + w) = -u := by abel
      rw [this]
      exact Submodule.neg_mem _ (Submodule.mem_sup_left hu)


/-- Theorem 3.5 (1): from the Hochschild--Serre five-term sequence (encoded by
`ker res = U`, `ker d₂ = im res`, `im d₂ = K₂`) and the norm identity
`N_G(M) = res(N)`, one obtains
`0 → V/(U+N) → Ĥ⁰(G,M) → K₂ → 0`, with `Ĥ⁰(G,M) = M^G/N_G(M)`. -/
theorem theorem_3_5_1
    {W K2 : Type*} [AddCommGroup W] [Module k W]
    [AddCommGroup K2] [Module k K2]
    (MG : Submodule k W) (resMG : V →ₗ[k] MG) (hker : LinearMap.ker resMG = B.U)
    (NG : Submodule k MG) (N : Submodule k V)
    (hNG : NG = Submodule.map resMG N)
    (d2 : MG →ₗ[k] K2) (hkerd2 : LinearMap.ker d2 = LinearMap.range resMG)
    (hd2surj : LinearMap.range d2 = ⊤) :
    ∃ (φ : (V ⧸ (B.U + N)) →ₗ[k] (MG ⧸ NG)) (ψ : (MG ⧸ NG) →ₗ[k] K2),
      Function.Injective φ ∧ Function.Surjective ψ ∧ LinearMap.range φ = LinearMap.ker ψ := by
  let f : V →ₗ[k] (MG ⧸ NG) := NG.mkQ.comp resMG
  have hf : B.U + N ≤ LinearMap.ker f := by
    intro x hx
    obtain ⟨u, hu, n, hn, hun⟩ := Submodule.mem_sup.mp hx
    rw [LinearMap.mem_ker]
    have hu0 : resMG u = 0 := by
      have : u ∈ LinearMap.ker resMG := by rw [hker]; exact hu
      exact this
    have hn0 : resMG n ∈ NG := by
      rw [hNG]
      exact Submodule.mem_map.mpr ⟨n, hn, rfl⟩
    have hfu : f u = 0 := by
      show Submodule.Quotient.mk (resMG u) = 0
      rw [hu0, Submodule.Quotient.mk_zero]
    have hfn : f n = 0 := by
      show Submodule.Quotient.mk (resMG n) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact hn0
    rw [show x = u + n from hun.symm, map_add, hfu, hfn, add_zero]
  let φ : (V ⧸ (B.U + N)) →ₗ[k] (MG ⧸ NG) := Submodule.liftQ (B.U + N) f hf
  have hφ : ∀ v : V, φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (resMG v) := by
    intro v
    simp [φ, f, Submodule.liftQ_apply]
  have hNGker : NG ≤ LinearMap.ker d2 := by
    intro m hm
    rw [hkerd2]
    rw [hNG] at hm
    obtain ⟨n, hn, rfl⟩ := Submodule.mem_map.mp hm
    exact ⟨n, rfl⟩
  let ψ : (MG ⧸ NG) →ₗ[k] K2 := Submodule.liftQ NG d2 hNGker
  have hψ : ∀ m : MG, ψ (Submodule.Quotient.mk m) = d2 m := by
    intro m
    simp [ψ, Submodule.liftQ_apply]
  refine ⟨φ, ψ, ?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨v, rfl⟩ := (Submodule.Quotient.mk_surjective _) z
    rw [Submodule.mem_bot]
    rw [LinearMap.mem_ker, hφ] at hz
    have hres : resMG v ∈ NG := by
      rw [Submodule.Quotient.mk_eq_zero] at hz
      exact hz
    rw [hNG] at hres
    obtain ⟨n, hn, hnv⟩ := Submodule.mem_map.mp hres
    have hmem : v - n ∈ B.U := by
      have : v - n ∈ LinearMap.ker resMG := by
        rw [LinearMap.mem_ker, map_sub, hnv, sub_self]
      rwa [hker] at this
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup.mpr ⟨v - n, hmem, n, hn, by abel⟩
  · intro y
    obtain ⟨m, rfl⟩ := LinearMap.range_eq_top.mp hd2surj y
    exact ⟨Submodule.Quotient.mk m, by rw [hψ]⟩
  · apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨v, rfl⟩ := (Submodule.Quotient.mk_surjective _) z
      rw [LinearMap.mem_ker, hφ, hψ]
      have : resMG v ∈ LinearMap.ker d2 := by
        rw [hkerd2]; exact ⟨v, rfl⟩
      exact this
    · intro y hy
      obtain ⟨m, rfl⟩ := (Submodule.Quotient.mk_surjective _) y
      rw [LinearMap.mem_ker, hψ] at hy
      have hm : m ∈ LinearMap.range resMG := by
        rw [← hkerd2]; exact hy
      obtain ⟨v, hv⟩ := hm
      refine ⟨Submodule.Quotient.mk v, ?_⟩
      rw [hφ, Submodule.Quotient.eq, hv, sub_self]
      exact NG.zero_mem


/-- The two first-slot classes are linearly independent. -/
lemma linearIndependent_a1a2 : LinearIndependent k ![B.a1, B.a2] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : g 0 • B.a1 + g 1 • B.a2 = 0 := by
    simpa [Fin.sum_univ_two] using hg
  have h0 : g 0 = 0 := by
    have h := congrArg (fun x => B.cup x B.a2) hg'
    have h' : g 0 • B.cup B.a1 B.a2 = 0 := by
      simpa [map_add, map_smul] using h
    exact (smul_eq_zero.mp h').resolve_right B.hne
  have h1 : g 1 = 0 := by
    have h := congrArg (fun x => B.cup x B.a1) hg'
    have h' : g 1 • B.cup B.a1 B.a2 = 0 := by
      simpa [map_add, map_smul] using h
    exact (smul_eq_zero.mp h').resolve_right B.hne
  fin_cases i
  · exact h0
  · exact h1

/-- Dimension additivity for a short exact sequence of finite-dimensional
vector spaces. -/
lemma finrank_ses
    {A B C : Type*} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    [Module.Finite k A] [Module.Finite k B] [Module.Finite k C]
    (φ : A →ₗ[k] B) (ψ : B →ₗ[k] C)
    (hφ : Function.Injective φ) (hψ : Function.Surjective ψ)
    (hex : LinearMap.range φ = LinearMap.ker ψ) :
    Module.finrank k B = Module.finrank k A + Module.finrank k C := by
  have h1 : Module.finrank k ↥ψ.range + Module.finrank k ↥ψ.ker = Module.finrank k B :=
    LinearMap.finrank_range_add_finrank_ker ψ
  have h2 : Module.finrank k ↥ψ.range = Module.finrank k C := by
    rw [LinearMap.range_eq_top.mpr hψ, finrank_top]
  have h3 : Module.finrank k ↥ψ.ker = Module.finrank k A := by
    rw [← hex]
    exact (LinearEquiv.ofInjective φ hφ).finrank_eq.symm
  omega


/-- The standard symplectic plane: `V = k × k`, `H² = k`, `x ∪ y = x₁y₂ - x₂y₁`. -/
def stdCup : (k × k) →ₗ[k] (k × k) →ₗ[k] k :=
  LinearMap.mk₂ k (fun x y : k × k => x.1 * y.2 - x.2 * y.1)
    (by intro x y z; simp; ring)
    (by intro x y z; simp; ring)
    (by intro c x y; simp; ring)
    (by intro c x y; simp; ring)

/-- Nonemptiness of the base: the standard symplectic plane is an instance. -/
def stdBiKummer : BiKummerData k (k × k) k where
  cup := stdCup
  a1 := (1, 0)
  a2 := (0, 1)
  hne := by simp [stdCup]
  skew := by
    intro x y
    simp [stdCup]
    ring

example : Nonempty (BiKummerData k (k × k) k) := ⟨stdBiKummer⟩


/-- Corollary 3.6 (1), subtraction-free form: the three dimension relations. -/
-- @source file=raw/L20261018.tex locator=label:thm:dimension quote="\dim_{\Fp}(U^\perp/N)&=\tau-\kappa-r+2,\\"
theorem theorem_3_6
    [NeZero (2 : k)] [Module.Finite k V]
    (N : Submodule k V) (hNU : N ≤ B.Uperp)
    {H0 K2 : Type*} [AddCommGroup H0] [Module k H0]
    [AddCommGroup K2] [Module k K2] [Module.Finite k H0] [Module.Finite k K2]
    (φ : (V ⧸ (B.U + N)) →ₗ[k] H0) (ψ : H0 →ₗ[k] K2)
    (hφ : Function.Injective φ) (hψ : Function.Surjective ψ)
    (hex : LinearMap.range φ = LinearMap.ker ψ)
    (j : (B.Uperp ⧸ (N.comap B.Uperp.subtype)) →ₗ[k] (V ⧸ (B.U + N)))
    (q : (V ⧸ (B.U + N)) →ₗ[k] (V ⧸ (B.U + B.Uperp)))
    (hj : Function.Injective j) (hq : Function.Surjective q)
    (hex2 : LinearMap.range j = LinearMap.ker q) :
    Module.finrank k (B.Uperp ⧸ (N.comap B.Uperp.subtype))
        + (Module.finrank k ↥B.Phi.range - 2)
        = Module.finrank k H0 - Module.finrank k K2
    ∧ Module.finrank k ↥N
        + Module.finrank k (B.Uperp ⧸ (N.comap B.Uperp.subtype))
        = Module.finrank k ↥B.Uperp
    ∧ Module.finrank k ↥B.Uperp + Module.finrank k ↥B.Phi.range
        = Module.finrank k V := by
  have hΦ : Module.finrank k ↥B.Phi.range + Module.finrank k ↥B.Uperp
      = Module.finrank k V := by
    rw [BiKummerData.Uperp]
    exact LinearMap.finrank_range_add_finrank_ker B.Phi
  have hr : Module.finrank k ↥B.Phi.range ≤ Module.finrank k V := by omega
  have hspan : B.U = Submodule.span k (Set.range (fun i : Fin 2 => ![B.a1, B.a2] i)) := by
    rw [BiKummerData.U, range_fin2]
  have hU : Module.finrank k ↥B.U = 2 := by
    rw [hspan]
    exact finrank_span_eq_card B.linearIndependent_a1a2
  have hU2 : Module.finrank k ↥(B.U ⊔ B.Uperp) = 2 + Module.finrank k ↥B.Uperp := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq B.U B.Uperp
    rw [B.lemma_3_1_1, finrank_bot, add_zero] at h1
    omega
  have hc2 : Module.finrank k (V ⧸ (B.U ⊔ B.Uperp))
      + Module.finrank k ↥(B.U ⊔ B.Uperp) = Module.finrank k V :=
    Submodule.finrank_quotient_add_finrank _
  have hc2' : Module.finrank k (V ⧸ (B.U ⊔ B.Uperp))
      = Module.finrank k ↥B.Phi.range - 2 := by omega
  have hb : Module.finrank k H0
      = Module.finrank k (V ⧸ (B.U + N)) + Module.finrank k K2 := finrank_ses φ ψ hφ hψ hex
  have hjq : Module.finrank k (V ⧸ (B.U + N))
      = Module.finrank k (B.Uperp ⧸ (N.comap B.Uperp.subtype))
        + Module.finrank k (V ⧸ (B.U + B.Uperp)) := finrank_ses j q hj hq hex2
  have hNN : Module.finrank k ↥(N.comap B.Uperp.subtype) = Module.finrank k ↥N := by
    have e := (Submodule.equivMapOfInjective B.Uperp.subtype Subtype.val_injective
      (N.comap B.Uperp.subtype)).finrank_eq
    have hmap : Submodule.map B.Uperp.subtype (N.comap B.Uperp.subtype) = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.mpr hNU
    rwa [hmap] at e
  have hquot : Module.finrank k (B.Uperp ⧸ (N.comap B.Uperp.subtype))
      + Module.finrank k ↥(N.comap B.Uperp.subtype) = Module.finrank k ↥B.Uperp :=
    Submodule.finrank_quotient_add_finrank _
  have hquot' : Module.finrank k ↥N
      + Module.finrank k (B.Uperp ⧸ (N.comap B.Uperp.subtype)) = Module.finrank k ↥B.Uperp := by
    rw [← hNN, add_comm]
    exact hquot
  have hc2'' : Module.finrank k ↥B.Phi.range - 2
      = Module.finrank k (V ⧸ (B.U + B.Uperp)) := hc2'.symm
  have hκτ : Module.finrank k K2 ≤ Module.finrank k H0 := by omega
  have hr2 : 2 ≤ Module.finrank k ↥B.Phi.range := by omega
  have hb' : Module.finrank k H0 - Module.finrank k K2
      = Module.finrank k (V ⧸ (B.U + N)) := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hb', hjq, hc2'']
  · exact hquot'
  · omega



end BiKummerData

end L20261018




open TauCeti

namespace GaloBase

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime]

noncomputable def muP : TopRep (ZMod p) (AbsoluteGaloisGroup K) :=
  letI : DiscreteTopology (ZMod p) := ZMod.instDiscreteTopology
  letI : ContinuousSMul (ZMod p) (ZMod p) := ⟨continuous_of_discreteTopology⟩
  TopRep.of (ContRepresentation.trivial (ZMod p) (AbsoluteGaloisGroup K) (ZMod p))

lemma muP_ρ (g : AbsoluteGaloisGroup K) (x : (muP K p).V) : (muP K p).ρ g x = x := rfl

/-- Ring structure on the carrier, definitionally that of `ZMod p`. -/
instance : Mul (muP K p).V := inferInstanceAs (Mul (ZMod p))
instance : CommMagma (muP K p).V := inferInstanceAs (CommMagma (ZMod p))

noncomputable def muPairing : TopPairing (muP K p) (muP K p) (muP K p) where
  bil := (LinearMap.mk₂ (ZMod p) (fun x y : ZMod p => x * y)
    (by intro x y z; ring)
    (by intro c x y; simp only [smul_eq_mul]; ring)
    (by intro x y z; ring)
    (by intro c x y; simp only [smul_eq_mul]; ring)
    : ZMod p →ₗ[ZMod p] ZMod p →ₗ[ZMod p] ZMod p)
  cont := by
    haveI : DiscreteTopology (muP K p).V := ZMod.instDiscreteTopology
    exact continuous_of_discreteTopology
  equivariant := by intro g x y; rw [muP_ρ, muP_ρ, muP_ρ]

noncomputable abbrev V : Type := ↑(continuousCohomology 1 (muP K p)).toModuleCat
noncomputable abbrev H2 : Type := ↑(continuousCohomology 2 (muP K p)).toModuleCat

noncomputable def cup : V K p →ₗ[ZMod p] V K p →ₗ[ZMod p] H2 K p :=
  (muPairing K p).cup 1 1

lemma muPairing_flip : (muPairing K p).flip = muPairing K p := by
  apply TopPairing.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [TopPairing.flip_bil]
  change y * x = x * y
  exact mul_comm y x

theorem cup_skew (a b : V K p) :
    cup (K := K) (p := p) a b = - cup (K := K) (p := p) b a := by
  have h := TopPairing.cup_gradedComm (muPairing K p) 1 1 a b
  rw [show (1 * 1 : ℕ) = 1 by norm_num, pow_one] at h
  rw [show Nat.add_comm 1 1 = rfl from Subsingleton.elim _ _] at h
  rw [ContinuousCohomology.degreeCast_rfl] at h
  rw [muPairing_flip] at h
  simpa [cup] using h

end GaloBase


namespace L20261018

/-- The paper's base, instantiated at the real TauCeti cup over the absolute Galois
group: the `skew` field is discharged by `cup_skew`, only `hne` remains. -/
noncomputable def galoBiKummer {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    (a1 a2 : GaloBase.V K p) (hne : GaloBase.cup (K := K) (p := p) a1 a2 ≠ 0) :
    BiKummerData (ZMod p) (GaloBase.V K p) (GaloBase.H2 K p) where
  cup := GaloBase.cup (K := K) (p := p)
  a1 := a1
  a2 := a2
  hne := hne
  skew := GaloBase.cup_skew (K := K) (p := p)

example {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
    (a1 a2 : GaloBase.V K p) (hne : GaloBase.cup (K := K) (p := p) a1 a2 ≠ 0) :
    (galoBiKummer a1 a2 hne).U ⊓ (galoBiKummer a1 a2 hne).Uperp = ⊥ :=
  (galoBiKummer a1 a2 hne).lemma_3_1_1

end L20261018

namespace L20261018

/-- Proposition 3.4, first three terms: the inflation map is injective and the
inflation-restriction sequence is exact (mathlib `H1InfRes`). The paper's
instance is `G = G_F`, `S = G_E`, `A = μ_p`; the last two terms (transgression)
are the named hypothesis of `theorem_3_5_1`. -/
theorem prop_3_4_first_three {k G : Type} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal] :
    Function.Injective (groupCohomology.H1InfRes A S).f ∧
      (groupCohomology.H1InfRes A S).Exact := by
  constructor
  · exact (ModuleCat.mono_iff_injective _).1
      (inferInstance : CategoryTheory.Mono (groupCohomology.H1InfRes A S).f)
  · exact groupCohomology.H1InfRes_exact A S

end L20261018

#print axioms GaloBase.cup_skew
#print axioms L20261018.BiKummerData.theorem_3_6
#print axioms L20261018.prop_3_4_first_three
#print axioms L20261018.BiKummerData.lemma_3_3_1
#print axioms L20261018.BiKummerData.theorem_3_5_1
