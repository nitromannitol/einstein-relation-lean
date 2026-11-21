import EinsteinFull.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.Calculus.U6BoundedPhysicalResolvent
import EinsteinFull.Calculus.U5RegularSignedRealization

/-!
# The physical quenched kernel from every starting point

The physical diffusion of Gantert–Mathieu–Piatnitski (2012), Section 7 (p. 32), runs on the
pair `ω = (a₀, V)` itself. This module constructs a physical quenched kernel
(`IsGMPPhysicalKernel`), jointly measurable in the starting point and the environment, as the
measurable selection of the unique solutions of the physical martingale problems. Any physical
origin law agrees with that kernel at the origin, since all realizations of one regular pair
have the same path law from every start.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal Classical

namespace EinsteinFull.Regeneration

/-- A physical origin law is the physical kernel at the origin, for almost every environment. -/
theorem ae_originLaw_eq_of_isGMPPhysicalKernel {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P₀ : Kernel (FieldPair d) (Path d)) (P : QuenchedPathLaws d)
    (hP₀ : IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 P₀)
    (hP : IsGMPPhysicalKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, P₀ ω = P (0, ω) := by
  filter_upwards [hP₀, hP] with ω hω₀ hω
  obtain ⟨hreg, r, hr⟩ := hω₀
  obtain ⟨_, r', hr'⟩ := hω
  rw [hr, hr' 0]
  exact u6_arbitrary_supplied_gmp_pathLaw_unique hd Λ₀ Q.ellipticity_parameter ω hreg lam
    h0 h1 r r' 0

/-- Diffusion matrix of the physical family over all environments: `a₀` on the regular set and
the identity off it. -/
noncomputable def physicalFamilyMatrix {d : ℕ} (Λ : ℝ) (ω : FieldPair d) (y : Vec d) : Mat d :=
  if IsRegular Λ ω then ω.1 y else 1

/-- Drift of the physical family over all environments: the physical drift on the regular set
and zero off it. -/
noncomputable def physicalFamilyDrift {d : ℕ} (Λ : ℝ) (i : Fin d) (lam : ℝ) (ω : FieldPair d)
    (y : Vec d) : Vec d :=
  if IsRegular Λ ω then physicalDrift ω i lam y else 0

theorem physicalFamilyMatrix_eq_of_regular {d : ℕ} {Λ : ℝ} {ω : FieldPair d}
    (hreg : IsRegular Λ ω) : physicalFamilyMatrix Λ ω = ⇑ω.1 :=
  funext fun y => by
    unfold physicalFamilyMatrix
    rw [ite_eq_left hreg]

theorem physicalFamilyDrift_eq_of_regular {d : ℕ} {Λ : ℝ} {ω : FieldPair d} (i : Fin d)
    (lam : ℝ) (hreg : IsRegular Λ ω) : physicalFamilyDrift Λ i lam ω = physicalDrift ω i lam :=
  funext fun y => by
    unfold physicalFamilyDrift
    rw [ite_eq_left hreg]

theorem measurable_physicalFamilyMatrix {d : ℕ} (Λ : ℝ) (i j : Fin d) :
    Measurable fun p : FieldPair d × Vec d => physicalFamilyMatrix Λ p.1 p.2 i j := by
  have hS : MeasurableSet {p : FieldPair d × Vec d | IsRegular Λ p.1} :=
    (Calculus.Feller.measurableSet_setOf_isRegular d Λ).preimage measurable_fst
  have e : (fun p : FieldPair d × Vec d => physicalFamilyMatrix Λ p.1 p.2 i j) = fun p =>
      if IsRegular Λ p.1 then p.1.1 p.2 i j else (1 : Mat d) i j := by
    funext p
    unfold physicalFamilyMatrix
    split_ifs <;> rfl
  rw [e]
  refine Measurable.ite hS ?_ measurable_const
  have h2 : Continuous fun p : FieldPair d × Vec d => p.1.1 p.2 :=
    ContinuousEval.continuous_eval.comp
      (((continuous_fst.comp continuous_fst).prodMk continuous_snd))
  exact (h2.matrix_elem i j).measurable

theorem measurable_physicalFamilyDrift {d : ℕ} (Λ : ℝ) (i : Fin d) (lam : ℝ) (k : Fin d) :
    Measurable fun p : FieldPair d × Vec d => physicalFamilyDrift Λ i lam p.1 p.2 k := by
  have hS : MeasurableSet {p : FieldPair d × Vec d | IsRegular Λ p.1} :=
    (Calculus.Feller.measurableSet_setOf_isRegular d Λ).preimage measurable_fst
  have e : (fun p : FieldPair d × Vec d => physicalFamilyDrift Λ i lam p.1 p.2 k) = fun p =>
      if IsRegular Λ p.1 then (clockDensity p.1 p.2)⁻¹ * famB Λ i lam p.1 p.2 k
        else (0 : Vec d) k := by
    funext p
    unfold physicalFamilyDrift physicalDrift famB
    split_ifs <;> rfl
  rw [e]
  refine Measurable.ite hS ?_ measurable_const
  have hc : Continuous fun p : FieldPair d × Vec d => clockDensity p.1 p.2 := by
    have h1 : Continuous fun p : FieldPair d × Vec d => p.1.2 p.2 :=
      ContinuousEval.continuous_eval.comp
        (((continuous_snd.comp continuous_fst).prodMk continuous_snd))
    exact Real.continuous_exp.comp (continuous_const.mul h1)
  exact (hc.measurable.inv).mul (measurable_famB Λ i lam k)

theorem physicalFamily_bounds {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) (i : Fin d) (lam : ℝ) :
    ∃ M : ℝ,
      (∀ (ω : FieldPair d) (y : Vec d) (a b : Fin d), |physicalFamilyMatrix Λ ω y a b| ≤ M) ∧
      ∀ (ω : FieldPair d) (y : Vec d) (k : Fin d), |physicalFamilyDrift Λ i lam ω y k| ≤ M := by
  obtain ⟨M, -, hB⟩ := family_bounds hΛ i lam
  refine ⟨max 1 (max Λ (Real.exp (2 * Λ) * M)), ?_, ?_⟩
  · intro ω y a b
    by_cases hreg : IsRegular Λ ω
    · unfold physicalFamilyMatrix
      rw [ite_eq_left hreg]
      exact (abs_apply_le_of_isElliptic hΛ hreg.1 y a b).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · unfold physicalFamilyMatrix
      rw [ite_eq_right hreg]
      refine le_trans ?_ (le_max_left _ _)
      rcases eq_or_ne a b with rfl | hab
      · simp
      · simp [hab]
  · intro ω y k
    by_cases hreg : IsRegular Λ ω
    · unfold physicalFamilyDrift
      rw [ite_eq_left hreg]
      have hb := hB ω y k
      rw [famB_eq_of_regular i lam hreg] at hb
      unfold physicalDrift
      rw [abs_mul]
      refine (mul_le_mul (abs_clockDensity_inv_le hreg y) hb (abs_nonneg _)
        (Real.exp_pos _).le).trans ?_
      exact (le_max_right _ _).trans (le_max_right _ _)
    · unfold physicalFamilyDrift
      rw [ite_eq_right hreg]
      simp only [Pi.zero_apply, abs_zero]
      exact zero_le_one.trans (le_max_left _ _)

/-- A jointly measurable family of solutions of the physical martingale problems in textbook
form, at every regular environment and every start. -/
theorem physical_textbook_kernel_all_starts {d : ℕ} (hd : 1 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    (i : Fin d) (lam : ℝ) :
    ∃ K : Kernel (FieldPair d × Vec d) (Path d), IsMarkovKernel K ∧
      ∀ ω : FieldPair d, IsRegular Λ ω → ∀ x : Vec d,
        SolvesMartingaleProblem
          (External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)) x (K (ω, x)) := by
  let : PolishSpace (FieldPair d) := fieldPair_polish d
  let A : (FieldPair d × Vec d) → Vec d → Mat d := fun p => physicalFamilyMatrix Λ p.1
  let B : (FieldPair d × Vec d) → Vec d → Vec d := fun p => physicalFamilyDrift Λ i lam p.1
  obtain ⟨M, hAb, hBb⟩ := physicalFamily_bounds hΛ i lam
  have hAm : ∀ a b, Measurable fun p : (FieldPair d × Vec d) × Vec d =>
      A p.1 p.2 a b := fun a b => (measurable_physicalFamilyMatrix Λ a b).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hBm : ∀ k, Measurable fun p : (FieldPair d × Vec d) × Vec d =>
      B p.1 p.2 k := fun k => (measurable_physicalFamilyDrift Λ i lam k).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hR := u5_measurableSet_solutionRelation_start A B hAm hBm
    (fun θ y a b => hAb θ.1 y a b) (fun θ y k => hBb θ.1 y k)
    Prod.snd measurable_snd
  have huniq : ∀ p : FieldPair d × Vec d, ∃! P : Measure (Path d),
      SolvesMartingaleProblem (External.Draft.svGenerator (A p) (B p)) p.2 P := by
    intro ⟨ω, x⟩
    by_cases hreg : IsRegular Λ ω
    · change ∃! P : Measure (Path d), SolvesMartingaleProblem
        (External.Draft.svGenerator (physicalFamilyMatrix Λ ω)
          (physicalFamilyDrift Λ i lam ω)) x P
      rw [physicalFamilyMatrix_eq_of_regular hreg, physicalFamilyDrift_eq_of_regular i lam hreg]
      obtain ⟨hc, hs, hb, he, hm, hbd⟩ := physical_svHypotheses hΛ hreg i lam
      exact foundation_textbook_well_posed d hd (⇑ω.1) (physicalDrift ω i lam)
        hc hs hb he hm hbd x
    · have e1 : physicalFamilyMatrix Λ ω = fun _ => 1 := funext fun y => by
        unfold physicalFamilyMatrix
        rw [ite_eq_right hreg]
      have e2 : physicalFamilyDrift Λ i lam ω = fun _ => 0 := funext fun y => by
        unfold physicalFamilyDrift
        rw [ite_eq_right hreg]
      change ∃! P : Measure (Path d), SolvesMartingaleProblem
        (External.Draft.svGenerator (physicalFamilyMatrix Λ ω)
          (physicalFamilyDrift Λ i lam ω)) x P
      rw [e1, e2]
      refine foundation_textbook_well_posed d hd (fun _ => 1) (fun _ => 0)
        continuous_const (fun _ => Matrix.transpose_one) ⟨1, fun _ a b => ?_⟩
        ⟨1, one_pos, fun y ξ => ?_⟩ measurable_const ⟨0, fun _ k => by simp⟩ x
      · rcases eq_or_ne a b with rfl | hab
        · simp
        · simp [hab]
      · simp [euclideanSq, Matrix.one_mulVec]
  obtain ⟨g, hg, hgs⟩ := exists_measurable_selector_measure
    (fun p P => SolvesMartingaleProblem (External.Draft.svGenerator (A p) (B p)) p.2 P)
    (fun _ _ h => h.1) huniq hR
  let K : Kernel (FieldPair d × Vec d) (Path d) := ⟨g, hg⟩
  refine ⟨K, ⟨fun p => (hgs p).1⟩, ?_⟩
  intro ω hω x
  have h := hgs (ω, x)
  change SolvesMartingaleProblem
    (External.Draft.svGenerator (physicalFamilyMatrix Λ ω)
      (physicalFamilyDrift Λ i lam ω)) x (K (ω, x)) at h
  rw [physicalFamilyMatrix_eq_of_regular hω, physicalFamilyDrift_eq_of_regular i lam hω] at h
  exact h

/-- A jointly measurable physical kernel realizes the regular law at every start. -/
theorem joint_physical_kernel_exists {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ P : QuenchedPathLaws d, IsGMPPhysicalKernel hd Q.ellipticity_parameter Q lam h0 h1 P := by
  have hΛpos : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨K, hK, hsel⟩ := physical_textbook_kernel_all_starts
    (by omega : 1 ≤ d) hΛpos (firstCoordinateIndex hd) lam
  let : IsMarkovKernel K := hK
  let P : QuenchedPathLaws d := K.comap (fun p => (p.2, p.1))
    (measurable_snd.prodMk measurable_fst)
  refine ⟨P, ?_⟩
  filter_upwards [Q.regular] with ω hω
  obtain ⟨R, -, hMP⟩ := u5_regular_signed_fixed_environment_realization_and_mp
    hd Q.ellipticity_parameter ω hω lam h0 h1
  refine ⟨hω, R, ?_⟩
  intro x
  have htextK := hsel ω hω x
  let : IsProbabilityMeasure (R.pathLaw x) :=
    R.pathLaw_isMarkovKernel.isProbabilityMeasure x
  have hmarg : ∀ t : ℝ≥0, 0 < t →
      (R.pathLaw x).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
    intro t ht
    rw [R.pathLaw_endpoint, R.transitionKernel_eq_heatKernel t ht x]
    exact withDensity_absolutelyContinuous _ _
  have htextR := c4_textbook_solves_of_physical_and_averaged_occupation
    hΛpos hω (firstCoordinateIndex hd) lam (hMP x)
    (u2_averaged_occupation_ac_of_marginals (R.pathLaw x) hmarg)
  obtain ⟨hc, hs, hb, he, hm, hbd⟩ :=
    physical_svHypotheses hΛpos hω (firstCoordinateIndex hd) lam
  obtain ⟨S, _, hu⟩ := foundation_textbook_well_posed d (by omega) (⇑ω.1)
    (physicalDrift ω (firstCoordinateIndex hd) lam) hc hs hb he hm hbd x
  change K (ω, x) = R.pathLaw x
  exact (hu _ htextK).trans (hu _ htextR).symm

/-- The physical laws are carried by a globally Markov path kernel with all starts correct and
absolutely continuous positive-time endpoints, equal to the physical realizations from every
start for almost every environment. -/
theorem global_physical_kernel_exists {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ P : QuenchedPathLaws d,
      IsGMPPhysicalKernel hd Q.ellipticity_parameter Q lam h0 h1 P ∧
      IsMarkovKernel P ∧
      (∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) ∧
      (∀ (a : Vec d × FieldPair d) (t : ℝ≥0), 0 < t →
        (P a).map (pathPosition t) ≪ (volume : Measure (Vec d))) := by
  classical
  obtain ⟨P, hP⟩ := joint_physical_kernel_exists hd Q lam h0 h1
  let Good : FieldPair d → Prop := fun ω =>
    ∃ hω : IsRegular Λ₀ ω,
      ∃ r : GantertFixedEnvironmentRealization hd Λ₀ Q.ellipticity_parameter ω hω lam h0 h1,
        ∀ x, P (x, ω) = r.pathLaw x
  have hgood : ∀ᵐ ω ∂Q.measure, Good ω := hP
  obtain ⟨N, hsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hE : ∀ᵐ ω ∂Q.measure, ω ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hNzero
  obtain ⟨ω₀, hω₀⟩ := hE.exists
  have hG : ∀ ω, ω ∉ N → Good ω := by
    intro ω hω
    by_contra hn
    exact hω (hsub hn)
  let f : FieldPair d → FieldPair d := fun ω => if ω ∈ N then ω₀ else ω
  have hf : Measurable f := measurable_const.piecewise hNm measurable_id
  have hfGood : ∀ ω, Good (f ω) := by
    intro ω
    by_cases hω : ω ∈ N
    · simpa [f, hω] using hG ω₀ hω₀
    · simpa [f, hω] using hG ω hω
  let P' : QuenchedPathLaws d := P.comap (fun a => (a.1, f a.2))
    (measurable_fst.prodMk (hf.comp measurable_snd))
  have heq (x : Vec d) (ω : FieldPair d) : P' (x, ω) = P (x, f ω) := rfl
  have hae : ∀ᵐ ω ∂Q.measure, ∀ x, P' (x, ω) = P (x, ω) := by
    filter_upwards [hE] with ω hω
    intro x
    simp only [heq, f, ite_eq_right hω]
  refine ⟨P', ?_, ?_, ?_, ?_⟩
  · filter_upwards [hP, hae] with ω hω he
    obtain ⟨hr, r, hrow⟩ := hω
    exact ⟨hr, r, fun x => (he x).trans (hrow x)⟩
  · constructor
    intro a
    obtain ⟨_, r, hr⟩ := hfGood a.2
    rw [heq, hr a.1]
    let := r.pathLaw_isMarkovKernel
    infer_instance
  · intro a
    obtain ⟨_, r, hr⟩ := hfGood a.2
    rw [heq, hr a.1]
    exact r.pathLaw_starts_at a.1
  · intro a t ht
    obtain ⟨_, r, hr⟩ := hfGood a.2
    rw [heq, hr a.1, r.pathLaw_endpoint, r.transitionKernel_eq_heatKernel t ht a.1]
    exact withDensity_absolutelyContinuous _ _

/-- The jointly measurable physical kernel, read at the reduced bound. -/
theorem joint_physical_kernel_exists_reducedBound {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ P : QuenchedPathLaws d,
      IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P := by
  obtain ⟨P, hP⟩ := joint_physical_kernel_exists hd Q lam h0 h1
  exact ⟨P, hP.reducedBound⟩

/-- The globally Markov physical kernel, read at the reduced bound. -/
theorem global_physical_kernel_exists_reducedBound {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ P : QuenchedPathLaws d,
      IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P ∧
      IsMarkovKernel P ∧
      (∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) ∧
      (∀ (a : Vec d × FieldPair d) (t : ℝ≥0), 0 < t →
        (P a).map (pathPosition t) ≪ (volume : Measure (Vec d))) := by
  obtain ⟨P, hP, h1, h2, h3⟩ := global_physical_kernel_exists hd Q lam h0 h1
  exact ⟨P, hP.reducedBound, h1, h2, h3⟩

end EinsteinFull.Regeneration
