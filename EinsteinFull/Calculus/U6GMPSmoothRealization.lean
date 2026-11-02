import EinsteinFull.Calculus.K11GMPRealizationFields
import EinsteinFull.Calculus.C4FoundationPhysicalLawUniqueness
import EinsteinFull.Calculus.U2GMPHeatDensity
import EinsteinFull.Calculus.U2GMPKernelReversibility
import EinsteinFull.Calculus.U8PhysicalUltracontractive
import EinsteinFull.Calculus.U3ForcedHorizonLaw

open EinsteinRelation MeasureTheory
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

noncomputable section
namespace EinsteinFull

/-- The path law used by the fixed-environment construction solves the physical
martingale problem at every starting point, for any signed force. -/
theorem u6_gmpPhysicalPathLaw_solves_martingale_problem
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (x : Vec d) : SolvesMartingaleProblem
      (physicalGenerator (firstCoordinateIndex hd) ω lam) x
      (Blueprint.gmpPhysicalPathLaw hd ω lam Λ hΛ hω hSmooth x) := by
  let K := Blueprint.gmpPhysicalPathLaw hd ω lam Λ hΛ hω hSmooth
  let : ProbabilityTheory.IsMarkovKernel K :=
    Blueprint.gmpPhysicalPathLaw_isMarkovKernel hd ω lam Λ hΛ hω hSmooth
  exact c4_gmpPhysical_realization_solves_martingale_problem hd ω lam Λ hΛ hω hSmooth K
    (Blueprint.gmpPhysicalPathLaw_spec hd ω lam Λ hΛ hω hSmooth).2 x

/-- The actual physical path law is the inverse-clock image of any reduced
martingale-problem solution from the same point and with the same signed force. -/
theorem u6_gmpPhysicalPathLaw_eq_timeChange_of_reduced_solution
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (x : Vec d) (P : Measure (Path d))
    (hP : SolvesMartingaleProblem (reducedGenerator (firstCoordinateIndex hd) ω lam) x P) :
    Blueprint.gmpPhysicalPathLaw hd ω lam Λ hΛ hω hSmooth x =
      P.map (timeChangeMap hω) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hphysical := c16_time_change_solves_of_regular hΛpos hω
    (firstCoordinateIndex hd) lam x hP
  obtain ⟨Q, _, huniq⟩ := exists_unique_physical_solution
    foundation_textbook_well_posed hΛpos hω hSmooth (firstCoordinateIndex hd) lam x
  exact (huniq _ (u6_gmpPhysicalPathLaw_solves_martingale_problem
    hd ω lam Λ hΛ hω hSmooth x)).trans (huniq _ hphysical).symm

/-- The Radon–Nikodym heat kernel of the actual physical transition law. -/
def u6GmpPhysicalHeatKernel {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (x y : Vec d) : ℝ≥0∞ :=
  (Blueprint.gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth t x).rnDeriv
    (volume : Measure (Vec d)) y

/-- The endpoint variable of the actual Radon–Nikodym heat kernel is measurable. -/
theorem u6_gmpPhysicalHeatKernel_measurable {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (x : Vec d) :
    Measurable (u6GmpPhysicalHeatKernel hd ω lam Λ hΛ hω hSmooth t x) :=
  Measure.measurable_rnDeriv _ _

/-- Domination of path laws on the past at a fixed time transfers to their
endpoint distributions at that time. -/
theorem u6_endpoint_absolutelyContinuous_of_past {d : ℕ} (T : ℝ≥0)
    (P R : Measure (Path d))
    (h : ∀ A : Set (Path d), MeasurableSet[pathFiltration d T] A →
      P A = 0 → R A = 0) :
    R.map (pathPosition T) ≪ P.map (pathPosition T) := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro S hS hzero
  have hpast : MeasurableSet[pathFiltration d T] (pathPosition T ⁻¹' S) := by
    exact (Filtration.stronglyAdapted_natural
      (fun t => (measurable_pathPosition (d := d) t).stronglyMeasurable) T).measurable hS
  rw [Measure.map_apply (measurable_pathPosition T) hS] at hzero ⊢
  exact h _ hpast hzero

/-- A single finite-horizon domination controls the endpoint law at every
earlier time. -/
theorem u6_endpoint_absolutelyContinuous_of_later_past {d : ℕ} (t T : ℝ≥0)
    (ht : t ≤ T) (P R : Measure (Path d))
    (h : ∀ A : Set (Path d), MeasurableSet[pathFiltration d T] A →
      P A = 0 → R A = 0) :
    R.map (pathPosition t) ≪ P.map (pathPosition t) := by
  apply u6_endpoint_absolutelyContinuous_of_past t P R
  intro A hA hzero
  exact h A ((pathFiltration d).mono ht A hA) hzero

/-- A finite-horizon density formula implies domination on the same past. -/
theorem u6_past_domination_of_density {d : ℕ} (T : ℝ≥0)
    (P R : Measure (Path d)) (Z : Path d → ℝ≥0∞)
    (h : ∀ A : Set (Path d), MeasurableSet[pathFiltration d T] A →
      R A = ∫⁻ γ in A, Z γ ∂P) :
    ∀ A : Set (Path d), MeasurableSet[pathFiltration d T] A →
      P A = 0 → R A = 0 := by
  intro A hA hzero
  rw [h A hA, Measure.restrict_eq_zero.mpr hzero, lintegral_zero_measure]

/-- Inverse-clock transport preserves finite-horizon domination, using the
deterministic bound on the inverse clock for the given physical horizon. -/
theorem u6_timeChange_past_domination {d : ℕ} {Λ : ℝ} {ω : FieldPair d}
    (hω : IsRegular Λ ω) (T : ℝ≥0) (P R : Measure (Path d))
    (h : ∀ A : Set (Path d),
      MeasurableSet[pathFiltration d (Real.toNNReal (Real.exp (2 * Λ) * T))] A →
      P A = 0 → R A = 0) :
    ∀ B : Set (Path d), MeasurableSet[pathFiltration d T] B →
      P.map (timeChangeMap hω) B = 0 → R.map (timeChangeMap hω) B = 0 := by
  intro B hB hzero
  let σ := isStoppingTime_inversePhysicalPathClock_canonical hω T
  have hbound : ∀ γ : Path d,
      ((EinsteinRelation.Clock.InverseMeaningV3.inversePhysicalPathClock ω γ Λ hω T : ℝ≥0) :
        WithTop ℝ≥0) ≤ Real.toNNReal (Real.exp (2 * Λ) * T) := by
    intro γ
    exact WithTop.coe_le_coe.mpr (NNReal.le_toNNReal_of_coe_le
      (EinsteinRelation.Clock.InverseMeaningV3.inversePhysicalPathClock_bounds ω γ Λ hω T).2)
  have hBc : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) T] B := by
    rw [← pathFiltration_eq_canonical]
    exact hB
  have hpre : MeasurableSet[pathFiltration d (Real.toNNReal (Real.exp (2 * Λ) * T))]
      (timeChangeMap hω ⁻¹' B) := by
    rw [pathFiltration_eq_canonical]
    exact (σ.measurableSpace_le_of_le_const hbound) _
      (measurable_timeChangeMap_stopped hω T hBc)
  have hBm : MeasurableSet B := (pathFiltration d).le T B hB
  rw [Measure.map_apply (measurable_timeChangeMap hω) hBm] at hzero ⊢
  exact h _ hpre hzero

/-- A reduced-law horizon domination transfers to domination of the actual
physical transition kernels at the same time and starting point. -/
theorem u6_physical_transition_absolutelyContinuous_of_reduced_past
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (T : ℝ≥0) (x : Vec d) (P R : Measure (Path d))
    (hP : SolvesMartingaleProblem (reducedGenerator (firstCoordinateIndex hd) ω 0) x P)
    (hR : SolvesMartingaleProblem (reducedGenerator (firstCoordinateIndex hd) ω lam) x R)
    (h : ∀ A : Set (Path d),
      MeasurableSet[pathFiltration d (Real.toNNReal (Real.exp (2 * Λ) * T))] A →
      P A = 0 → R A = 0) :
    Blueprint.gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth T x ≪
      Blueprint.gmpPhysicalTransitionKernel hd ω 0 Λ hΛ hω hSmooth T x := by
  have hdom := u6_timeChange_past_domination hω T P R h
  have hend := u6_endpoint_absolutelyContinuous_of_past T
    (P.map (timeChangeMap hω)) (R.map (timeChangeMap hω)) hdom
  rw [← u6_gmpPhysicalPathLaw_eq_timeChange_of_reduced_solution
      hd ω 0 Λ hΛ hω hSmooth x P hP,
    ← u6_gmpPhysicalPathLaw_eq_timeChange_of_reduced_solution
      hd ω lam Λ hΛ hω hSmooth x R hR,
    Blueprint.gmpPhysicalPathLaw_endpoint hd ω 0 Λ hΛ hω hSmooth,
    Blueprint.gmpPhysicalPathLaw_endpoint hd ω lam Λ hΛ hω hSmooth] at hend
  exact hend

/-- The textbook reduced laws used for signed-force comparison give the
same domination of the actual physical transition kernels. -/
theorem u6_physical_transition_absolutelyContinuous_of_textbook_past
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (T : ℝ≥0) (x : Vec d) (P R : Measure (Path d))
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) 0)) x P)
    (hR : SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) lam)) x R)
    (h : ∀ A : Set (Path d),
      MeasurableSet[pathFiltration d (Real.toNNReal (Real.exp (2 * Λ) * T))] A →
      P A = 0 → R A = 0) :
    Blueprint.gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth T x ≪
      Blueprint.gmpPhysicalTransitionKernel hd ω 0 Λ hΛ hω hSmooth T x := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hPocc := foundation_reduced_textbook_averaged_occupation_ac_of_two_le
    hd hΛpos hω (firstCoordinateIndex hd) 0 hP
  have hRocc := foundation_reduced_textbook_averaged_occupation_ac_of_two_le
    hd hΛpos hω (firstCoordinateIndex hd) lam hR
  exact u6_physical_transition_absolutelyContinuous_of_reduced_past
    hd ω lam Λ hΛ hω hSmooth T x P R
    (c16_reduced_solves_of_textbook_and_averaged_occupation
      hΛpos hω (firstCoordinateIndex hd) 0 hP hPocc)
    (c16_reduced_solves_of_textbook_and_averaged_occupation
      hΛpos hω (firstCoordinateIndex hd) lam hR hRocc) h

/-- The fixed-environment realization at zero force. -/
theorem u6_gmp_smooth_fixed_environment_realization_zero
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    Nonempty (GantertFixedEnvironmentRealization hd Λ hΛ ω hω 0 le_rfl
      (by norm_num)) := by
  have hac : ∀ t : ℝ≥0, 0 < t → ∀ x,
      Blueprint.gmpPhysicalTransitionKernel hd ω 0 Λ hΛ hω hSmooth t x ≪
        (volume : Measure (Vec d)) := by
    intro t ht x
    obtain ⟨M, hM, hbound⟩ := u8_unforced_physical_L1_to_Linfty hd ω Λ hΛ hω t ht
    obtain ⟨p, _, _, hp⟩ := u2_unforced_kernel_real_density_of_L1_to_Linfty
      hd ω Λ hΛ hω hSmooth t M hM.le hbound
    change Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x ≪ _
    rw [hp x]
    exact withDensity_absolutelyContinuous _ _
  refine ⟨{
    pathLaw := Blueprint.gmpPhysicalPathLaw hd ω 0 Λ hΛ hω hSmooth
    transitionKernel := Blueprint.gmpPhysicalTransitionKernel hd ω 0 Λ hΛ hω hSmooth
    heatKernel := u6GmpPhysicalHeatKernel hd ω 0 Λ hΛ hω hSmooth
    pathLaw_isMarkovKernel := Blueprint.gmpPhysicalPathLaw_isMarkovKernel hd ω 0 Λ hΛ hω hSmooth
    transitionKernel_isMarkovKernel := Blueprint.gmpPhysicalTransitionKernel_isMarkovKernel hd ω 0 Λ hΛ hω hSmooth
    transitionKernel_zero := Blueprint.gmpPhysicalTransitionKernel_zero hd ω 0 Λ hΛ hω hSmooth
    transitionKernel_add := Blueprint.gmpPhysicalTransitionKernel_add hd ω 0 Λ hΛ hω hSmooth
    transitionKernel_reversible := ?_
    pathLaw_starts_at := Blueprint.gmpPhysicalPathLaw_starts_at hd ω 0 Λ hΛ hω hSmooth
    heatKernel_aeMeasurable := ?_
    transitionKernel_eq_heatKernel := ?_
    pathLaw_endpoint := Blueprint.gmpPhysicalPathLaw_endpoint hd ω 0 Λ hΛ hω hSmooth
    pathLaw_ordered_finite_dimensional := Blueprint.gmpPhysicalPathLaw_ordered_finite_dimensional hd ω 0 Λ hΛ hω hSmooth
    closedForm_domain := ?_
    closedForm_value := ?_
  }⟩
  · intro t A B hA hB
    exact u2_gmpPhysicalC0KernelSemigroup_measurable_rectangles hd ω 0 Λ hΛ hω hSmooth t A B hA hB
  · intro t ht x
    exact (u6_gmpPhysicalHeatKernel_measurable hd ω 0 Λ hΛ hω hSmooth t x).aemeasurable
  · intro t ht x
    letI : IsProbabilityMeasure
        (Blueprint.gmpPhysicalTransitionKernel hd ω 0 Λ hΛ hω hSmooth t x) :=
      ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω 0 Λ hΛ hω hSmooth t x⟩
    exact (Measure.withDensity_rnDeriv_eq _ _ (hac t ht x)).symm
  · intro f hf
    exact u1_gmpPhysical_kernel_closedForm_domain hd ω 0 Λ hΛ hω hSmooth f hf
  · intro f q hq u hu
    exact u1_gmpPhysical_kernel_closedForm_value hd ω 0 Λ hΛ hω hSmooth f q hq u hu

/-- The actual physical kernels have a density at every positive time and start. -/
theorem u6_physical_transition_absolutelyContinuous_volume
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    Blueprint.gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth t x ≪
      (volume : Measure (Vec d)) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  obtain ⟨P, hP, _⟩ := foundation_reduced_textbook_well_posed
    (le_trans (by norm_num : 1 ≤ 2) hd) hΛpos hω (firstCoordinateIndex hd) 0 x
  obtain ⟨R, hR, _⟩ := foundation_reduced_textbook_well_posed
    (le_trans (by norm_num : 1 ≤ 2) hd) hΛpos hω (firstCoordinateIndex hd) lam x
  have hdom := u6_physical_transition_absolutelyContinuous_of_textbook_past
    hd ω lam Λ hΛ hω hSmooth t x P R hP hR
    (u6_past_domination_of_density _ P R _
      (u3_reduced_force_finite_horizon_law
        (le_trans (by norm_num : 1 ≤ 2) hd) hΛpos hω (firstCoordinateIndex hd)
        hP lam _ hR))
  obtain ⟨M, hM, hbound⟩ := u8_unforced_physical_L1_to_Linfty hd ω Λ hΛ hω t ht
  obtain ⟨p, _, _, hp⟩ := u2_unforced_kernel_real_density_of_L1_to_Linfty
    hd ω Λ hΛ hω hSmooth t M hM.le hbound
  have hzero : Blueprint.gmpPhysicalTransitionKernel hd ω 0 Λ hΛ hω hSmooth t x ≪
      (volume : Measure (Vec d)) := by
    change Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x ≪ _
    rw [hp x]
    exact withDensity_absolutelyContinuous _ _
  exact hdom.trans hzero

/-- The smooth fixed-environment realization exists for the full force range. -/
def u6GmpSmoothFixedEnvironmentRealization
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1 := by
  have hac : ∀ t : ℝ≥0, 0 < t → ∀ x,
      Blueprint.gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth t x ≪
        (volume : Measure (Vec d)) :=
    fun t ht x => u6_physical_transition_absolutelyContinuous_volume
      hd ω lam Λ hΛ hω hSmooth t ht x
  refine {
    pathLaw := Blueprint.gmpPhysicalPathLaw hd ω lam Λ hΛ hω hSmooth
    transitionKernel := Blueprint.gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth
    heatKernel := u6GmpPhysicalHeatKernel hd ω lam Λ hΛ hω hSmooth
    pathLaw_isMarkovKernel := Blueprint.gmpPhysicalPathLaw_isMarkovKernel hd ω lam Λ hΛ hω hSmooth
    transitionKernel_isMarkovKernel := Blueprint.gmpPhysicalTransitionKernel_isMarkovKernel hd ω lam Λ hΛ hω hSmooth
    transitionKernel_zero := Blueprint.gmpPhysicalTransitionKernel_zero hd ω lam Λ hΛ hω hSmooth
    transitionKernel_add := Blueprint.gmpPhysicalTransitionKernel_add hd ω lam Λ hΛ hω hSmooth
    transitionKernel_reversible := ?_
    pathLaw_starts_at := Blueprint.gmpPhysicalPathLaw_starts_at hd ω lam Λ hΛ hω hSmooth
    heatKernel_aeMeasurable := ?_
    transitionKernel_eq_heatKernel := ?_
    pathLaw_endpoint := Blueprint.gmpPhysicalPathLaw_endpoint hd ω lam Λ hΛ hω hSmooth
    pathLaw_ordered_finite_dimensional := Blueprint.gmpPhysicalPathLaw_ordered_finite_dimensional hd ω lam Λ hΛ hω hSmooth
    closedForm_domain := ?_
    closedForm_value := ?_
  }
  · intro t A B hA hB
    exact u2_gmpPhysicalC0KernelSemigroup_measurable_rectangles hd ω lam Λ hΛ hω hSmooth t A B hA hB
  · intro t ht x
    exact (u6_gmpPhysicalHeatKernel_measurable hd ω lam Λ hΛ hω hSmooth t x).aemeasurable
  · intro t ht x
    letI : IsProbabilityMeasure
        (Blueprint.gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth t x) :=
      ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
    exact (Measure.withDensity_rnDeriv_eq _ _ (hac t ht x)).symm
  · intro f hf
    exact u1_gmpPhysical_kernel_closedForm_domain hd ω lam Λ hΛ hω hSmooth f hf
  · intro f q hq u hu
    exact u1_gmpPhysical_kernel_closedForm_value hd ω lam Λ hΛ hω hSmooth f q hq u hu

/-- The smooth fixed-environment realization exists for the full force range. -/
theorem u6_gmp_smooth_fixed_environment_realization_exists
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Nonempty (EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1) :=
  ⟨u6GmpSmoothFixedEnvironmentRealization hd hΛ ω hω hSmooth lam h0 h1⟩

#print axioms u6_gmp_smooth_fixed_environment_realization_exists
#print axioms u6_physical_transition_absolutelyContinuous_volume
#print axioms u6_gmp_smooth_fixed_environment_realization_zero
#print axioms u6_past_domination_of_density
#print axioms u6_physical_transition_absolutelyContinuous_of_textbook_past
#print axioms u6_physical_transition_absolutelyContinuous_of_reduced_past
#print axioms u6_gmpPhysicalPathLaw_eq_timeChange_of_reduced_solution
#print axioms u6_timeChange_past_domination
#print axioms u6_endpoint_absolutelyContinuous_of_later_past
#print axioms u6_endpoint_absolutelyContinuous_of_past
#print axioms u6_gmpPhysicalPathLaw_solves_martingale_problem
#print axioms u6_gmpPhysicalHeatKernel_measurable
end EinsteinFull
