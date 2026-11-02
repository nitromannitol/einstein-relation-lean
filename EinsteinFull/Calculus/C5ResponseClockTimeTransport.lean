import EinsteinFull.Calculus.C4ResponseClockCesaro
import EinsteinRelation.Probability.ProbabilityPart
import EinsteinFull.Calculus.S4PathwiseV2Support
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeTimeChange

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Disintegration uses the supplied probability fibres, including when the raw
kernel is not globally finite. -/
private theorem response_clock_joint_eq_compProd {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (Y : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw Y ω)) :
    Carriers.annealedCoordinateJoint Q Y op =
      Q.compProd (Probability.probabilityPart (originLaw Y)) := by
  have hae := Probability.probabilityPart_ae_eq Q (originLaw Y) op
  ext S hS
  have h := Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral
    Q (originLaw Y) op (S.indicator 1) (measurable_one.indicator hS)
  unfold Carriers.annealedCoordinateJoint
  rw [← lintegral_indicator_one hS, h, Measure.compProd_apply hS]
  refine lintegral_congr_ae (hae.mono fun ω hω => ?_)
  dsimp only
  rw [hω, ← lintegral_indicator_one (measurable_prodMk_left hS)]
  rfl

/-- Complex integrable observations disintegrate without changing the supplied
quenched laws on any environment of positive measure. -/
theorem response_clock_integral_disintegration {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (Y : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw Y ω))
    {F : FieldPair d × Path d → ℂ}
    (hF : Integrable F (Carriers.annealedCoordinateJoint Q Y op)) :
    (∫ z, F z ∂Carriers.annealedCoordinateJoint Q Y op) =
      ∫ ω, ∫ γ, F (ω, γ) ∂originLaw Y ω ∂Q := by
  rw [response_clock_joint_eq_compProd Q Y op] at hF ⊢
  rw [Measure.integral_compProd hF]
  refine integral_congr_ae
    ((Probability.probabilityPart_ae_eq Q (originLaw Y) op).mono fun ω hω => ?_)
  dsimp only
  rw [hω]

/-- Real-force realization identifies the actual semigroup mean with the
quenched expectations of its literal `Lp` representative. -/
theorem response_clock_semigroup_nested_identification
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (hreal : RealSemigroupAt hd Q) (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, (P t f) ω ∂reducedLaw Q) =
      ∫ ω, ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω) ∂Q.measure := by
  change (∫ ω, (P t f) ω ∂Q.measure.map reduce) = _
  rw [integral_map Probability.measurable_reduce.aemeasurable
      (Lp.stronglyMeasurable (P t f)).aestronglyMeasurable]
  exact integral_congr_ae
    ((response_clock_semigroup_path_identification d hd Λ r Q hreal lam P hP Y hY t f).mono
      fun _ h => h.2)

/-- The actual physical density is integrable at every time under the joint law
of any supplied reduced martingale-problem solution. -/
theorem response_physical_clock_density_integrable {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) :
    Integrable (fun z : FieldPair d × Path d =>
      (clockDensity z.1 (pathPosition t z.2) : ℂ))
      (Carriers.annealedCoordinateJoint Q.measure Y
        (response_clock_origin_probability Q i lam Y hY)) := by
  have : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q.measure Y
      (response_clock_origin_probability Q i lam Y hY)) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q.measure (originLaw Y) (response_clock_origin_probability Q i lam Y hY)
  have hb := Clock.ae_annealedCoordinateJoint_mem Q.measure Y
    (response_clock_origin_probability Q i lam Y hY)
    (Clock.isClosed_clockBoundSet (Real.exp (2 * Λ))).measurableSet
    (response_clock_path_bound Q Y)
  refine Integrable.of_bound
    ((Complex.continuous_ofReal.comp (Clock.continuous_clockDensity_at t)).aestronglyMeasurable)
    (Real.exp (2 * Λ)) ?_
  filter_upwards [hb] with z hz
  rw [Complex.norm_real, Real.norm_of_nonneg (clockDensity_pos _ _).le]
  exact hz t

/-- Environment/path disintegration followed by time integration gives the
literal expected physical clock. This step needs no spatial representative
substitution and works for every nonnegative terminal time. -/
theorem response_physical_clock_time_disintegration {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) :
    (∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, ∫ γ,
      (clockDensity ω (pathPosition t.toNNReal γ) : ℂ) ∂originLaw Y ω ∂Q.measure) =
      ∫ z, ((Clock.physicalPathClock z.1 z.2 T : ℝ) : ℂ)
        ∂Carriers.annealedCoordinateJoint Q.measure Y
          (response_clock_origin_probability Q i lam Y hY) := by
  have hb := Clock.ae_annealedCoordinateJoint_mem Q.measure Y
    (response_clock_origin_probability Q i lam Y hY)
    (Clock.isClosed_clockBoundSet (Real.exp (2 * Λ))).measurableSet
    (response_clock_path_bound Q Y)
  rw [integral_complex_ofReal,
    Clock.integral_physicalPathClock_eq Q.measure Y
      (response_clock_origin_probability Q i lam Y hY) (Real.exp (2 * Λ)) hb T,
    ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  rw [← integral_complex_ofReal]
  simp only [Clock.clockDensity_obs]
  exact (response_clock_integral_disintegration Q.measure Y
    (response_clock_origin_probability Q i lam Y hY)
    (response_physical_clock_density_integrable Q i lam Y hY t.toNNReal)).symm

/-- The same actual clock rate controls the nested physical path expectations.
The missing transport to an `Lp` observation is a separate occupation step. -/
theorem response_nested_physical_clock_cesaro_of_rate {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (η : ℝ) (hη : HasReducedClockRate Q Y η) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..T, ∫ ω, ∫ γ,
        (clockDensity ω (pathPosition t.toNNReal γ) : ℂ) ∂originLaw Y ω ∂Q.measure)
      atTop (𝓝 (η : ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (response_expected_clock_cesaro_of_rate Q i lam Y hY η hη)
  have hc : Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
      ∫ z, ((Clock.physicalPathClock z.1 z.2 T.toNNReal : ℝ) : ℂ)
        ∂Carriers.annealedCoordinateJoint Q.measure Y
          (response_clock_origin_probability Q i lam Y hY)) atTop (𝓝 (η : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_div, div_eq_mul_inv,
      mul_comm, integral_complex_ofReal, Complex.ofReal_mul, Complex.ofReal_inv] using h
  refine hc.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have heq := response_physical_clock_time_disintegration Q i lam Y hY T.toNNReal
  simp only [Real.coe_toNNReal T hT] at heq
  exact congrArg (fun z : ℂ => (T : ℂ)⁻¹ * z) heq.symm

/-- The complete clock primitive is integrable under the actual joint law.
Its deterministic linear bound is obtained from the same physical potential. -/
theorem response_physical_clock_primitive_integrable {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) :
    Integrable (fun z : FieldPair d × Path d =>
      ((Clock.physicalPathClock z.1 z.2 T : ℝ) : ℂ))
      (Carriers.annealedCoordinateJoint Q.measure Y
        (response_clock_origin_probability Q i lam Y hY)) := by
  have : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q.measure Y
      (response_clock_origin_probability Q i lam Y hY)) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q.measure (originLaw Y) (response_clock_origin_probability Q i lam Y hY)
  have hb := Clock.ae_annealedCoordinateJoint_mem Q.measure Y
    (response_clock_origin_probability Q i lam Y hY)
    (Clock.isClosed_clockBoundSet (Real.exp (2 * Λ))).measurableSet
    (response_clock_path_bound Q Y)
  refine Integrable.of_bound
    (Complex.continuous_ofReal.comp (Clock.continuous_physicalPathClock_at T)).aestronglyMeasurable
    (Real.exp (2 * Λ) * (T : ℝ)) ?_
  filter_upwards [hb] with z hz
  rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  exact Clock.physicalPathClock_le_of_clock_bound z.1 z.2 hz T

/-- Complete time/environment/path interchange for the actual physical density.
Every supplied reduced martingale law has this identity at every terminal time. -/
theorem response_physical_clock_time_swap {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) :
    (∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, ∫ γ,
      (clockDensity ω (pathPosition t.toNNReal γ) : ℂ) ∂originLaw Y ω ∂Q.measure) =
      ∫ ω, ∫ γ, (∫ t in (0 : ℝ)..(T : ℝ),
        (clockDensity ω (pathPosition t.toNNReal γ) : ℂ)) ∂originLaw Y ω ∂Q.measure := by
  rw [response_physical_clock_time_disintegration Q i lam Y hY T,
    response_clock_integral_disintegration Q.measure Y
      (response_clock_origin_probability Q i lam Y hY)
      (response_physical_clock_primitive_integrable Q i lam Y hY T)]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    apply integral_congr_ae
    exact ae_of_all _ fun γ => by
      dsimp only
      rw [intervalIntegral.integral_ofReal]
      rfl

/-- The actual nested quenched expectation of the clock has the same supplied
rate. The terminal time is truncated exactly as in the physical clock. -/
theorem response_nested_clock_expectation_cesaro_of_rate {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (η : ℝ) (hη : HasReducedClockRate Q Y η) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
      ∫ ω, ∫ γ, ((Clock.physicalPathClock ω γ T.toNNReal : ℝ) : ℂ)
        ∂originLaw Y ω ∂Q.measure) atTop (𝓝 (η : ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (response_expected_clock_cesaro_of_rate Q i lam Y hY η hη)
  have hc : Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
      ∫ z, ((Clock.physicalPathClock z.1 z.2 T.toNNReal : ℝ) : ℂ)
        ∂Carriers.annealedCoordinateJoint Q.measure Y
          (response_clock_origin_probability Q i lam Y hY)) atTop (𝓝 (η : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_div, div_eq_mul_inv,
      mul_comm, integral_complex_ofReal, Complex.ofReal_mul, Complex.ofReal_inv] using h
  convert hc using 1
  funext T
  rw [response_clock_integral_disintegration Q.measure Y
    (response_clock_origin_probability Q i lam Y hY)
    (response_physical_clock_primitive_integrable Q i lam Y hY T.toNNReal)]

/-- The inverse-clock kernel preserves every probability fibre of an arbitrary
supplied kernel; its other fibres need no finiteness hypothesis. -/
private theorem response_exists_inverse_clock_kernel {d : ℕ} (L : ℝ)
    (Y : QuenchedPathLaws d) :
    ∃ X : QuenchedPathLaws d, ∀ (ω : FieldPair d) (hω : IsRegular L ω),
      IsProbabilityMeasure (Y (0, ω)) →
        X (0, ω) = (Y (0, ω)).map (EinsteinFull.timeChangeMap hω) := by
  refine ⟨ProbabilityTheory.Kernel.map
    (ProbabilityTheory.Kernel.id ×ₖ Probability.probabilityPart Y)
    (EinsteinFull.timeChangeFamily L), fun ω hω hprob => ?_⟩
  letI := hprob
  rw [ProbabilityTheory.Kernel.map_apply _ (EinsteinFull.measurable_timeChangeFamily d L),
    ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.id_apply,
    Measure.dirac_prod, Probability.probabilityPart_eq_of_isProbabilityMeasure Y (0, ω),
    Measure.map_map (EinsteinFull.measurable_timeChangeFamily d L) measurable_prodMk_left]
  congr 1
  funext γ
  exact dite_eq_left hω

/-- Inverse clocks construct the physical family from the actual almost-sure
reduced solutions at every signed force. -/
theorem response_inverse_family_of_reduced_family {d : ℕ}
    (D : EinsteinFull.StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) (i : Fin d)
    (Y : DiffusionFamily d)
    (hY : ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y lam (0, ω))) :
    ∃ X : DiffusionFamily d, EinsteinFull.IsSignedPhysicalFamily i Q X ∧
      ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular D.ellipticity ω,
        X lam (0, ω) = (Y lam (0, ω)).map
          (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ D.ellipticity hω) := by
  have hΛ : 0 < D.ellipticity := zero_lt_one.trans_le D.one_le_ellipticity
  choose X hX using fun lam : ℝ => response_exists_inverse_clock_kernel D.ellipticity (Y lam)
  refine ⟨X, fun lam => ?_, fun lam => ?_⟩
  · filter_upwards [Q.regular, hsm, hY lam] with ω hreg hs hsol
    rw [hX lam ω hreg hsol.1]
    exact EinsteinFull.timeChange_solves hΛ hreg hs i lam 0 hsol
  · filter_upwards [Q.regular, hY lam] with ω hreg hsol
    exact ⟨hreg, hX lam ω hreg hsol.1⟩

/-- A supplied law can replace its force in a genuine reduced family before
applying the time-change dependency. Both witnesses refer to that supplied law. -/
theorem response_velocity_clock_witnesses_of_reduced_family
    (htc : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : EinsteinFull.StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : EinsteinFull.HasSmoothBounds D Q)
    (Y₀ : DiffusionFamily d)
    (hY₀ : ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y₀ lam (0, ω)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) :
    ∃ (velocity : Vec d) (η : ℝ),
      HasQuenchedVelocity Q.measure (originLaw Y) velocity ∧ HasReducedClockRate Q Y η := by
  classical
  let PY : DiffusionFamily d := fun l => if l = lam then Y else Y₀ l
  have hPY : ∀ l : ℝ, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω l)
        0 (PY l (0, ω)) := by
    intro l
    by_cases he : l = lam
    · subst l
      simpa only [PY, ite_true] using hY
    · simpa only [PY, ite_eq_right he] using hY₀ l
  obtain ⟨PX, hPX, hrel⟩ := response_inverse_family_of_reduced_family D Q
    (hQ.mono fun _ h => h.1) (⟨0, by omega⟩ : Fin d) PY hPY
  obtain ⟨Λ, -, hall⟩ := htc D.ellipticity D.one_le_ellipticity
  obtain ⟨hvel, -, -⟩ := hall d hd D.dependenceRange D.derivativeBound Q
    D.one_le_dependenceRange D.derivativeBound_pos hQ PX PY hPX hPY hrel
  obtain ⟨η, vX, vY, -, -, hη, -, hvY, -⟩ := hvel lam hlam
  exact ⟨vY, η, by simpa only [PY, ite_true] using hvY,
    by simpa only [PY, ite_true] using hη⟩

end EinsteinFull.Blueprint
