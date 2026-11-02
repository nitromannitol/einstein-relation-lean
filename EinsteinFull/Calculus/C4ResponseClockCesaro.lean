import EinsteinFull.Blueprint.G4.node_p_u3A_response_u23_cesaro_u2D_abel
import EinsteinFull.Calculus.C4RealSemigroupAt
import EinsteinRelation.Clock.ClockExpectation
open MeasureTheory Filter
open scoped Topology NNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
/- SUPERVISOR EXACT CONTRACT (not a declaration/proof):
theorem response_clock_cesaro_of_rate
    (hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (μ : Lp ℂ 2 (reducedLaw Q))
    (hμ : IsReducedClockObservation Q μ) (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (η : ℝ) (hη : HasReducedClockRate Q Y η) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..T, ∫ ω, (P t.toNNReal μ) ω ∂reducedLaw Q)
      atTop (𝓝 (η : ℂ))
-/

/-- Every actual origin solution is a probability law, with the quantifier needed
by the annealed clock construction. -/
theorem response_clock_origin_probability {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω))) :
    ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) :=
  hY.mono fun _ h => h.1

/-- The actual potential bound controls the clock along every path. -/
theorem response_clock_path_bound {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (Y : QuenchedPathLaws d) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω, ∀ s : ℝ≥0,
      clockDensity ω (pathPosition s γ) ≤ Real.exp (2 * Λ) := by
  filter_upwards [Q.regular] with ω hω
  exact ae_of_all _ fun γ s => (clockDensity_bounds ω _ Λ (hω.2.1 _)).2

/-- The produced almost-sure rate gives the Cesàro limit of the actual expected
clock, with no semigroup representative substitution. -/
theorem response_expected_clock_cesaro_of_rate {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (η : ℝ) (hη : HasReducedClockRate Q Y η) :
    Tendsto (fun T : ℝ =>
      (∫ z, (Clock.physicalPathClock z.1 z.2 T.toNNReal : ℝ)
        ∂Carriers.annealedCoordinateJoint Q.measure Y
          (response_clock_origin_probability Q i lam Y hY)) / T)
      atTop (𝓝 η) := by
  exact Clock.tendsto_integral_physicalPathClock_div_of_fiber Q.measure Y
    (response_clock_origin_probability Q i lam Y hY) (Real.exp (2 * Λ)) η
    (response_clock_path_bound Q Y) hη

/-- The actual path-observation primitive has the same Cesàro limit. -/
theorem response_path_clock_primitive_cesaro_of_rate {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (η : ℝ) (hη : HasReducedClockRate Q Y η) :
    Tendsto (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T, ∫ z, (Carriers.reducedObservationAt t.toNNReal z).2 0
        ∂Carriers.annealedCoordinateJoint Q.measure Y
          (response_clock_origin_probability Q i lam Y hY)) / T)
      atTop (𝓝 η) := by
  have hb : ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q.measure Y
      (response_clock_origin_probability Q i lam Y hY),
      ∀ s : ℝ≥0, clockDensity z.1 (pathPosition s z.2) ≤ Real.exp (2 * Λ) :=
    Clock.ae_annealedCoordinateJoint_mem Q.measure Y
      (response_clock_origin_probability Q i lam Y hY)
      (Clock.isClosed_clockBoundSet (Real.exp (2 * Λ))).measurableSet
      (response_clock_path_bound Q Y)
  refine (response_expected_clock_cesaro_of_rate Q i lam Y hY η hη).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [Clock.integral_physicalPathClock_eq Q.measure Y
    (response_clock_origin_probability Q i lam Y hY) (Real.exp (2 * Λ)) hb,
    Real.toNNReal_of_nonneg hT]
  rfl

/-- Real-force realization applies to the supplied family, by full-generator
uniqueness. This retains the literal `Lp` representative in the path integral. -/
theorem response_clock_semigroup_path_identification
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (hreal : RealSemigroupAt hd Q) (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
      P t f (reduce ω) =
        ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω) := by
  obtain ⟨hc, _, _, _, hpath⟩ := hreal lam
  rw [hP.unique hc]
  exact hpath Y hY t f

/-- The actual path primitive also has the required complex normalization. -/
theorem response_complex_path_clock_cesaro_of_rate {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (η : ℝ) (hη : HasReducedClockRate Q Y η) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..T, ∫ z, ((Carriers.reducedObservationAt t.toNNReal z).2 0 : ℂ)
        ∂Carriers.annealedCoordinateJoint Q.measure Y
          (response_clock_origin_probability Q i lam Y hY))
      atTop (𝓝 (η : ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (response_path_clock_primitive_cesaro_of_rate Q i lam Y hY η hη)
  simpa only [Function.comp_def, Complex.ofReal_div, div_eq_mul_inv,
    mul_comm, integral_complex_ofReal, intervalIntegral.integral_ofReal,
    Complex.ofReal_mul, Complex.ofReal_inv] using h

/-- The reduced-law observation identity is valid on almost every spatial
orbit. The spatial quantifier remains almost everywhere. -/
theorem response_clock_spatial_representative {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (μ : Lp ℂ 2 (reducedLaw Q))
    (hμ : IsReducedClockObservation Q μ) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ x ∂(volume : Measure (Vec d)),
      μ (translate x (reduce ω)) = (clockDensity ω x : ℂ) := by
  let a : FieldPair d → ℂ := fun ω => μ (reduce ω)
  let b : FieldPair d → ℂ := fun ω => (clockDensity ω 0 : ℂ)
  have ha : Measurable a :=
    (Lp.stronglyMeasurable μ).measurable.comp Probability.measurable_reduce
  have hb : Measurable b := by
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_eval_const 0).comp continuous_snd)))).measurable
  have hab : a =ᵐ[Q.measure] b :=
    ae_of_ae_map Probability.measurable_reduce.aemeasurable hμ
  have horbit : ∀ᵐ ω ∂Q.measure, ∀ᵐ x ∂(volume : Measure (Vec d)),
      a (translate x ω) = b (translate x ω) := by
    apply (Measure.ae_ae_comm ?_).mp
      (ae_of_all _ fun x =>
        (measurePreserving_translate Q.measure Q.stationary x).quasiMeasurePreserving.ae hab)
    exact measurableSet_eq_fun
      (ha.comp Probability.continuous_translate.measurable)
      (hb.comp Probability.continuous_translate.measurable)
  filter_upwards [horbit] with ω hω
  filter_upwards [hω] with x hx
  simpa only [a, b, reduce_translate, clockDensity, translate_scalar, add_zero] using hx

end EinsteinFull.Blueprint
