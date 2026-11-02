import EinsteinFull.Calculus.C5ResponseClockTimeTransport
import EinsteinFull.Calculus.C5ResponseClockBounds
import EinsteinFull.Calculus.C5ResponseObservationMeanBound
import EinsteinFull.Calculus.C9ComplexCesaroAbel

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Spatial occupation transports the literal clock representative along the
supplied paths. The occupation estimate remains an explicit internal input. -/
theorem response_clock_path_observation_of_occupation
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ)
    (Y : QuenchedPathLaws d)
    (hocc : ∀ᵐ ω ∂Q.measure, ∀ N : Set (Vec d), MeasurableSet N →
      (volume : Measure (Vec d)) N = 0 →
      ∀ᵐ γ ∂Y (0, ω), ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        γ t.toNNReal ∉ N) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        μ (translate (γ t.toNNReal) (reduce ω)) =
          (clockDensity ω (γ t.toNNReal) : ℂ) := by
  filter_upwards [response_clock_spatial_representative Q μ hμ, hocc] with ω hω ho
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hω)
  filter_upwards [ho N hN hnull] with γ hγ
  filter_upwards [hγ] with t ht
  by_contra hnot
  exact ht (hsub hnot)

private theorem response_clock_time_equality_measurable {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (μ : Lp ℂ 2 (reducedLaw Q)) :
    MeasurableSet {zt : (FieldPair d × Path d) × ℝ |
      μ (translate (zt.1.2 zt.2.toNNReal) (reduce zt.1.1)) =
        (clockDensity zt.1.1 (zt.1.2 zt.2.toNNReal) : ℂ)} := by
  have heval : Continuous (fun zt : (FieldPair d × Path d) × ℝ =>
      zt.1.2 zt.2.toNNReal) :=
    continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
      (continuous_real_toNNReal.comp continuous_snd))
  have henv : Continuous (fun zt : (FieldPair d × Path d) × ℝ =>
      translate (zt.1.2 zt.2.toNNReal) (reduce zt.1.1)) :=
    Probability.continuous_translate.comp (heval.prodMk
      (Probability.continuous_reduce.comp (continuous_fst.comp continuous_fst)))
  apply measurableSet_eq_fun ((Lp.stronglyMeasurable μ).measurable.comp henv.measurable)
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul (continuous_eval.comp
      ((continuous_snd.comp (continuous_fst.comp continuous_fst)).prodMk heval))))).measurable

/-- After occupation transport and Fubini, the semigroup clock mean equals
the actual physical density mean for almost every positive time. -/
theorem response_clock_mean_of_occupation
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (hreal : RealSemigroupAt hd Q)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ) (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (hocc : ∀ᵐ ω ∂Q.measure, ∀ N : Set (Vec d), MeasurableSet N →
      (volume : Measure (Vec d)) N = 0 →
      ∀ᵐ γ ∂Y (0, ω), ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        γ t.toNNReal ∉ N) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ ω, (P t.toNNReal μ) ω ∂reducedLaw Q) =
        ∫ ω, ∫ γ, (clockDensity ω (γ t.toNNReal) : ℂ) ∂Y (0, ω) ∂Q.measure := by
  let op := response_clock_origin_probability Q (⟨0, by omega⟩ : Fin d) lam Y hY
  let : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q.measure Y op) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q.measure (originLaw Y) op
  have heq := response_clock_time_equality_measurable Q μ
  have hevent : MeasurableSet {z : FieldPair d × Path d |
      ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        μ (translate (z.2 t.toNNReal) (reduce z.1)) =
          (clockDensity z.1 (z.2 t.toNNReal) : ℂ)} := by
    simp only [ae_iff]
    exact measurableSet_eq_fun (measurable_measure_prodMk_left heq.compl) measurable_const
  have hj := Clock.ae_annealedCoordinateJoint_mem Q.measure Y op hevent
    (response_clock_path_observation_of_occupation Q μ hμ Y hocc)
  have ht := (Measure.ae_ae_comm heq).mp hj
  filter_upwards [ht] with t ht
  have hint := response_physical_clock_density_integrable Q
    (⟨0, by omega⟩ : Fin d) lam Y hY t.toNNReal
  rw [response_clock_semigroup_nested_identification d hd Λ r Q hreal lam P hP Y hY]
  change (∫ ω, ∫ γ, μ (translate (γ t.toNNReal) (reduce ω))
    ∂originLaw Y ω ∂Q.measure) = _
  rw [← response_clock_integral_disintegration Q.measure Y op
      (hint.congr (ht.mono fun _ hz => hz.symm)),
    integral_congr_ae ht]
  exact response_clock_integral_disintegration Q.measure Y op hint

/-- The literal clock observation has the Cesàro and Abel limits of the same
actual clock rate, once the internal spatial occupation estimate is supplied. -/
theorem response_clock_limits_of_rate_and_occupation
    (hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2)
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
    (hocc : ∀ᵐ ω ∂Q.measure, ∀ N : Set (Vec d), MeasurableSet N →
      (volume : Measure (Vec d)) N = 0 →
      ∀ᵐ γ ∂Y (0, ω), ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        γ t.toNNReal ∉ N)
    (η : ℝ) (hη : HasReducedClockRate Q Y η) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..T, ∫ ω, (P t.toNNReal μ) ω ∂reducedLaw Q)
        atTop (𝓝 (η : ℂ)) ∧
    Tendsto (fun s : ℝ => (s : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
      (Real.exp (-s * t) : ℂ) * (∫ ω, (P t.toNNReal μ) ω ∂reducedLaw Q))
        (𝓝[>] (0 : ℝ)) (𝓝 (η : ℂ)) := by
  have hmean := response_clock_mean_of_occupation d hd D.ellipticity
    D.dependenceRange Q (realSemigroupAt_of_stmtV2 hreal hd D Q hQ) μ hμ lam P hP Y hY hocc
  have hcesaro : Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..T, ∫ ω, (P t.toNNReal μ) ω ∂reducedLaw Q)
        atTop (𝓝 (η : ℂ)) := by
    refine (response_nested_physical_clock_cesaro_of_rate Q
      (⟨0, by omega⟩ : Fin d) lam Y hY η hη).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [Set.uIoc_of_le hT]
    exact ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1)
      (hmean.mono fun _ he => he.symm)
  have hbound : ∀ᵐ ω ∂reducedLaw Q, ‖μ ω‖ ≤ Real.exp (2 * D.ellipticity) := by
    apply (ae_map_iff Probability.measurable_reduce.aemeasurable
      (measurableSet_le (Lp.stronglyMeasurable μ).measurable.norm measurable_const)).mpr
    filter_upwards [Q.regular,
      ae_of_ae_map Probability.measurable_reduce.aemeasurable hμ] with ω hreg heq
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    change |clockDensity ω 0| ≤ Real.exp (2 * D.ellipticity)
    rw [abs_of_pos (clockDensity_pos ω 0)]
    exact (clockDensity_bounds ω 0 D.ellipticity (hreg.2.1 0)).2
  obtain ⟨hcont, hbounded⟩ := response_observation_mean_bounded_continuous
    hreal d hd D Q hQ lam P hP Y hY μ (Real.exp (2 * D.ellipticity))
    (Real.exp_pos _).le hbound
  exact ⟨hcesaro, complex_abel_limit_of_cesaro _ hcont _
    (Real.exp_pos _).le hbounded _ hcesaro⟩

/-- Conditional assembly of the clock half, preserving velocity-before-clock
witness order and using one supplied law and one rate for all conclusions.
The two remaining internal inputs are family existence and null occupation. -/
theorem response_clock_witness_of_family_and_occupation
    (htc : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (μ : Lp ℂ 2 (reducedLaw Q))
    (hμ : IsReducedClockObservation Q μ)
    (Y₀ : DiffusionFamily d)
    (hY₀ : ∀ l : ℝ, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω l)
        0 (Y₀ l (0, ω)))
    (lam : ℝ) (hlam : lam ≠ 0)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (hocc : ∀ᵐ ω ∂Q.measure, ∀ N : Set (Vec d), MeasurableSet N →
      (volume : Measure (Vec d)) N = 0 →
      ∀ᵐ γ ∂Y (0, ω), ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        γ t.toNNReal ∉ N) :
    ∃ (velocity : Vec d) (η : ℝ),
      HasQuenchedVelocity Q.measure (originLaw Y) velocity ∧
      HasReducedClockRate Q Y η ∧
      Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
        ∫ t in (0 : ℝ)..T, ∫ ω, (P t.toNNReal μ) ω ∂reducedLaw Q)
          atTop (𝓝 (η : ℂ)) ∧
      Tendsto (fun s : ℝ => (s : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-s * t) : ℂ) * (∫ ω, (P t.toNNReal μ) ω ∂reducedLaw Q))
          (𝓝[>] (0 : ℝ)) (𝓝 (η : ℂ)) ∧
      ∀ lower upper : ℝ,
        (∀ᵐ ω ∂reducedLaw Q, ∀ x : Vec d,
          lower ≤ ω.2 x ∧ ω.2 x ≤ upper) →
        (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω, ∀ t : ℝ≥0,
          lower * (t : ℝ) ≤ (Clock.physicalPathClock ω γ t : ℝ) ∧
          (Clock.physicalPathClock ω γ t : ℝ) ≤ upper * (t : ℝ)) ∧
        lower ≤ η ∧ η ≤ upper := by
  obtain ⟨velocity, η, hvelocity, hη⟩ :=
    response_velocity_clock_witnesses_of_reduced_family htc hd D Q hQ Y₀ hY₀ lam hlam Y hY
  obtain ⟨hcesaro, habel⟩ := response_clock_limits_of_rate_and_occupation
    hreal d hd D Q hQ μ hμ lam P hP Y hY hocc η hη
  exact ⟨velocity, η, hvelocity, hη, hcesaro, habel,
    response_clock_bounds_of_rate d hd D.ellipticity D.dependenceRange Q Y lam hY η hη⟩

end EinsteinFull.Blueprint
