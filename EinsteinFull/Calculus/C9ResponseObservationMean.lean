import EinsteinFull.Blueprint.G4.node_p_u3A_response_u23_cesaro_u2D_abel
import EinsteinFull.Calculus.C4RealSemigroupAt
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Calculus.ComplexHorizontalMeanSupport
import EinsteinFull.Frozen.ReducedLawStationary
import Mathlib.MeasureTheory.Measure.OpenPos
open MeasureTheory Filter
open scoped Topology NNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation
/- SUPERVISOR EXACT CONTRACT (not a declaration/proof):
theorem response_observation_mean_bounded_continuous
    (hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (f : Lp ℂ 2 (reducedLaw Q)) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ K) :
    Continuous (fun t : ℝ => ∫ ω, (P t.toNNReal f) ω ∂reducedLaw Q) ∧
      ∀ t : ℝ, 0 ≤ t → ‖∫ ω, (P t.toNNReal f) ω ∂reducedLaw Q‖ ≤ K
-/

/-- The actual semigroup observation mean is continuous, including at zero
and at negative real parameters after the prescribed `toNNReal` extension. -/
theorem response_observation_mean_continuous
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t : ℝ => ∫ ω, (P t.toNNReal f) ω ∂reducedLaw Q) := by
  letI := reducedLaw_probability Q
  exact (continuous_complexL2_integral (reducedLaw Q)).comp
    ((hP.2.2.1 f).comp continuous_real_toNNReal)

/-- Stationarity transports an essential observation bound to almost every
spatial point on almost every original environment orbit. -/
theorem response_observation_spatial_bound
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (f : Lp ℂ 2 (reducedLaw Q)) {K : ℝ}
    (hf : ∀ᵐ η ∂reducedLaw Q, ‖f η‖ ≤ K) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ x ∂(volume : Measure (Vec d)),
      ‖f (translate x (reduce ω))‖ ≤ K := by
  letI := reducedLaw_probability Q
  have hspatial : ∀ᵐ η ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      ‖f (translate x η)‖ ≤ K := by
    apply (Measure.ae_ae_comm ?_).mp
      (ae_of_all _ fun x =>
        (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hf)
    exact measurableSet_le
      (((Lp.stronglyMeasurable f).measurable.comp
        Probability.continuous_translate.measurable).norm)
      measurable_const
  exact ae_of_ae_map Probability.measurable_reduce.aemeasurable hspatial

/-- Positive-time endpoint absolute continuity transports the spatial bound to
the literal observation representative at that path time. -/
theorem response_observation_path_bound_of_endpoint_ac
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (Y : QuenchedPathLaws d) (t : ℝ≥0)
    (hac : ∀ᵐ ω ∂Q.measure,
      (Y (0, ω)).map (pathPosition t) ≪ (volume : Measure (Vec d)))
    (f : Lp ℂ 2 (reducedLaw Q)) {K : ℝ}
    (hf : ∀ᵐ η ∂reducedLaw Q, ‖f η‖ ≤ K) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      ‖f (translate (γ t) (reduce ω))‖ ≤ K := by
  filter_upwards [response_observation_spatial_bound Q f hf, hac] with ω hω hacω
  exact ae_of_ae_map (measurable_pathPosition t).aemeasurable (hacω.ae_le hω)

/-- The exact uniform constant follows from the actual path identification
once the supplied martingale-problem family has endpoint absolute continuity.
The endpoint property is an internal prerequisite, not an added root premise. -/
theorem response_observation_mean_bound_of_endpoint_ac
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hreal : RealSemigroupAt hd Q) (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (t : ℝ≥0)
    (hac : ∀ᵐ ω ∂Q.measure,
      (Y (0, ω)).map (pathPosition t) ≪ (volume : Measure (Vec d)))
    (f : Lp ℂ 2 (reducedLaw Q)) (K : ℝ)
    (hf : ∀ᵐ η ∂reducedLaw Q, ‖f η‖ ≤ K) :
    ‖∫ η, (P t f) η ∂reducedLaw Q‖ ≤ K := by
  letI := reducedLaw_probability Q
  have hid := (hreal lam).2.2.2.2 Y hY t f
  have hbound : ∀ᵐ ω ∂Q.measure, ‖(P t f) (reduce ω)‖ ≤ K := by
    filter_upwards [hid, hY, response_observation_path_bound_of_endpoint_ac Q Y t hac f hf]
      with ω he hmp hb
    letI := hmp.1
    rw [hP.eq_forcedComplexEvolution, he.2]
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const hb
  have hred : ∀ᵐ η ∂reducedLaw Q, ‖(P t f) η‖ ≤ K :=
    (ae_map_iff Probability.measurable_reduce.aemeasurable
      (measurableSet_le (Lp.stronglyMeasurable (P t f)).measurable.norm
        measurable_const)).mpr hbound
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const hred

/-- Continuity upgrades an almost-everywhere positive-time bound on the
actual mean to every nonnegative time, including time zero. -/
theorem response_observation_mean_bound_of_ae_time
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (K : ℝ)
    (hae : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioi 0),
      ‖∫ ω, (P t.toNNReal f) ω ∂reducedLaw Q‖ ≤ K) :
    ∀ t : ℝ, 0 ≤ t → ‖∫ ω, (P t.toNNReal f) ω ∂reducedLaw Q‖ ≤ K := by
  let g : ℝ → ℝ := fun t => ‖∫ ω, (P t.toNNReal f) ω ∂reducedLaw Q‖
  have hg : Continuous g := (response_observation_mean_continuous hP f).norm
  have hpos : Set.Ioi (0 : ℝ) ⊆ {t | g t ≤ K} := by
    intro t ht
    have hinterval : (fun s => max (g s) K) =ᵐ[volume.restrict (Set.Ioc 0 t)]
        (fun _ => K) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (show Set.Ioc 0 t ⊆ Set.Ioi 0 from fun _ hs => hs.1) hae] with s hs
      exact max_eq_right hs
    have heq := Measure.eqOn_Ioc_of_ae_eq volume hinterval
      (hg.max continuous_const).continuousOn continuous_const.continuousOn
    exact (max_eq_right_iff).mp (heq ⟨ht, le_rfl⟩)
  have hclosed : IsClosed {t | g t ≤ K} := isClosed_le hg continuous_const
  have hnonneg := hclosed.closure_subset_iff.mpr hpos
  rw [closure_Ioi] at hnonneg
  exact fun t ht => hnonneg ht

end EinsteinFull.Blueprint
