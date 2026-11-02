import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Calculus.C9ResponseThresholdEnergy
import EinsteinFull.Calculus.C6ResponseThresholdExcessDerivative
import EinsteinFull.Calculus.ComplexForceApproximationSupport

open MeasureTheory Filter Set
open scoped NNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/- SUPERVISOR EXACT CONTRACT (not a declaration/proof):
theorem response_real_force_semigroup_bound
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (f : Lp ℂ 2 (reducedLaw Q)) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ K) :
    ∀ t : ℝ≥0, ∀ᵐ ω ∂reducedLaw Q, ‖(P t f) ω‖ ≤ K
-/

private def thresholdExcess {d : ℕ} (μ : Measure (FieldPair d)) (K : ℝ)
    (f : Lp ℂ 2 μ) : ℝ := ∫ ω, (max (‖f ω‖ - K) 0) ^ 2 ∂μ

private theorem threshold_excess_continuous {d : ℕ} (μ : Measure (FieldPair d))
    (K : ℝ) (hK : 0 ≤ K) : Continuous (thresholdExcess μ K) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  obtain ⟨v, _, hv⟩ := response_threshold_excess_energy_hasFDerivAt μ K hK f
  exact hv.continuousAt

private theorem threshold_excess_integrable {d : ℕ} (μ : Measure (FieldPair d))
    (K : ℝ) (hK : 0 ≤ K) (f : Lp ℂ 2 μ) :
    Integrable (fun ω => (max (‖f ω‖ - K) 0)^2) μ := by
  have hm : AEStronglyMeasurable (fun ω => max (‖f ω‖ - K) 0) μ :=
    ((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f).norm
  apply (Lp.memLp f).norm.integrable_sq.mono' (hm.pow 2)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (le_max_right _ _)
    exact max_le (by linarith) (norm_nonneg _)

private theorem threshold_excess_eq_zero_iff {d : ℕ} (μ : Measure (FieldPair d))
    (K : ℝ) (hK : 0 ≤ K) (f : Lp ℂ 2 μ) :
    thresholdExcess μ K f = 0 ↔ ∀ᵐ ω ∂μ, ‖f ω‖ ≤ K := by
  rw [thresholdExcess, integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
    (threshold_excess_integrable μ K hK f)]
  constructor
  · intro h
    filter_upwards [h] with ω hω
    have hz : max (‖f ω‖ - K) 0 = 0 := sq_eq_zero_iff.mp hω
    have := le_max_left (‖f ω‖ - K) 0
    linarith only [this, hz]
  · intro h
    filter_upwards [h] with ω hω
    simp only [max_eq_right (sub_nonpos.mpr hω), zero_pow (by decide : 2 ≠ 0), Pi.zero_apply]

/-- Domain orbits satisfy a scalar exponential estimate for their actual threshold excess. -/
theorem response_threshold_excess_orbit_bound (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q) (lam : ℝ)
        (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P →
        ∀ (f g : Lp ℂ 2 (reducedLaw Q)),
          IsComplexGeneratorPair Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) f g →
          ∀ K : ℝ, 0 ≤ K → ∀ t : ℝ≥0,
            (∫ ω, (max (‖(P t f) ω‖ - K) 0)^2 ∂reducedLaw Q) ≤
              (∫ ω, (max (‖f ω‖ - K) 0)^2 ∂reducedLaw Q) *
                Real.exp ((2 * C * |lam|) * (t : ℝ)) := by
  obtain ⟨C, hC, henergy⟩ := response_real_force_threshold_energy d hd D
  refine ⟨C, hC, ?_⟩
  intro Q hQ lam P hP f g hfg K hK t
  let E := thresholdExcess (reducedLaw Q) K
  have hE : Continuous E := threshold_excess_continuous _ K hK
  choose v hv hdiff using fun s : ℝ =>
    response_threshold_excess_energy_hasFDerivAt (reducedLaw Q) K hK
      (P s.toNNReal f)
  have hdif (s : ℝ) (hs : 0 ≤ s) :
      HasDerivWithinAt (fun r : ℝ => E (P r.toNNReal f))
        (2 * inner ℝ (v s) (P s.toNNReal g)) (Ici s) s := by
    simpa only [E, thresholdExcess, Function.comp_def, smul_apply,
      innerSL_apply_apply, smul_eq_mul] using
        (hdiff s).comp_hasDerivWithinAt s (hP.hasDerivWithinAt_orbit hfg s hs)
  have hinner (s : ℝ) : inner ℝ (v s) (P s.toNNReal g) =
      ∫ ω, (star (((max (‖(P s.toNNReal f) ω‖ - K) 0 /
        ‖(P s.toNNReal f) ω‖ : ℝ) : ℂ) * (P s.toNNReal f) ω) *
        (P s.toNNReal g) ω).re ∂reducedLaw Q := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv s] with ω hω
    rw [Complex.inner, hω, mul_comm]
    rfl
  have hb := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun s : ℝ => E (P s.toNNReal f))
    (f' := fun s : ℝ => 2 * inner ℝ (v s) (P s.toNNReal g))
    (δ := E f) (K := 2 * C * |lam|) (ε := 0)
    (a := 0) (b := (t : ℝ))
    (hE.comp ((hP.2.2.1 f).comp continuous_real_toNNReal)).continuousOn
    (fun s hs _ hr => (hdif s hs.1).liminf_right_slope_le hr)
    (by simp only [Real.toNNReal_zero, hP.1, ContinuousLinearMap.id_apply, le_refl])
    (fun s _ => by
      rw [hinner, add_zero]
      have h := henergy Q hQ lam _ _ (hP.map_generator hfg s.toNNReal) K hK
      change 2 * _ ≤ 2 * C * |lam| * E (P s.toNNReal f)
      dsimp only [E, thresholdExcess]
      linarith only [h])
    (t : ℝ) ⟨t.property, le_rfl⟩
  simpa only [E, thresholdExcess, Real.toNNReal_coe, sub_zero, gronwallBound_ε0] using hb

/-- Every real-force semigroup preserves each nonnegative essential norm bound. -/
theorem response_real_force_semigroup_bound
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (f : Lp ℂ 2 (reducedLaw Q)) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ K) :
    ∀ t : ℝ≥0, ∀ᵐ ω ∂reducedLaw Q, ‖(P t f) ω‖ ≤ K := by
  obtain ⟨C, _, hbound⟩ := response_threshold_excess_orbit_bound d hd D
  let E := thresholdExcess (reducedLaw Q) K
  have hE : Continuous E := threshold_excess_continuous _ K hK
  have hfzero : E f = 0 := (threshold_excess_eq_zero_iff _ K hK f).mpr hf
  let fn := fun n : ℕ => forcedComplexResolventApproximation Q ⟨0, by omega⟩ (lam : ℂ) n f
  have hfn : Tendsto fn atTop (𝓝 f) := tendsto_forcedComplexResolventApproximation _ _ _ _
  intro t
  have hn (n : ℕ) : E (P t (fn n)) ≤ E (fn n) * Real.exp ((2 * C * |lam|) * (t : ℝ)) :=
    hbound Q hQ lam P hP _ _ (forcedComplexYosida_graph Q _ _ n f) K hK t
  have hz : E (P t f) ≤ 0 := by
    have h := le_of_tendsto_of_tendsto
      (hE.tendsto _ |>.comp ((P t).continuous.tendsto _ |>.comp hfn))
      ((hE.tendsto _ |>.comp hfn).mul_const (Real.exp ((2 * C * |lam|) * (t : ℝ))))
      (Eventually.of_forall hn)
    simpa only [hfzero, zero_mul] using h
  have hnonneg : 0 ≤ E (P t f) := integral_nonneg fun _ => sq_nonneg _
  exact (threshold_excess_eq_zero_iff _ K hK (P t f)).mp (le_antisymm hz hnonneg)

end EinsteinFull.Blueprint
