import EinsteinFull.Calculus.ComplexForcedSmoothingSupport
import EinsteinFull.Calculus.ComplexSemigroupCenteringSupport

/-!
# The actual bounded forced horizontal gradient operator

Positive-time smoothing and uniqueness bundle the actual gradient as a bounded
complex linear map with the structural square-root time and quadratic-force
exponential bound. The semigroup law transports it without differentiating
any random representative.
-/

open MeasureTheory Filter
open scoped NNReal Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

private def gradientValue (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℂ 2 (reducedLaw Q)) :
    PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
  (hP.exists_gradient_forced f t ht).choose

private theorem gradientValue_spec (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t f) (gradientValue hP t ht f) :=
  (hP.exists_gradient_forced f t ht).choose_spec.1

private theorem gradientValue_bound (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖gradientValue hP t ht f‖ ≤ ((2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) / Real.sqrt (t : ℝ)) *
      Real.exp (65 * complexForceShift d Λ₀ ζ * (t : ℝ))) * ‖f‖ :=
  (hP.exists_gradient_forced f t ht).choose_spec.2

/-- The actual horizontal gradient of any complete forced family, as a bounded operator. -/
def IsComplexEnvironmentSemigroup.forcedGradient
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) (ht : 0 < t) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
  let L : Lp ℂ 2 (reducedLaw Q) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
    { toFun := gradientValue hP t ht
      map_add' := fun f g => by
        apply WithLp.ofLp_injective 2
        apply (gradientValue_spec hP t ht (f+g)).unique
        intro j
        simpa only [map_add, PiLp.add_apply] using
          (gradientValue_spec hP t ht f j).add (gradientValue_spec hP t ht g j)
      map_smul' := fun c f => by
        change gradientValue hP t ht (c • f) = c • gradientValue hP t ht f
        apply WithLp.ofLp_injective 2
        apply (gradientValue_spec hP t ht (c • f)).unique
        intro j
        simpa only [map_smul, PiLp.smul_apply] using (gradientValue_spec hP t ht f j).smul c }
  L.mkContinuous ((2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) / Real.sqrt (t : ℝ)) *
      Real.exp (65 * complexForceShift d Λ₀ ζ * (t : ℝ)))
    (gradientValue_bound hP t ht)

/-- The bounded operator is the actual full strong horizontal gradient of the evolved datum. -/
theorem IsComplexEnvironmentSemigroup.forcedGradient_spec
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t f) (hP.forcedGradient t ht f) :=
  gradientValue_spec hP t ht f

/-- The actual forced gradient operator has the structural t^(-1/2) exponential norm bound. -/
theorem IsComplexEnvironmentSemigroup.norm_forcedGradient_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) (ht : 0 < t) :
    ‖hP.forcedGradient t ht‖ ≤ ((2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) / Real.sqrt (t : ℝ)) *
      Real.exp (65 * complexForceShift d Λ₀ ζ * (t : ℝ))) :=
  (hP.forcedGradient t ht).opNorm_le_bound (by positivity) (gradientValue_bound hP t ht)

/-- Every actual gradient of the evolved datum equals the bundled operator value. -/
theorem IsComplexEnvironmentSemigroup.forcedGradient_eq
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (t : ℝ≥0) (ht : 0 < t) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) G) :
    hP.forcedGradient t ht f = G :=
  WithLp.ofLp_injective 2 ((hP.forcedGradient_spec t ht f).unique hG)

/-- The gradient at time t+s is the bounded gradient at t applied after the evolution at s. -/
theorem IsComplexEnvironmentSemigroup.forcedGradient_add
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (t : ℝ≥0) (ht : 0 < t) (s : ℝ≥0) :
    hP.forcedGradient (t+s) (add_pos_of_pos_of_nonneg ht s.property) =
      (hP.forcedGradient t ht).comp (P s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply hP.forcedGradient_eq
  simpa only [hP.2.1, ContinuousLinearMap.comp_apply] using
    hP.forcedGradient_spec t ht (P s f)

/-- The actual forced gradient orbit is strongly continuous at all positive times. -/
theorem IsComplexEnvironmentSemigroup.continuous_forcedGradient_apply
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t : {t : ℝ≥0 // 0 < t} => hP.forcedGradient t.1 t.2 f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let δ : ℝ≥0 := t.1 / 2
  have hδ : 0 < δ := half_pos t.2
  have hδt : δ < t.1 := half_lt_self t.2
  have hv : Continuous (fun s : {s : ℝ≥0 // 0 < s} =>
      hP.forcedGradient δ hδ (P (s.1-δ) f)) :=
    (hP.forcedGradient δ hδ).continuous.comp
      ((hP.2.2.1 f).comp (continuous_subtype_val.sub continuous_const))
  apply hv.continuousAt.congr_of_eventuallyEq
  filter_upwards [(continuous_subtype_val.tendsto t).eventually
    (eventually_gt_nhds hδt)] with s hs
  have he := congrArg (fun A => A f) (hP.forcedGradient_add δ hδ (s.1-δ))
  simpa only [add_tsub_cancel_of_le hs.le, ContinuousLinearMap.comp_apply] using he

/-- Subtracting the reduced-law mean preserves the actual horizontal gradient. -/
theorem HasComplexHorizontalGradient.centered
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (centeredComplexLp Q f) G := by
  letI := reducedLaw_probability Q
  have hc := hasComplexHorizontalGradient_const (reducedLaw Q)
    (reducedLaw_stationary Q) (∫ ω, f ω ∂reducedLaw Q)
  intro j
  change HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
    (f - Lp.const 2 (reducedLaw Q) (∫ ω, f ω ∂reducedLaw Q)) (G j)
  simpa only [neg_one_smul, ← sub_eq_add_neg, sub_zero] using
    (hG j).add ((hc j).smul (-1))

/-- The centered forward evolution has the same actual gradient as the uncentered evolution. -/
theorem IsComplexEnvironmentSemigroup.forcedGradient_centered_spec
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (centeredComplexLp Q (P t (centeredComplexLp Q f))) (hP.forcedGradient t ht f) := by
  rw [hP.centered_apply]
  exact (hP.forcedGradient_spec t ht f).centered

/-- The actual twice-centered forward evolution satisfies the same uniform gradient smoothing bound. -/
theorem IsComplexEnvironmentSemigroup.exists_gradient_centered_forced
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (centeredComplexLp Q (P t (centeredComplexLp Q f))) G ∧
      ‖G‖ ≤ (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) / Real.sqrt (t : ℝ)) *
        Real.exp (65 * complexForceShift d Λ₀ ζ * (t : ℝ)) * ‖f‖ := by
  refine ⟨hP.forcedGradient t ht f, hP.forcedGradient_centered_spec t ht f, ?_⟩
  exact ((hP.forcedGradient t ht).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (hP.norm_forcedGradient_le t ht) (norm_nonneg f))

end EinsteinFull
