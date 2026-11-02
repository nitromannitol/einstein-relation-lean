import EinsteinFull.Calculus.ComplexUnforcedSmoothingSupport

/-!
# The actual bounded unforced horizontal gradient operator

Positive-time smoothing and uniqueness bundle the actual gradient as a bounded
complex linear map with the structural square-root time bound. The semigroup
law transports it without differentiating any random representative.
-/

open MeasureTheory Filter
open scoped NNReal Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

private def gradientValue (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℂ 2 (reducedLaw Q)) :
    PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
  (hP.exists_gradient_unforced f t ht).choose

private theorem gradientValue_spec (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t f) (gradientValue hP t ht f) :=
  (hP.exists_gradient_unforced f t ht).choose_spec.1

private theorem gradientValue_bound (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖gradientValue hP t ht f‖ ≤ Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀) / (t : ℝ)) * ‖f‖ :=
  (hP.exists_gradient_unforced f t ht).choose_spec.2

/-- The actual horizontal gradient of any complete unforced family, as a bounded operator. -/
def IsComplexEnvironmentSemigroup.unforcedGradient
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0) (ht : 0 < t) :
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
  L.mkContinuous (Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀) / (t : ℝ)))
    (gradientValue_bound hP t ht)

/-- The bounded operator is the actual full strong horizontal gradient of the evolved datum. -/
theorem IsComplexEnvironmentSemigroup.unforcedGradient_spec
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t f) (hP.unforcedGradient t ht f) :=
  gradientValue_spec hP t ht f

/-- The actual unforced gradient operator has the structural t^(-1/2) norm bound. -/
theorem IsComplexEnvironmentSemigroup.norm_unforcedGradient_le
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0) (ht : 0 < t) :
    ‖hP.unforcedGradient t ht‖ ≤ Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀) / (t : ℝ)) :=
  (hP.unforcedGradient t ht).opNorm_le_bound (Real.sqrt_nonneg _) (gradientValue_bound hP t ht)

/-- Every actual gradient of the evolved datum equals the bundled operator value. -/
theorem IsComplexEnvironmentSemigroup.unforcedGradient_eq
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (t : ℝ≥0) (ht : 0 < t) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) G) :
    hP.unforcedGradient t ht f = G :=
  WithLp.ofLp_injective 2 ((hP.unforcedGradient_spec t ht f).unique hG)

/-- The gradient at time t+s is the bounded gradient at t applied after the evolution at s. -/
theorem IsComplexEnvironmentSemigroup.unforcedGradient_add
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (t : ℝ≥0) (ht : 0 < t) (s : ℝ≥0) :
    hP.unforcedGradient (t+s) (add_pos_of_pos_of_nonneg ht s.property) =
      (hP.unforcedGradient t ht).comp (P s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply hP.unforcedGradient_eq
  simpa only [hP.2.1, ContinuousLinearMap.comp_apply] using
    hP.unforcedGradient_spec t ht (P s f)

/-- The actual unforced gradient orbit is strongly continuous at all positive times. -/
theorem IsComplexEnvironmentSemigroup.continuous_unforcedGradient_apply
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t : {t : ℝ≥0 // 0 < t} => hP.unforcedGradient t.1 t.2 f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let δ : ℝ≥0 := t.1 / 2
  have hδ : 0 < δ := half_pos t.2
  have hδt : δ < t.1 := half_lt_self t.2
  have hv : Continuous (fun s : {s : ℝ≥0 // 0 < s} =>
      hP.unforcedGradient δ hδ (P (s.1-δ) f)) :=
    (hP.unforcedGradient δ hδ).continuous.comp
      ((hP.2.2.1 f).comp (continuous_subtype_val.sub continuous_const))
  apply hv.continuousAt.congr_of_eventuallyEq
  filter_upwards [(continuous_subtype_val.tendsto t).eventually
    (eventually_gt_nhds hδt)] with s hs
  have he := congrArg (fun A => A f) (hP.unforcedGradient_add δ hδ (s.1-δ))
  simpa only [add_tsub_cancel_of_le hs.le, ContinuousLinearMap.comp_apply] using he

end EinsteinFull
