import EinsteinFull.Work.W2.TransposeGraphGradientEnergySupport

/-!
# Bounded transpose-resolvent gradients and full-domain orbit continuity

The full transpose resolvent on all complex L2 data has a unique actual strong
horizontal gradient. Its energy estimate supplies a bounded complex linear map
with the Euclidean PiLp2 norm. On full generator graph data, the exact resolvent
identity and graph invariance recover a continuous gradient orbit, including
at time zero. This does not assert smoothing for arbitrary L2 initial data.
-/

open MeasureTheory
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

private def transposeResolventGradientValue (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) :
    PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
  WithLp.toLp 2
    (existsUnique_gradient_complexL2Transpose_forcedComplexResolvent_energy_le Q i ζ s hs rhs).exists.choose

private theorem transposeResolventGradientValue_spec (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs) rhs)
      (transposeResolventGradientValue Q i ζ s hs rhs) :=
  (existsUnique_gradient_complexL2Transpose_forcedComplexResolvent_energy_le Q i ζ s hs rhs).exists.choose_spec.1

private theorem transposeResolventGradientValue_bound (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ‖transposeResolventGradientValue Q i ζ s hs rhs‖ ≤
      Real.sqrt (4 * (Real.exp (2 * Λ₀) * Λ₀) / (s - complexForceShift d Λ₀ ζ)) * ‖rhs‖ := by
  have he := (existsUnique_gradient_complexL2Transpose_forcedComplexResolvent_energy_le
    Q i ζ s hs rhs).exists.choose_spec.2
  change ‖transposeResolventGradientValue Q i ζ s hs rhs‖ ^ 2 ≤ _ at he
  have hK : 0 ≤ 4 * (Real.exp (2 * Λ₀) * Λ₀) / (s - complexForceShift d Λ₀ ζ) :=
    div_nonneg (mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le
      (le_trans zero_le_one Q.ellipticity_parameter))) (sub_pos.mpr hs).le
  have h := Real.sqrt_le_sqrt he
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hK] using h

/-- The actual transpose resolvent gradient on every complex L2 datum, bundled
as a bounded complex linear operator with Euclidean coordinate norm. -/
def transposeResolventGradient (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
  let L : Lp ℂ 2 (reducedLaw Q) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
    { toFun := transposeResolventGradientValue Q i ζ s hs
      map_add' := fun f g => by
        apply WithLp.ofLp_injective 2
        apply (transposeResolventGradientValue_spec Q i ζ s hs (f + g)).unique
        intro j
        simpa only [map_add, PiLp.add_apply] using
          (transposeResolventGradientValue_spec Q i ζ s hs f j).add
            (transposeResolventGradientValue_spec Q i ζ s hs g j)
      map_smul' := fun c f => by
        change transposeResolventGradientValue Q i ζ s hs (c • f) =
          c • transposeResolventGradientValue Q i ζ s hs f
        apply WithLp.ofLp_injective 2
        apply (transposeResolventGradientValue_spec Q i ζ s hs (c • f)).unique
        intro j
        simpa only [map_smul, PiLp.smul_apply] using
          (transposeResolventGradientValue_spec Q i ζ s hs f j).smul c }
  L.mkContinuous
    (Real.sqrt (4 * (Real.exp (2 * Λ₀) * Λ₀) / (s - complexForceShift d Λ₀ ζ)))
    (transposeResolventGradientValue_bound Q i ζ s hs)

/-- Literal full strong horizontal-gradient specification of the bounded map. -/
theorem transposeResolventGradient_spec (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs) rhs)
      (transposeResolventGradient Q i ζ s hs rhs) :=
  transposeResolventGradientValue_spec Q i ζ s hs rhs

/-- Structural resolvent-gradient operator bound, uniform over all L2 data. -/
theorem norm_transposeResolventGradient_le (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) :
    ‖transposeResolventGradient Q i ζ s hs‖ ≤
      Real.sqrt (4 * (Real.exp (2 * Λ₀) * Λ₀) / (s - complexForceShift d Λ₀ ζ)) :=
  (transposeResolventGradient Q i ζ s hs).opNorm_le_bound (Real.sqrt_nonneg _)
    (transposeResolventGradientValue_bound Q i ζ s hs)

/-- Every strong gradient of the actual transpose resolvent equals this map. -/
theorem transposeResolventGradient_eq (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s)
    {rhs : Lp ℂ 2 (reducedLaw Q)}
    {G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs) rhs) G) :
    transposeResolventGradient Q i ζ s hs rhs = G :=
  WithLp.ofLp_injective 2 ((transposeResolventGradient_spec Q i ζ s hs rhs).unique hG)

/-- The literal gradient specification determines the bounded complex linear
operator uniquely on its entire L2 domain. -/
theorem transposeResolventGradient_unique (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s)
    (A : Lp ℂ 2 (reducedLaw Q) →L[ℂ]
      PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)))
    (hA : ∀ rhs, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs) rhs) (A rhs)) :
    transposeResolventGradient Q i ζ s hs = A := by
  ext rhs : 1
  exact transposeResolventGradient_eq Q i ζ s hs (hA rhs)

/-- The genuine resolvent identity recovers the strong gradient of every full
transpose-generator graph pair. -/
theorem IsComplexTransposeGeneratorPair.resolventGradient_spec
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f
      (transposeResolventGradient Q i ζ s hs ((s : ℂ) • f - g)) := by
  have h := transposeResolventGradient_spec Q i ζ s hs ((s : ℂ) • f - g)
  rwa [(isComplexTransposeGeneratorPair_iff_resolvent Q i ζ s hs f g).mp hfg] at h

/-- Transport along the actual full generator graph supplies the gradient of
each transpose orbit value from one fixed real resolvent shift. -/
theorem IsComplexTransposeSemigroup.resolventGradient_orbit_spec
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) (t : ℝ≥0) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (T t f)
      (transposeResolventGradient Q i ζ s hs ((s : ℂ) • T t f - T t g)) :=
  (hT.map_generator hP hfg t).resolventGradient_spec s hs

/-- For full generator graph initial data, the actual gradient orbit is
continuous on the entire nonnegative time axis, including zero. -/
theorem IsComplexTransposeSemigroup.continuous_resolventGradient_orbit
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) :
    Continuous (fun t => transposeResolventGradient Q i ζ s hs
      ((s : ℂ) • T t f - T t g)) :=
  (transposeResolventGradient Q i ζ s hs).continuous.comp
    (((hT.continuous_apply hP f).const_smul (s : ℂ)).sub (hT.continuous_apply hP g))

/-- Full transpose-generator initial data have a unique continuous actual
Euclidean gradient orbit. No additional orbit regularity is assumed. -/
theorem IsComplexTransposeSemigroup.existsUnique_continuous_gradient_orbit
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃! G : ℝ≥0 → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      (∀ t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (T t f) (G t)) ∧
        Continuous G := by
  let s := complexForceShift d Λ₀ ζ + 1
  have hs : complexForceShift d Λ₀ ζ < s := lt_add_one _
  refine ⟨fun t => transposeResolventGradient Q i ζ s hs ((s : ℂ) • T t f - T t g),
    ⟨hT.resolventGradient_orbit_spec hP hfg s hs,
      hT.continuous_resolventGradient_orbit hP f g s hs⟩, ?_⟩
  intro H hH
  funext t
  exact WithLp.ofLp_injective 2
    ((hH.1 t).unique (hT.resolventGradient_orbit_spec hP hfg s hs t))

/-- In particular the literal bilinear transpose of the constructed forced
evolution has this unique continuous gradient orbit for every full graph datum. -/
theorem existsUnique_continuous_gradient_complexL2Transpose_forcedComplexEvolution_orbit
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃! G : ℝ≥0 → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      (∀ t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (complexL2Transpose (reducedLaw Q) (forcedComplexEvolution Q i ζ t) f) (G t)) ∧
        Continuous G :=
  (isComplexTransposeSemigroup_complexL2Transpose Q (forcedComplexEvolution Q i ζ)).existsUnique_continuous_gradient_orbit
    (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ) hfg

end EinsteinFull
