import EinsteinRelation.Carriers.DensityAnnealedTwins
import EinsteinRelation.Density.LaplaceDensityExistence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Exponential

/-! # The Laplace-time integral identity for the reduced density

Let `rho` be a nonnegative measurable density of the reduced Laplace-time law
`reducedLaplaceObservedLaw` with respect to the reduced reference law `Measure.map reduce Q`.
For every bounded measurable `g` on the reduced canonical space,

`∫ rho g d(map reduce Q) = ∫_{[0, ∞)} s e^{-s t} E[g(ω_t)] dt`,

where `E[g(ω_t)]` is the integral of `g ∘ reducedObservationAt t` against the annealed joint law.

The argument has four steps. The density turns the reference integral into an integral against
the observed law. The observed law is the image of the product of the exponential law with the
annealed joint law. Fubini's theorem splits that product integral. The exponential integral over
`ℝ` becomes an integral over `[0, ∞)` against the density `s e^{-s t}`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace EinsteinRelation.Density

/-- The exponential law of rate `r > 0` integrates `φ` as an integral over `[0, ∞)` against the
density `r e^{-r t}`. -/
theorem integral_expMeasure_eq_setIntegral_Ici {r : ℝ} (hr : 0 < r) (φ : ℝ → ℝ) :
    ∫ t, φ t ∂(ProbabilityTheory.expMeasure r) =
      ∫ t in Set.Ici (0:ℝ), r * Real.exp (-(r * t)) * φ t := by
  have hmeas : Measurable (ProbabilityTheory.exponentialPDF r) :=
    ENNReal.measurable_ofReal.comp (ProbabilityTheory.measurable_exponentialPDFReal r)
  have hfin : ∀ᵐ x ∂(volume : Measure ℝ), ProbabilityTheory.exponentialPDF r x < ∞ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hexp : ProbabilityTheory.expMeasure r =
      (volume : Measure ℝ).withDensity (ProbabilityTheory.exponentialPDF r) := rfl
  have hpt : ∀ t : ℝ, (ProbabilityTheory.exponentialPDF r t).toReal • φ t =
      (Set.Ici (0:ℝ)).indicator (fun t => r * Real.exp (-(r * t)) * φ t) t := by
    intro t
    by_cases ht : 0 ≤ t
    · rw [ProbabilityTheory.exponentialPDF_of_nonneg ht,
        ENNReal.toReal_ofReal (mul_nonneg hr.le (Real.exp_pos (-(r * t))).le), smul_eq_mul,
        Set.indicator_of_mem (Set.mem_Ici.mpr ht)]
    · rw [ProbabilityTheory.exponentialPDF_of_neg (not_le.mp ht), ENNReal.toReal_zero, zero_smul,
        Set.indicator_of_notMem (show t ∉ Set.Ici (0:ℝ) from fun h => ht (Set.mem_Ici.mp h))]
  rw [hexp, integral_withDensity_eq_integral_toReal_smul hmeas hfin φ]
  calc ∫ t, (ProbabilityTheory.exponentialPDF r t).toReal • φ t
      = ∫ t, (Set.Ici (0:ℝ)).indicator (fun t => r * Real.exp (-(r * t)) * φ t) t :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ t in Set.Ici (0:ℝ), r * Real.exp (-(r * t)) * φ t :=
        integral_indicator measurableSet_Ici

/-- The annealed joint law of the production twin is a probability measure when the environment
law is one. -/
theorem isProbabilityMeasure_annealedCoordinateJoint {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) :
    IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q P origin_probability) :=
  Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
    Q (originLaw P) origin_probability

/-- The integral against the reduced observed law is the integral of the composed observation
against the product of the exponential law and the annealed joint law. -/
theorem integral_reducedLaplaceObservedLaw_eq {d : ℕ} (Q : Measure (FieldPair d))
    (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (s : {r : ℝ // 0 < r}) (g : FieldPair d → ℝ) (hg : Measurable g) :
    ∫ w, g w ∂(Carriers.reducedLaplaceObservedLaw Q P origin_probability s) =
      ∫ z, g (Carriers.reducedObservationAt z.1.toNNReal z.2)
        ∂((ProbabilityTheory.expMeasure s.1).prod
          (Carriers.annealedCoordinateJoint Q P origin_probability)) := by
  unfold Carriers.reducedLaplaceObservedLaw
  exact integral_map
    (EinsteinRelation.laplaceDensity_measurable_observation (d := d)).aemeasurable
    hg.aestronglyMeasurable

/-- The fixed-time observation integral `t ↦ E[g(ω_t)]` is measurable in the time. -/
theorem measurable_integral_reducedObservationAt {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (g : FieldPair d → ℝ) (hg : Measurable g) :
    Measurable (fun t : ℝ =>
      ∫ z, g (Carriers.reducedObservationAt t.toNNReal z)
        ∂(Carriers.annealedCoordinateJoint Q P origin_probability)) := by
  haveI := isProbabilityMeasure_annealedCoordinateJoint Q P origin_probability
  have hF : Measurable (fun p : ℝ × (FieldPair d × Path d) =>
      g (Carriers.reducedObservationAt p.1.toNNReal p.2)) :=
    hg.comp (EinsteinRelation.laplaceDensity_measurable_observation (d := d))
  exact (hF.stronglyMeasurable.integral_prod_right').measurable

/-- The fixed-time observation integral of a function bounded by `B` is bounded by `B`. -/
theorem abs_integral_reducedObservationAt_le {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (g : FieldPair d → ℝ) {B : ℝ} (hB : ∀ w, |g w| ≤ B) (t : ℝ) :
    |∫ z, g (Carriers.reducedObservationAt t.toNNReal z)
        ∂(Carriers.annealedCoordinateJoint Q P origin_probability)| ≤ B := by
  haveI := isProbabilityMeasure_annealedCoordinateJoint Q P origin_probability
  have hbound : ∀ᵐ z ∂(Carriers.annealedCoordinateJoint Q P origin_probability),
      ‖g (Carriers.reducedObservationAt t.toNNReal z)‖ ≤ B :=
    Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB _
  have h := norm_integral_le_of_norm_le_const hbound
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

/-- For a nonnegative measurable density `rho` of the reduced Laplace-time law, integration of a
bounded measurable `g` against `rho` is the exponential-weighted integral over `[0, ∞)` of the
fixed-time expectations `E[g(ω_t)]`. -/
theorem integral_mul_density_eq_setIntegral_Ici {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (s : {r : ℝ // 0 < r}) (rho : FieldPair d → ℝ)
    (hrho : Carriers.IsReducedLaplaceDensity Q P origin_probability s rho)
    (g : FieldPair d → ℝ) (hg : Measurable g) {B : ℝ} (hB : ∀ w, |g w| ≤ B) :
    ∫ w, rho w * g w ∂(Measure.map reduce Q) =
      ∫ t in Set.Ici (0:ℝ), s.1 * Real.exp (-(s.1 * t)) *
        ∫ z, g (Carriers.reducedObservationAt t.toNNReal z)
          ∂(Carriers.annealedCoordinateJoint Q P origin_probability) := by
  obtain ⟨hρ, hnonneg, hlaw⟩ := hrho
  haveI := isProbabilityMeasure_annealedCoordinateJoint Q P origin_probability
  haveI := ProbabilityTheory.isProbabilityMeasure_expMeasure s.2
  have hm : Measurable (fun w => ENNReal.ofReal (rho w)) := ENNReal.measurable_ofReal.comp hρ
  have hfin : ∀ᵐ w ∂(Measure.map reduce Q), ENNReal.ofReal (rho w) < ∞ :=
    Filter.Eventually.of_forall fun w => ENNReal.ofReal_lt_top
  have hdens : ∫ w, g w ∂((Measure.map reduce Q).withDensity fun w => ENNReal.ofReal (rho w)) =
      ∫ w, rho w * g w ∂(Measure.map reduce Q) := by
    rw [integral_withDensity_eq_integral_toReal_smul hm hfin g]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show (ENNReal.ofReal (rho w)).toReal • g w = rho w * g w
    rw [ENNReal.toReal_ofReal (hnonneg w), smul_eq_mul]
  have hint : Integrable (fun z : ℝ × (FieldPair d × Path d) =>
      g (Carriers.reducedObservationAt z.1.toNNReal z.2))
      ((ProbabilityTheory.expMeasure s.1).prod
        (Carriers.annealedCoordinateJoint Q P origin_probability)) := by
    have hF : Measurable (fun z : ℝ × (FieldPair d × Path d) =>
        g (Carriers.reducedObservationAt z.1.toNNReal z.2)) :=
      hg.comp (EinsteinRelation.laplaceDensity_measurable_observation (d := d))
    exact Integrable.of_bound hF.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB _)
  calc ∫ w, rho w * g w ∂(Measure.map reduce Q)
      = ∫ w, g w ∂((Measure.map reduce Q).withDensity fun w => ENNReal.ofReal (rho w)) :=
        hdens.symm
    _ = ∫ w, g w ∂(Carriers.reducedLaplaceObservedLaw Q P origin_probability s) := by
        rw [hlaw]
    _ = ∫ z, g (Carriers.reducedObservationAt z.1.toNNReal z.2)
          ∂((ProbabilityTheory.expMeasure s.1).prod
            (Carriers.annealedCoordinateJoint Q P origin_probability)) :=
        integral_reducedLaplaceObservedLaw_eq Q P origin_probability s g hg
    _ = ∫ t, ∫ z, g (Carriers.reducedObservationAt t.toNNReal z)
          ∂(Carriers.annealedCoordinateJoint Q P origin_probability)
          ∂(ProbabilityTheory.expMeasure s.1) :=
        integral_prod (fun z : ℝ × (FieldPair d × Path d) =>
          g (Carriers.reducedObservationAt z.1.toNNReal z.2)) hint
    _ = ∫ t in Set.Ici (0:ℝ), s.1 * Real.exp (-(s.1 * t)) *
          ∫ z, g (Carriers.reducedObservationAt t.toNNReal z)
            ∂(Carriers.annealedCoordinateJoint Q P origin_probability) :=
        integral_expMeasure_eq_setIntegral_Ici s.2 (fun t =>
          ∫ z, g (Carriers.reducedObservationAt t.toNNReal z)
            ∂(Carriers.annealedCoordinateJoint Q P origin_probability))

/-- The reduced Laplace-time density has total mass one. -/
theorem integral_density_eq_one {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (s : {r : ℝ // 0 < r}) (rho : FieldPair d → ℝ)
    (hrho : Carriers.IsReducedLaplaceDensity Q P origin_probability s rho) :
    ∫ w, rho w ∂(Measure.map reduce Q) = 1 := by
  haveI := isProbabilityMeasure_annealedCoordinateJoint Q P origin_probability
  haveI := ProbabilityTheory.isProbabilityMeasure_expMeasure s.2
  have hJ : ∫ _z, (1:ℝ) ∂(Carriers.annealedCoordinateJoint Q P origin_probability) = 1 := by
    simp [integral_const]
  calc ∫ w, rho w ∂(Measure.map reduce Q)
      = ∫ w, rho w * (1:ℝ) ∂(Measure.map reduce Q) := by
        simp only [mul_one]
    _ = ∫ t in Set.Ici (0:ℝ), s.1 * Real.exp (-(s.1 * t)) *
          ∫ _z, (1:ℝ) ∂(Carriers.annealedCoordinateJoint Q P origin_probability) :=
        integral_mul_density_eq_setIntegral_Ici Q P origin_probability s rho hrho
          (fun _ => 1) measurable_const (B := 1) (fun _ => by simp)
    _ = ∫ t in Set.Ici (0:ℝ), s.1 * Real.exp (-(s.1 * t)) * (1:ℝ) := by
        rw [hJ]
    _ = ∫ t, (1:ℝ) ∂(ProbabilityTheory.expMeasure s.1) :=
        (integral_expMeasure_eq_setIntegral_Ici s.2 (fun _ => (1:ℝ))).symm
    _ = 1 := by
        simp [integral_const]

end EinsteinRelation.Density
