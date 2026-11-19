import EinsteinFull.External.DFGW.Reversibility
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Symmetry of transition-kernel correlations

For bounded measurable observables, the Markov property identifies the two-time correlation
with the transition-kernel pairing. Reversibility makes this pairing symmetric.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A transition-kernel pairing is the corresponding two-time correlation. -/
theorem integral_kernel_mul_eq_correlation (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ C, ∀ x, |f x| ≤ C) (hgb : ∃ C, ∀ x, |g x| ≤ C) (t : ℝ≥0) :
    (∫ x, (∫ y, f y ∂T t x) * g x ∂μ) =
      ∫ η : C(ℝ, S), f (η t) * g (η 0) ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  let ψ : C(ℝ, S) → ℝ := fun η => f (η t)
  let ζ : C(ℝ, S) → ℝ := fun η => g (η 0)
  have hψm : Measurable ψ := hf.comp (continuous_eval_const (t : ℝ)).measurable
  have hζm : Measurable ζ := hg.comp (continuous_eval_const 0).measurable
  have hψ : Integrable ψ P := Integrable.of_bound hψm.aestronglyMeasurable Cf
    (ae_of_all _ fun η => by simpa only [Real.norm_eq_abs] using hCf (η t))
  have hψζ : Integrable (ψ * ζ) P := by
    have hi := hψ.mul_bdd hζm.aestronglyMeasurable
      (ae_of_all P fun η => by simpa only [Real.norm_eq_abs] using hCg (η 0))
    exact hi.congr (ae_of_all P fun η => (Pi.mul_apply ψ ζ η).symm)
  have hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic 0) ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) := (Draft.dfgwPast (S := S)).le 0
  have hzero : Measurable[Draft.dfgwCoordSigma (S := S) (Set.Iic 0)]
      (fun η : C(ℝ, S) => η 0) := by
    apply Measurable.of_comap_le
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Iic (0 : ℝ)) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance) (0 : ℝ) (by change (0 : ℝ) ≤ 0; exact le_rfl) le_rfl
  have hζpast : StronglyMeasurable[Draft.dfgwCoordSigma (S := S) (Set.Iic 0)] ζ :=
    (hg.comp hzero).stronglyMeasurable
  have h1 := condExp_mul_of_stronglyMeasurable_right hζpast hψζ hψ
  have h2 : (∫ η, (P[ψ * ζ | Draft.dfgwCoordSigma (Set.Iic 0)]) η ∂P) =
      ∫ η, (ψ * ζ) η ∂P := integral_condExp hσ
  rw [integral_congr_ae h1] at h2
  have hmark := hP.markov t f hf ⟨Cf, hCf⟩
  have hk : Measurable fun x => ∫ y, f y ∂T t x :=
    (hf.stronglyMeasurable.integral_kernel (κ := T t)).measurable
  have hmap := integral_map (μ := P) (continuous_eval_const (0 : ℝ)).measurable.aemeasurable
    (f := fun x => (∫ y, f y ∂T t x) * g x) (by
      rw [hP.marginal]
      exact (hk.mul hg).aestronglyMeasurable)
  rw [hP.marginal] at hmap
  calc
    (∫ x, (∫ y, f y ∂T t x) * g x ∂μ) =
        ∫ η : C(ℝ, S), (∫ y, f y ∂T t (η 0)) * g (η 0) ∂P := hmap
    _ = ∫ η : C(ℝ, S), (P[ψ | Draft.dfgwCoordSigma (Set.Iic 0)]) η * ζ η ∂P := by
      apply integral_congr_ae
      filter_upwards [hmark] with η hη
      rw [hη]
    _ = ∫ η : C(ℝ, S), f (η t) * g (η 0) ∂P := by
      simpa only [Pi.mul_apply, ψ, ζ] using h2

/-- A reversible transition kernel is symmetric on bounded measurable observables. -/
theorem integral_kernel_mul_comm (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ C, ∀ x, |f x| ≤ C) (hgb : ∃ C, ∀ x, |g x| ≤ C) (t : ℝ≥0) :
    (∫ x, (∫ y, f y ∂T t x) * g x ∂μ) =
      ∫ x, (∫ y, g y ∂T t x) * f x ∂μ := by
  let : IsProbabilityMeasure P := hP.probability
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  have hft : Integrable (fun η : C(ℝ, S) => f (η t)) P :=
    Integrable.of_bound (hf.comp (continuous_eval_const (t : ℝ)).measurable).aestronglyMeasurable
      Cf (ae_of_all P fun η => by simpa only [Real.norm_eq_abs] using hCf (η t))
  have hgf : Integrable (fun η : C(ℝ, S) => g (η 0) * f (η t)) P :=
    hft.bdd_mul (hg.comp (continuous_eval_const (0 : ℝ)).measurable).aestronglyMeasurable
      (ae_of_all P fun η => by simpa only [Real.norm_eq_abs] using hCg (η 0))
  calc
    (∫ x, (∫ y, f y ∂T t x) * g x ∂μ) =
        ∫ η : C(ℝ, S), f (η t) * g (η 0) ∂P :=
      integral_kernel_mul_eq_correlation hP f g hf hg ⟨Cf, hCf⟩ ⟨Cg, hCg⟩ t
    _ = ∫ η : C(ℝ, S), g (η 0) * f (η t) ∂P := by
      simp only [mul_comm]
    _ = ∫ η : C(ℝ, S), f (η 0) * g (η t) ∂P :=
      integral_mul_eval_comm hP g f t hgf
    _ = ∫ η : C(ℝ, S), g (η t) * f (η 0) ∂P := by
      simp only [mul_comm]
    _ = ∫ x, (∫ y, g y ∂T t x) * f x ∂μ :=
      (integral_kernel_mul_eq_correlation hP g f hg hf ⟨Cg, hCg⟩ ⟨Cf, hCf⟩ t).symm

end EinsteinFull.External.DFGW
