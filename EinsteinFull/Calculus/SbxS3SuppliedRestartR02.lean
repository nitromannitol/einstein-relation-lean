import EinsteinFull.Calculus.U1RegularKernelContinuity
import EinsteinFull.Calculus.U2GMPFinalEnvironment

open EinsteinRelation EinsteinFull MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal

namespace EinsteinFull

/-- Every starting law of a supplied reduced kernel has the countable
conditional restart property on a common conull environment event. -/
theorem s3_supplied_reduced_countable_condExp_restart
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (s : ℕ → ℝ≥0) (F : ℕ → Path d → ℝ),
      (∀ n, StronglyMeasurable (F n)) → ∀ (C : ℕ → ℝ),
      (∀ n γ, ‖F n γ‖ ≤ C n) →
      ∀ᵐ γ ∂P (x, ω), ∀ n,
        ((P (x, ω))[fun η => F n (MarkovProcess.ContinuousPath.shift (s n) η) |
          MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) (s n)]) γ =
        ∫ η, F n η ∂P (γ (s n), ω) := by
  filter_upwards [hP] with ω hω
  obtain ⟨hreg, R, hR⟩ := hω
  intro x s F hF C hFC
  letI : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  have h : ∀ᵐ γ ∂R.pathLaw x, ∀ n,
      ((R.pathLaw x)[fun η => F n (MarkovProcess.ContinuousPath.shift (s n) η) |
        MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) (s n)]) γ =
      ∫ η, F n η ∂R.pathLaw (γ (s n)) := by
    apply ae_all_iff.mpr
    intro n
    exact SubdiffusiveProcess.Section10.condExp_shift_realization
      (u2RegularC0KernelSemigroup hd (zeroPotentialReducedPair ω) lam
        (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hreg)
      (u2_regular_kernel_conservative hd (zeroPotentialReducedPair ω) lam
        (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hreg)
      (u2RegularC0KernelSemigroup_isFeller hd (zeroPotentialReducedPair ω) lam
        (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hreg)
      R.pathLaw (u6_arbitrary_supplied_gmp_canonical_FDD hd (zeroPotentialReducedPair ω)
        lam (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        hreg h0 h1 R) x (s n) (F n) (hF n) (C n) (hFC n)
  simpa only [hR] using h

/-- Countably many bounded measurable endpoint observations restart under the
same supplied reduced laws and on one conull environment event. -/
theorem s3_supplied_reduced_countable_endpoint_condExp_restart
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (s t : ℕ → ℝ≥0)
      (f : ℕ → Vec d → ℝ), (∀ n, StronglyMeasurable (f n)) →
      ∀ (C : ℕ → ℝ), (∀ n y, ‖f n y‖ ≤ C n) →
      ∀ᵐ γ ∂P (x, ω), ∀ n,
        ((P (x, ω))[fun η => f n (η (s n + t n)) |
          MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) (s n)]) γ =
        ∫ η, f n (η (t n)) ∂P (γ (s n), ω) := by
  filter_upwards [s3_supplied_reduced_countable_condExp_restart hd Q lam h0 h1 P hP]
    with ω hω
  intro x s t f hf C hC
  have h := hω x s (fun n η => f n (η (t n)))
    (fun n => (hf n).comp_measurable
      (MarkovProcess.ContinuousPath.measurable_coordinateProcess (t n)))
    C (fun n η => hC n (η (t n)))
  simpa only [MarkovProcess.ContinuousPath.shift_apply] using h

end EinsteinFull
