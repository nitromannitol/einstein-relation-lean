import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_environment_u23_unforced_u2D_process
import EinsteinFull.Calculus.C27RealForceRealization
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Frozen.ReducedClockRate
import EinsteinRelation.Clock.CentredClockField
import EinsteinRelation.Clock.ClockExpectation
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Calculus.ComplexSemigroupCenteringSupport
import EinsteinFull.Calculus.ComplexTransposeResolventSupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The literal joint-law clock mean is the physical density mean, without
identifying the reduced second coordinate with the physical potential. -/
theorem c20_clock_mean_eq_physical {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) :
    (∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q) =
      ∫ ω, clockDensity ω 0 ∂Q.measure := by
  exact integral_map Probability.measurable_reduce.aemeasurable
    Clock.continuous_clockAtOrigin.aestronglyMeasurable

/-- The actual clock observable is integrable under the joint reduced law. -/
theorem c20_clock_integrable {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) :
    Integrable (fun ω : FieldPair d => ω.2 (0 : Vec d)) (reducedLaw Q) :=
  Clock.integrable_clockAtOrigin Q

/-- Positivity is obtained from the uniform physical bounds, before any
almost-sure clock-rate theorem is used. -/
theorem c20_clock_mean_pos {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) :
    0 < ∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q := by
  exact lt_of_lt_of_le
    (inv_pos.mpr (Clock.sourceReducedBound_pos Q.ellipticity_parameter))
    (reducedClockMean_bounds Q).1

/-- Construct the complex L² clock from the actual bounded joint observable;
no smoothness or extra observation witness is assumed. -/
theorem c20_exists_clock_observation {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) :
    ∃ μ : Lp ℂ 2 (reducedLaw Q), IsReducedClockObservation Q μ := by
  letI : IsProbabilityMeasure (reducedLaw Q) :=
    Clock.isProbabilityMeasure_reducedReferenceLaw Q
  have hm : MemLp (fun ω : FieldPair d => (ω.2 (0 : Vec d) : ℂ))
      2 (reducedLaw Q) := by
    apply MemLp.of_bound
      (Complex.continuous_ofReal.comp Clock.continuous_clockAtOrigin).aestronglyMeasurable
      (sourceReducedBound Λ)
    filter_upwards [Clock.ae_abs_clockAtOrigin_le Q] with ω hω
    simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hω
  exact ⟨hm.toLp _, hm.coeFn_toLp⟩

/-- Extract the canonical supplied-path realization and its invariant literal
clock mean from the permitted stationary-environment graph dependency.
This does not assert an almost-sure path ergodic limit. -/
theorem c20_supplied_unforced_clock_realization
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0)
        0 (Y (0, ω))) :
    ∃ (μ : Lp ℂ 2 (reducedLaw Q))
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsReducedClockObservation Q μ ∧
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P ∧
      (∀ t : ℝ≥0, (∫ ω, P t μ ω ∂reducedLaw Q) =
        Complex.ofReal (∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q)) ∧
      (∀ t : ℝ≥0, ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => μ (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
        P t μ (reduce ω) =
          ∫ γ : Path d, μ (translate (γ t) (reduce ω)) ∂Y (0, ω)) := by
  obtain ⟨μ, hμ⟩ := c20_exists_clock_observation Q
  obtain ⟨P, hP, _htranspose, hmass, _hfixed, _henergy, hrealize⟩ := id hunforced
  refine ⟨μ, P, hμ, hP, ?_, (fun t => hrealize Y hY t μ)⟩
  intro t
  calc
    (∫ ω, P t μ ω ∂reducedLaw Q) = ∫ ω, μ ω ∂reducedLaw Q := (hmass t μ).2
    _ = ∫ ω, (ω.2 (0 : Vec d) : ℂ) ∂reducedLaw Q := integral_congr_ae hμ
    _ = Complex.ofReal (∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q) := integral_complex_ofReal

/-- A generator coboundary has an exact continuous-time primitive along the
canonical semigroup orbit. This uses the full frozen generator graph. -/
theorem c20_integral_generator_orbit {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g) = P t f - f := by
  have hf : Continuous (fun s : ℝ => P s.toNNReal f) :=
    (hP.2.2.1 f).comp continuous_real_toNNReal
  have hg : Continuous (fun s : ℝ => P s.toNNReal g) :=
    (hP.2.2.1 g).comp continuous_real_toNNReal
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (a := (0 : ℝ)) (b := (t : ℝ)) t.property hf.continuousOn
    (fun s hs => (hP.hasDerivWithinAt_orbit hfg s hs.1.le).mono
      Set.Ioi_subset_Ici_self) (hg.intervalIntegrable 0 t)
  simpa only [Real.toNNReal_coe, Real.toNNReal_zero, hP.1,
    ContinuousLinearMap.id_apply] using h

/-- Contraction bounds a generator coboundary's integrated orbit uniformly
in terminal time, rather than by a constant growing with time. -/
theorem c20_integral_generator_orbit_bound {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (hcontract : ∀ t : ℝ≥0, ∀ f : Lp ℂ 2 (reducedLaw Q), ‖P t f‖ ≤ ‖f‖)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    (t : ℝ≥0) :
    ‖∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g‖ ≤ 2 * ‖f‖ := by
  rw [c20_integral_generator_orbit hP hfg t]
  calc
    ‖P t f - f‖ ≤ ‖P t f‖ + ‖f‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (hcontract t f) le_rfl
    _ = 2 * ‖f‖ := (two_mul _).symm

/-- Averaging any contractive orbit remains contractive, including terminal
time zero. This is the uniform estimate needed to pass to a dense closure. -/
theorem c20_semigroup_average_norm_le {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hcontract : ∀ t : ℝ≥0, ∀ f : Lp ℂ 2 (reducedLaw Q), ‖P t f‖ ≤ ‖f‖)
    (g : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    ‖(t : ℝ)⁻¹ • (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g)‖ ≤ ‖g‖ := by
  by_cases ht : t = 0
  · subst t
    simpa only [NNReal.coe_zero, inv_zero, zero_smul, norm_zero] using norm_nonneg g
  have htpos : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  have hb : ‖∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g‖ ≤ ‖g‖ * (t : ℝ) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (t : ℝ)) (fun s _ => hcontract s.toNNReal g)
    simpa only [sub_zero, abs_of_nonneg htpos.le] using h
  rw [norm_smul]
  have hn : ‖(t : ℝ)⁻¹‖ = (t : ℝ)⁻¹ :=
    Real.norm_of_nonneg (inv_nonneg.mpr htpos.le)
  rw [hn]
  calc
    (t : ℝ)⁻¹ * ‖∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g‖ ≤
        (t : ℝ)⁻¹ * (‖g‖ * (t : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr t.property)
    _ = ‖g‖ := by field_simp [htpos.ne']

/-- The canonical continuous-time Cesàro average vanishes on generator
coboundaries. Pathwise almost-sure convergence is a separate remaining step. -/
theorem c20_generator_average_tendsto_zero {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (hcontract : ∀ t : ℝ≥0, ∀ f : Lp ℂ 2 (reducedLaw Q), ‖P t f‖ ≤ ‖f‖)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
      (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun t : ℝ≥0 => (2 * ‖f‖) / (t : ℝ))
  · intro t
    rw [norm_smul]
    have ht : ‖(t : ℝ)⁻¹‖ = (t : ℝ)⁻¹ :=
      Real.norm_of_nonneg (inv_nonneg.mpr t.property)
    rw [ht]
    calc
      (t : ℝ)⁻¹ * ‖∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g‖ ≤
          (t : ℝ)⁻¹ * (2 * ‖f‖) :=
        mul_le_mul_of_nonneg_left (c20_integral_generator_orbit_bound hP hcontract hfg t)
          (inv_nonneg.mpr t.property)
      _ = (2 * ‖f‖) / (t : ℝ) := by rw [div_eq_mul_inv, mul_comm]
  · exact tendsto_const_nhds.div_atTop (NNReal.tendsto_coe_atTop.mpr tendsto_id)

/-- The permitted graph dependency supplies the preceding analytic bridge
without a new contraction premise at the source-facing boundary. -/
theorem c20_unforced_generator_averages
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) :
    ∃ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P ∧
      ∀ f g : Lp ℂ 2 (reducedLaw Q),
        IsComplexGeneratorPair Q ⟨0, by omega⟩ 0 f g →
        Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
          (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g)) atTop (𝓝 0) := by
  obtain ⟨P, hP, _, hmass, _, _, _⟩ := id hunforced
  exact ⟨P, hP, fun _ _ hfg =>
    c20_generator_average_tendsto_zero hP (fun t f => (hmass t f).1) hfg⟩

/-- Continuous-time averaging respects differences in the actual L² carrier. -/
theorem c20_semigroup_average_sub {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (f g : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    (t : ℝ)⁻¹ • (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal (f - g)) =
      (t : ℝ)⁻¹ • (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f) -
      (t : ℝ)⁻¹ • (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g) := by
  have hf : IntervalIntegrable (fun s : ℝ => P s.toNNReal f) volume 0 (t : ℝ) :=
    ((hP.2.2.1 f).comp continuous_real_toNNReal).intervalIntegrable 0 (t : ℝ)
  have hg : IntervalIntegrable (fun s : ℝ => P s.toNNReal g) volume 0 (t : ℝ) :=
    ((hP.2.2.1 g).comp continuous_real_toNNReal).intervalIntegrable 0 (t : ℝ)
  simp only [map_sub, intervalIntegral.integral_sub hf hg, smul_sub]

/-- The contraction estimate extends the generator-coboundary limit to the
norm closure of the full generator range, with no extra spectral premise. -/
theorem c20_generator_range_closure_average_tendsto_zero {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (hcontract : ∀ t : ℝ≥0, ∀ f : Lp ℂ 2 (reducedLaw Q), ‖P t f‖ ≤ ‖f‖)
    {g : Lp ℂ 2 (reducedLaw Q)}
    (hg : g ∈ closure {v | ∃ u, IsComplexGeneratorPair Q i 0 u v}) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
      (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨v, ⟨u, huv⟩, hgv⟩ := Metric.mem_closure_iff.mp hg (ε / 2) (half_pos hε)
  have hv := Metric.tendsto_nhds.mp
    (c20_generator_average_tendsto_zero hP hcontract huv) (ε / 2) (half_pos hε)
  filter_upwards [hv] with t ht
  rw [dist_zero_right] at ht ⊢
  have hd := c20_semigroup_average_norm_le hcontract (g - v) t
  rw [c20_semigroup_average_sub hP g v t] at hd
  have hgv' : ‖g - v‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hgv
  calc
    ‖(t : ℝ)⁻¹ • (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g)‖ ≤
        ‖(t : ℝ)⁻¹ • (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g) -
          (t : ℝ)⁻¹ • (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal v)‖ +
        ‖(t : ℝ)⁻¹ • (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal v)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ ‖g - v‖ + ‖(t : ℝ)⁻¹ • (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal v)‖ :=
      add_le_add hd le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hgv' ht
    _ = ε := add_halves ε

/-- The bilinear annihilator of the full generator range is its unforced
kernel. The reverse adjoint inclusion supplies domain regularity. -/
theorem c20_generator_annihilator_iff_kernel {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∀ u v : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i 0 u v →
      (∫ ω, f ω * v ω ∂reducedLaw Q) = 0) ↔
        IsComplexGeneratorPair Q i 0 f 0 := by
  have hz (u : Lp ℂ 2 (reducedLaw Q)) :
      (∫ ω, (0 : Lp ℂ 2 (reducedLaw Q)) ω * u ω ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp only [hω, Pi.zero_apply, zero_mul]
  rw [← isComplexTransposeGeneratorPair_zero_iff]
  rw [isComplexTransposeGeneratorPair_iff_bilinear_adjoint]
  constructor
  · intro h u v huv
    rw [hz, h u v huv]
  · intro h u v huv
    exact (h u v huv).symm.trans (hz u)

/-- Fixed vectors of the actual semigroup are exactly the full generator
kernel, using the frozen strong-generator characterization in both directions. -/
theorem c20_generator_kernel_iff_fixed {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (f : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexGeneratorPair Q i 0 f 0 ↔ ∀ t : ℝ≥0, P t f = f := by
  constructor
  · exact fun hf t => hP.map_kernel hf t
  · intro hf
    apply (hP.2.2.2 f 0).mp
    simpa only [hf, sub_self, smul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (0 : Lp ℂ 2 (reducedLaw Q)))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 0))

/-- The exact stationary-environment graph dependency identifies every
annihilator of the full unforced generator range with an actual constant. -/
theorem c20_unforced_generator_annihilator_constants
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    (∀ u v : Lp ℂ 2 (reducedLaw Q),
      IsComplexGeneratorPair Q (⟨0, by omega⟩ : Fin d) 0 u v →
        (∫ ω, f ω * v ω ∂reducedLaw Q) = 0) ↔
      ∃ c : ℂ, f =ᵐ[reducedLaw Q] fun _ => c := by
  obtain ⟨P, hP, _, _, hfixed, _, _⟩ := id hunforced
  exact (c20_generator_annihilator_iff_kernel Q _ f).trans
    ((c20_generator_kernel_iff_fixed hP f).trans (hfixed f))

/-- Every mean-zero L² observation lies in the norm closure of the actual
unforced generator range. This uses constants in the annihilator, rather than
assuming a spectral gap or a rate of mixing. -/
theorem c20_mean_zero_mem_generator_range_closure
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q)
    (g : Lp ℂ 2 (reducedLaw Q)) (hg : (∫ ω, g ω ∂reducedLaw Q) = 0) :
    g ∈ closure {v | ∃ u,
      IsComplexGeneratorPair Q (⟨0, by omega⟩ : Fin d) 0 u v} := by
  letI := reducedLaw_probability Q
  let i : Fin d := ⟨0, by omega⟩
  let R : Submodule ℂ (Lp ℂ 2 (reducedLaw Q)) :=
    { carrier := {v | ∃ u, IsComplexGeneratorPair Q i 0 u v}
      zero_mem' := by
        refine ⟨0, ?_⟩
        simpa only [zero_smul] using (isComplexGeneratorPair_const Q i 0 1).smul 0
      add_mem' := by
        rintro v w ⟨u, hu⟩ ⟨z, hz⟩
        exact ⟨u + z, hu.add hz⟩
      smul_mem' := by
        rintro c v ⟨u, hu⟩
        exact ⟨c • u, hu.smul c⟩ }
  change g ∈ closure (R : Set (Lp ℂ 2 (reducedLaw Q)))
  rw [← Submodule.topologicalClosure_coe, ← R.orthogonal_orthogonal_eq_closure]
  apply (R.orthogonal.mem_orthogonal g).mpr
  intro f hf
  have hb (v : Lp ℂ 2 (reducedLaw Q)) :
      inner ℂ f v = ∫ ω, complexL2Conjugation (reducedLaw Q) f ω * v ω ∂reducedLaw Q := by
    simpa only [complexL2Conjugation_involutive] using
      inner_complexL2Conjugation_eq_integral_mul (reducedLaw Q)
        (complexL2Conjugation (reducedLaw Q) f) v
  obtain ⟨c, hc⟩ := (c20_unforced_generator_annihilator_constants d hd Λ r Q hunforced
    (complexL2Conjugation (reducedLaw Q) f)).mp (by
      intro u v huv
      rw [← hb]
      exact (R.mem_orthogonal' f).mp hf v ⟨u, huv⟩)
  rw [hb]
  calc
    (∫ ω, complexL2Conjugation (reducedLaw Q) f ω * g ω ∂reducedLaw Q) =
        ∫ ω, c * g ω ∂reducedLaw Q := by
      apply integral_congr_ae
      filter_upwards [hc] with ω hω
      rw [hω]
    _ = c * ∫ ω, g ω ∂reducedLaw Q := integral_const_mul c _
    _ = 0 := by rw [hg, mul_zero]

/-- The permitted stationary-environment dependency yields continuous-time
L² mean ergodicity for every mean-zero observation of the actual environment.
Almost-sure additive averages along supplied particle paths remain separate. -/
theorem c20_unforced_mean_zero_operator_averages
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q) :
    ∃ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) 0 P ∧
      ∀ g : Lp ℂ 2 (reducedLaw Q), (∫ ω, g ω ∂reducedLaw Q) = 0 →
        Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
          (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g)) atTop (𝓝 0) := by
  obtain ⟨P, hP, _, hmass, _, _, _⟩ := id hunforced
  refine ⟨P, hP, fun g hg => ?_⟩
  exact c20_generator_range_closure_average_tendsto_zero hP
    (fun t f => (hmass t f).1)
    (c20_mean_zero_mem_generator_range_closure d hd Λ r Q hunforced g hg)

/-- On the very semigroup realizing an arbitrary supplied unforced law, the
literal centered joint-law clock has a vanishing continuous-time L² average.
The realization is retained for the centered observable used in the limit. -/
theorem c20_supplied_centered_clock_operator_averages
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (hunforced : UnforcedAt hd Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0)
        0 (Y (0, ω))) :
    ∃ (μ : Lp ℂ 2 (reducedLaw Q))
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsReducedClockObservation Q μ ∧
      IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) 0 P ∧
      (centeredComplexLp Q μ =ᵐ[reducedLaw Q] fun ω =>
        (ω.2 (0 : Vec d) : ℂ) -
          Complex.ofReal (∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q)) ∧
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
        (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal (centeredComplexLp Q μ)))
          atTop (𝓝 0) ∧
      (∀ t : ℝ≥0, ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d =>
          centeredComplexLp Q μ (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
        P t (centeredComplexLp Q μ) (reduce ω) =
          ∫ γ : Path d, centeredComplexLp Q μ (translate (γ t) (reduce ω))
            ∂Y (0, ω)) := by
  obtain ⟨μ, hμ⟩ := c20_exists_clock_observation Q
  obtain ⟨P, hP, _, hmass, _, _, hrealize⟩ := id hunforced
  have hmean : (∫ ω, μ ω ∂reducedLaw Q) =
      Complex.ofReal (∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q) := by
    rw [integral_congr_ae hμ, integral_complex_ofReal]
  refine ⟨μ, P, hμ, hP, ?_, ?_, fun t => hrealize Y hY t _⟩
  · filter_upwards [coeFn_centeredComplexLp Q μ, hμ] with ω hc hm
    rw [hc, hm, hmean]
  · exact c20_generator_range_closure_average_tendsto_zero hP
      (fun t f => (hmass t f).1)
      (c20_mean_zero_mem_generator_range_closure d hd Λ r Q hunforced _
        (integral_centeredComplexLp Q μ))


/-- Integer-time convergence is equivalent to the actual continuous-time clock
speed, since the physical clock is nonnegative and monotone on every path. -/
theorem c20_clock_speed_iff_integer_event {d : ℕ}
    (ω : FieldPair d) (γ : Path d) (η : ℝ) :
    Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η ↔
      (ω, γ) ∈ Clock.clockRateNatSet η := by
  constructor
  · intro h
    exact h.comp tendsto_natCast_atTop_atTop
  · intro h
    exact Clock.tendsto_div_of_tendsto_natCast
      (fun t => NNReal.coe_nonneg (Clock.physicalPathClock ω γ t))
      (fun _ _ hst => Clock.physicalPathClock_mono (ω, γ) hst) h

/-- The full continuous-time speed event is measurable through its countable
integer-time characterization; no uniform path regularity premise is needed. -/
theorem c20_measurableSet_clock_speed {d : ℕ} (η : ℝ) :
    MeasurableSet {z : FieldPair d × Path d |
      Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed z.1 z.2 η} := by
  have heq : {z : FieldPair d × Path d |
      Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed z.1 z.2 η} =
      Clock.clockRateNatSet η := by
    ext z
    exact c20_clock_speed_iff_integer_event z.1 z.2 η
  rw [heq]
  exact Clock.measurableSet_clockRateNatSet η

/-- A measurable event of the actual annealed environment-path law holds if
and only if it holds under almost every actual quenched origin law. -/
theorem c20_annealed_event_iff_fibers {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw Y ω))
    {S : Set (FieldPair d × Path d)} (hS : MeasurableSet S) :
    (∀ᵐ z ∂Carriers.annealedCoordinateJoint Q Y hprob, z ∈ S) ↔
      ∀ᵐ ω ∂Q, ∀ᵐ γ ∂originLaw Y ω, (ω, γ) ∈ S := by
  constructor
  · intro h
    let V := Probability.ValidAnnealedLawSupport.ProbabilityFiber (originLaw Y)
    letI : IsProbabilityMeasure (Q.comap (Subtype.val : V → FieldPair d)) :=
      Probability.ValidAnnealedLawSupport.probabilityFiberBase_isProbabilityMeasure
        Q (originLaw Y) hprob
    have hm : Measurable (fun z : V × Path d => (z.1.1, z.2)) :=
      (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
    change ∀ᵐ z ∂((Q.comap (Subtype.val : V → FieldPair d)).compProd
      (Probability.ValidAnnealedLawSupport.probabilityFiberKernel (originLaw Y))).map
        (fun z => (z.1.1, z.2)), z ∈ S at h
    have hfib := Measure.ae_ae_of_ae_compProd (ae_of_ae_map hm.aemeasurable h)
    have hvalid := Probability.ValidAnnealedLawSupport.measurableSet_probabilityFiberSet
      (originLaw Y)
    have hrestr : ∀ᵐ ω ∂Q.restrict
        (Probability.ValidAnnealedLawSupport.ProbabilityFiberSet (originLaw Y)),
        ∀ᵐ γ ∂originLaw Y ω, (ω, γ) ∈ S :=
      (ae_restrict_iff_subtype hvalid).2 hfib
    filter_upwards [hprob, (ae_restrict_iff' hvalid).1 hrestr] with ω hω hs
    exact hs hω.measure_univ
  · exact Clock.ae_annealedCoordinateJoint_mem Q Y hprob hS

/-- The literal reduced-clock rate target is exactly the measurable annealed
integer-time event for the same arbitrary supplied path law. -/
theorem c20_reduced_clock_rate_iff_annealed_integer_event {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω)) (η : ℝ) :
    HasReducedClockRate Q Y η ↔
      ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q.measure Y hprob,
        z ∈ Clock.clockRateNatSet η := by
  rw [c20_annealed_event_iff_fibers Q.measure Y hprob
    (Clock.measurableSet_clockRateNatSet η)]
  exact eventually_congr (Filter.Eventually.of_forall fun ω =>
    eventually_congr (Filter.Eventually.of_forall fun γ =>
      c20_clock_speed_iff_integer_event ω γ η))

/-- For a supplied unforced martingale-problem law, the probability-fiber
condition for the annealed event comes from that very law, without an extra
assumption on its off-support fibers. -/
theorem c20_supplied_unforced_clock_event {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y (0, ω))) (η : ℝ) :
    ∃ hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω),
      HasReducedClockRate Q Y η ↔
        ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q.measure Y hprob,
          z ∈ Clock.clockRateNatSet η := by
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) :=
    hY.mono fun _ hω => hω.1
  exact ⟨hprob, c20_reduced_clock_rate_iff_annealed_integer_event Q Y hprob η⟩


/-- The exact integer-sample interpolation consumer requested by the clock
plan. Monotonicity already suffices, so the stated regularity is unused. -/
theorem c20_physical_clock_limit_of_integer_samples
    {d : ℕ} (ω : FieldPair d) (γ : Path d) (Λ : ℝ) (_hω : IsRegular Λ ω)
    (m : ℝ)
    (hNat : Tendsto (fun n : ℕ =>
      (Clock.physicalPathClock ω γ (n : ℝ≥0) : ℝ) / (n : ℝ)) atTop (𝓝 m)) :
    Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t)
      atTop (𝓝 m) :=
  (c20_clock_speed_iff_integer_event ω γ m).2 hNat

/-- Positive maximum of the first `n` additive orbit sums. This recursive
form is the deterministic input to the finite Hopf maximal inequality. -/
def c20HopfMax {α : Type*} (T : α → α) (f : α → ℝ) : ℕ → α → ℝ
  | 0, _ => 0
  | n + 1, x => max (f x + c20HopfMax T f n (T x)) 0

theorem c20HopfMax_nonneg {α : Type*} (T : α → α) (f : α → ℝ)
    (n : ℕ) (x : α) : 0 ≤ c20HopfMax T f n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

theorem c20HopfMax_le_succ {α : Type*} (T : α → α) (f : α → ℝ)
    (n : ℕ) (x : α) : c20HopfMax T f n x ≤ c20HopfMax T f (n + 1) x := by
  induction n generalizing x with
  | zero => exact c20HopfMax_nonneg T f 1 x
  | succ n ih =>
    exact max_le_max (add_le_add le_rfl (ih (T x))) le_rfl

/-- Every prefix orbit sum lies below the recursive positive maximum. -/
theorem c20_birkhoffSum_le_hopfMax {α : Type*} (T : α → α) (f : α → ℝ)
    (n k : ℕ) (hkn : k ≤ n) (x : α) :
    birkhoffSum T f k x ≤ c20HopfMax T f n x := by
  induction n generalizing k x with
  | zero =>
    have hk : k = 0 := Nat.eq_zero_of_le_zero hkn
    subst k
    exact le_rfl
  | succ n ih =>
    cases k with
    | zero => exact c20HopfMax_nonneg T f (n + 1) x
    | succ k =>
      rw [birkhoffSum_succ_apply']
      have hsum : birkhoffSum T f k (T x) ≤ c20HopfMax T f n (T x) :=
        ih k (Nat.le_of_succ_le_succ hkn) (T x)
      exact (add_le_add le_rfl hsum).trans (le_max_left _ _)

/-- The positive maximum is attained by one of the finitely many prefix sums,
including the empty sum. -/
theorem c20HopfMax_eq_birkhoffSum {α : Type*} (T : α → α) (f : α → ℝ)
    (n : ℕ) (x : α) :
    ∃ k ≤ n, c20HopfMax T f n x = birkhoffSum T f k x := by
  induction n generalizing x with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    obtain ⟨k, hk, heq⟩ := ih (T x)
    by_cases ha : 0 ≤ f x + c20HopfMax T f n (T x)
    · refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
      rw [c20HopfMax, max_eq_left ha, birkhoffSum_succ_apply', heq]
    · refine ⟨0, Nat.zero_le _, ?_⟩
      rw [c20HopfMax, max_eq_right (not_le.mp ha).le, birkhoffSum_zero_apply]

theorem c20HopfMax_pos_iff {α : Type*} (T : α → α) (f : α → ℝ)
    (n : ℕ) (x : α) :
    0 < c20HopfMax T f n x ↔ ∃ k ≤ n, 0 < birkhoffSum T f k x := by
  constructor
  · intro hx
    obtain ⟨k, hk, heq⟩ := c20HopfMax_eq_birkhoffSum T f n x
    exact ⟨k, hk, heq ▸ hx⟩
  · rintro ⟨k, hk, hx⟩
    exact hx.trans_le (c20_birkhoffSum_le_hopfMax T f n k hk x)

theorem c20HopfMax_measurable {α : Type*} [MeasurableSpace α]
    {T : α → α} {f : α → ℝ} (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (c20HopfMax T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (hf.add (ih.comp hT)).max measurable_const

theorem c20HopfMax_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (c20HopfMax T f n) μ := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih => exact (hf.add (hT.integrable_comp_of_integrable ih)).pos_part

/-- The finite Hopf inequality, proved for any measure-preserving map and
integrable measurable observable. No path-process realization is assumed here. -/
theorem c20_hopf_finite_maximal_inequality {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hmf : Measurable f) (hf : Integrable f μ)
    (n : ℕ) :
    0 ≤ ∫ x, {x | 0 < c20HopfMax T f (n + 1) x}.indicator f x ∂μ := by
  let M := c20HopfMax T f (n + 1)
  let E := {x | 0 < M x}
  have hM : Measurable M := c20HopfMax_measurable hT.measurable hmf _
  have hMi : Integrable M μ := c20HopfMax_integrable hT hf _
  have hE : MeasurableSet E := measurableSet_lt measurable_const hM
  have hcomp : Integrable (fun x => M (T x)) μ := hT.integrable_comp_of_integrable hMi
  have hpoint : ∀ x, M x ≤ E.indicator f x + M (T x) := by
    intro x
    by_cases hx : x ∈ E
    · have hx' : 0 < max (f x + c20HopfMax T f n (T x)) 0 := hx
      have ha : 0 < f x + c20HopfMax T f n (T x) :=
        (lt_max_iff.mp hx').resolve_right (lt_irrefl 0)
      rw [Set.indicator_of_mem hx]
      change max (f x + c20HopfMax T f n (T x)) 0 ≤ _
      rw [max_eq_left ha.le]
      exact add_le_add le_rfl (c20HopfMax_le_succ T f n (T x))
    · rw [Set.indicator_of_notMem hx, zero_add]
      exact (le_of_not_gt hx).trans (c20HopfMax_nonneg T f (n + 1) (T x))
  have heq : (∫ x, M (T x) ∂μ) = ∫ x, M x ∂μ := by
    calc
      _ = ∫ x, M x ∂μ.map T :=
        (integral_map hT.measurable.aemeasurable hM.aestronglyMeasurable).symm
      _ = _ := by rw [hT.map_eq]
  have hle := integral_mono hMi ((hf.indicator hE).add hcomp) hpoint
  change (∫ x, M x ∂μ) ≤ ∫ x, E.indicator f x + M (T x) ∂μ at hle
  rw [integral_add (hf.indicator hE) hcomp, heq] at hle
  change 0 ≤ ∫ x, E.indicator f x ∂μ
  linarith only [hle]

/-- The finite Hopf inequality in terms of actual Birkhoff sums. It is an
analytic consumer of a measure-preserving map, not a path-stationarity claim. -/
theorem c20_birkhoff_finite_maximal_inequality {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hmf : Measurable f) (hf : Integrable f μ)
    (n : ℕ) :
    0 ≤ ∫ x, {x | ∃ k ≤ n + 1, 0 < birkhoffSum T f k x}.indicator f x ∂μ := by
  have heq : {x | ∃ k ≤ n + 1, 0 < birkhoffSum T f k x} =
      {x | 0 < c20HopfMax T f (n + 1) x} := by
    ext x
    exact (c20HopfMax_pos_iff T f (n + 1) x).symm
  rw [heq]
  exact c20_hopf_finite_maximal_inequality hT hmf hf n


/-- Hopf's maximal inequality over all finite orbit sums. The finite events
increase, and their indicator observables are dominated by the integrable norm. -/
theorem c20_birkhoff_maximal_inequality {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hmf : Measurable f) (hf : Integrable f μ) :
    0 ≤ ∫ x, {x | ∃ k : ℕ, 0 < birkhoffSum T f k x}.indicator f x ∂μ := by
  let E : ℕ → Set α := fun n => {x | 0 < c20HopfMax T f (n + 1) x}
  let A : Set α := {x | ∃ k : ℕ, 0 < birkhoffSum T f k x}
  have hE (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_lt measurable_const (c20HopfMax_measurable hT.measurable hmf _)
  have hlim (x : α) :
      Tendsto (fun n => (E n).indicator f x) atTop (𝓝 (A.indicator f x)) := by
    by_cases hx : x ∈ A
    · obtain ⟨k, hk⟩ := hx
      have hevent : ∀ᶠ n : ℕ in atTop, (E n).indicator f x = A.indicator f x := by
        filter_upwards [eventually_ge_atTop k] with n hn
        have hen : x ∈ E n := (c20HopfMax_pos_iff T f (n + 1) x).2
          ⟨k, hn.trans (Nat.le_succ n), hk⟩
        rw [Set.indicator_of_mem hen, Set.indicator_of_mem (show x ∈ A from ⟨k, hk⟩)]
      exact tendsto_const_nhds.congr' (hevent.mono fun _ hn => hn.symm)
    · have hn (n : ℕ) : x ∉ E n := by
        intro hen
        obtain ⟨k, _, hk⟩ := (c20HopfMax_pos_iff T f (n + 1) x).1 hen
        exact hx ⟨k, hk⟩
      simpa only [Set.indicator_of_notMem hx, Set.indicator_of_notMem (hn _)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have ht : Tendsto (fun n => ∫ x, (E n).indicator f x ∂μ) atTop
      (𝓝 (∫ x, A.indicator f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    · intro n
      exact (hf.indicator (hE n)).aestronglyMeasurable
    · exact hf.norm
    · intro n
      exact Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ E n
        · simp only [Set.indicator_of_mem hx, le_refl]
        · simp only [Set.indicator_of_notMem hx, norm_zero, norm_nonneg]
    · exact Filter.Eventually.of_forall hlim
  exact ge_of_tendsto' ht fun n => c20_hopf_finite_maximal_inequality hT hmf hf n

/-- The positive maximal-orbit event is measurable for measurable data. -/
theorem c20_measurableSet_birkhoff_positive_max {α : Type*} [MeasurableSpace α]
    {T : α → α} {f : α → ℝ} (hT : Measurable T) (hf : Measurable f) :
    MeasurableSet {x | ∃ k : ℕ, 0 < birkhoffSum T f k x} := by
  have heq : {x | ∃ k : ℕ, 0 < birkhoffSum T f k x} =
      ⋃ n : ℕ, {x | 0 < c20HopfMax T f (n + 1) x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, (c20HopfMax_pos_iff T f (k + 1) x).2 ⟨k, Nat.le_succ k, hk⟩⟩
    · rintro ⟨n, hn⟩
      obtain ⟨k, _, hk⟩ := (c20HopfMax_pos_iff T f (n + 1) x).1 hn
      exact ⟨k, hk⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (c20HopfMax_measurable hT hf _)

/-- Weak maximal bound for additive orbit averages on a finite measure space.
The threshold is kept multiplied through, so the statement also covers zero. -/
theorem c20_birkhoff_maximal_measure_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hmf : Measurable f) (hf : Integrable f μ)
    (ε : ℝ) :
    ε * μ.real {x | ∃ k : ℕ, (k : ℝ) * ε < birkhoffSum T f k x} ≤
      ∫ x, ‖f x‖ ∂μ := by
  let g : α → ℝ := fun x => f x - ε
  let A : Set α := {x | ∃ k : ℕ, 0 < birkhoffSum T g k x}
  have hmg : Measurable g := hmf.sub measurable_const
  have hgi : Integrable g μ := hf.sub (integrable_const ε)
  have hA : MeasurableSet A := c20_measurableSet_birkhoff_positive_max hT.measurable hmg
  have hhopf := c20_birkhoff_maximal_inequality hT hmg hgi
  have hidentity : A.indicator g =
      A.indicator f - A.indicator (fun _ => ε) := by
    ext x
    by_cases hx : x ∈ A <;> simp [g, hx]
  change 0 ≤ ∫ x, A.indicator g x ∂μ at hhopf
  rw [hidentity] at hhopf
  change 0 ≤ ∫ x, A.indicator f x - A.indicator (fun _ => ε) x ∂μ at hhopf
  rw [integral_sub (hf.indicator hA) ((integrable_const ε).indicator hA),
    integral_indicator_const ε hA] at hhopf
  have hbound : (∫ x, A.indicator f x ∂μ) ≤ ∫ x, ‖f x‖ ∂μ := by
    apply integral_mono (hf.indicator hA) hf.norm
    intro x
    by_cases hx : x ∈ A
    · simpa only [Set.indicator_of_mem hx, Real.norm_eq_abs] using le_abs_self (f x)
    · simp only [Set.indicator_of_notMem hx, norm_nonneg]
  have heq : A = {x | ∃ k : ℕ, (k : ℝ) * ε < birkhoffSum T f k x} := by
    ext x
    change (∃ k : ℕ, 0 < birkhoffSum T g k x) ↔
      ∃ k : ℕ, (k : ℝ) * ε < birkhoffSum T f k x
    have hs (k : ℕ) : birkhoffSum T g k x = birkhoffSum T f k x - (k : ℝ) * ε := by
      simp [g, birkhoffSum, Finset.sum_sub_distrib]
    simp only [hs, sub_pos]
  rw [heq] at hhopf
  rw [heq] at hbound
  change 0 ≤ (∫ x, {x | ∃ k : ℕ, (k : ℝ) * ε < birkhoffSum T f k x}.indicator f x ∂μ) -
    μ.real {x | ∃ k : ℕ, (k : ℝ) * ε < birkhoffSum T f k x} * ε at hhopf
  linarith only [hhopf, hbound]

/-- The weak maximal estimate also controls absolute orbit averages. -/
theorem c20_birkhoff_abs_maximal_measure_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hmf : Measurable f) (hf : Integrable f μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ε * μ.real {x | ∃ k : ℕ, (k : ℝ) * ε < ‖birkhoffSum T f k x‖} ≤
      ∫ x, ‖f x‖ ∂μ := by
  have hsub : {x | ∃ k : ℕ, (k : ℝ) * ε < ‖birkhoffSum T f k x‖} ⊆
      {x | ∃ k : ℕ, (k : ℝ) * ε < birkhoffSum T (fun y => ‖f y‖) k x} := by
    rintro x ⟨k, hk⟩
    refine ⟨k, hk.trans_le ?_⟩
    exact norm_sum_le _ _
  have hm := mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hsub) hε
  have hb := c20_birkhoff_maximal_measure_bound hT hmf.norm hf.norm ε
  simp only [norm_norm] at hb
  exact hm.trans hb


/-- An integrable observable has summable linearly spaced norm tails. -/
theorem c20_tsum_norm_tail_ne_top {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ℝ)
    (hmg : Measurable g) (hg : Integrable g μ) {ε : ℝ} (hε : 0 < ε) :
    (∑' n : ℕ, μ {ω | ε * ((n : ℝ) + 1) < ‖g ω‖}) ≠ ∞ := by
  classical
  let A : ℕ → Set Ω := fun n => {ω | ε * ((n : ℝ) + 1) < ‖g ω‖}
  have hA (n : ℕ) : MeasurableSet (A n) :=
    measurableSet_lt measurable_const hmg.norm
  have hbound (ω : Ω) :
      (∑' n : ℕ, (A n).indicator (fun _ => (1 : ℝ≥0∞)) ω) ≤
        ENNReal.ofReal (‖g ω‖ / ε + 1) := by
    let N := ⌊‖g ω‖ / ε⌋₊ + 1
    have hsupport (n : ℕ) (hn : n ∉ Finset.range N) :
        (A n).indicator (fun _ => (1 : ℝ≥0∞)) ω = 0 := by
      apply Set.indicator_of_notMem
      intro hmem
      change ε * ((n : ℝ) + 1) < ‖g ω‖ at hmem
      have hsmall : (n : ℝ) + 1 < ‖g ω‖ / ε :=
        (lt_div_iff₀ hε).2 (by simpa only [mul_comm] using hmem)
      have hn' : n + 1 ≤ ⌊‖g ω‖ / ε⌋₊ :=
        Nat.le_floor (by simpa only [Nat.cast_add, Nat.cast_one] using hsmall.le)
      have hnN : N ≤ n := Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hn)
      change ⌊‖g ω‖ / ε⌋₊ + 1 ≤ n at hnN
      omega
    rw [tsum_eq_sum hsupport]
    calc
      (∑ n ∈ Finset.range N, (A n).indicator (fun _ => (1 : ℝ≥0∞)) ω) ≤
          ∑ _n ∈ Finset.range N, (1 : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro n _
        exact Set.indicator_le_self' (fun _ _ => (zero_le : (0 : ℝ≥0∞) ≤ 1)) _
      _ = (N : ℝ≥0∞) := by simp
      _ ≤ ENNReal.ofReal (‖g ω‖ / ε + 1) := by
        rw [← ENNReal.ofReal_natCast]
        apply ENNReal.ofReal_le_ofReal
        change ((⌊‖g ω‖ / ε⌋₊ + 1 : ℕ) : ℝ) ≤ ‖g ω‖ / ε + 1
        rw [Nat.cast_add, Nat.cast_one]
        exact add_le_add (Nat.floor_le (div_nonneg (norm_nonneg (g ω)) hε.le)) (le_refl 1)
  have hfinite : (∫⁻ ω, ENNReal.ofReal (‖g ω‖ / ε + 1) ∂μ) < ∞ := by
    apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun ω => by positivity))).1
    exact ((hg.norm.div_const ε).add (integrable_const 1)).hasFiniteIntegral
  have hsum : (∑' n, μ (A n)) =
      ∫⁻ ω, ∑' n : ℕ, (A n).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
    rw [lintegral_tsum (fun n => (measurable_const.indicator (hA n)).aemeasurable)]
    exact tsum_congr fun n => (lintegral_indicator_one (hA n)).symm
  change (∑' n, μ (A n)) ≠ ∞
  rw [hsum]
  exact (lt_of_le_of_lt (lintegral_mono hbound) hfinite).ne

/-- First Borel--Cantelli gives sublinear orbit growth, without independence. -/
theorem c20_measurable_integrable_orbit_div_nat_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (g : Ω → ℝ)
    (hmg : Measurable g) (hg : Integrable g μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => g ((T^[n]) ω) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  have htail (ε : ℝ) (hε : 0 < ε) :
      ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
        ‖g ((T^[n]) ω)‖ ≤ ε * ((n : ℝ) + 1) := by
    have hs : (∑' n : ℕ, μ {ω | ε * ((n : ℝ) + 1) < ‖g ((T^[n]) ω)‖}) ≠ ∞ := by
      have heq (n : ℕ) :
          μ {ω | ε * ((n : ℝ) + 1) < ‖g ((T^[n]) ω)‖} =
            μ {ω | ε * ((n : ℝ) + 1) < ‖g ω‖} :=
        (hT.iterate n).measure_preimage
          (measurableSet_lt measurable_const hmg.norm).nullMeasurableSet
      simp_rw [heq]
      exact c20_tsum_norm_tail_ne_top μ g hmg hg hε
    filter_upwards [ae_eventually_notMem hs] with ω hω
    exact hω.mono fun n hn => le_of_not_gt hn
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      ‖g ((T^[n]) ω)‖ ≤ (1 / ((k : ℝ) + 1)) * ((n : ℝ) + 1) := by
    rw [ae_all_iff]
    intro k
    exact htail _ (by positivity)
  filter_upwards [hall] with ω hω
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hω k)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right, norm_div,
    Real.norm_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)]
  exact ((div_le_iff₀ (show 0 < (n : ℝ) + 1 by positivity)).2 (hN n hn)).trans_lt hk

/-- Sublinear orbit growth for any integrable representative. -/
theorem c20_integrable_orbit_div_nat_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (g : Ω → ℝ) (hg : Integrable g μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => g ((T^[n]) ω) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  let g' := hg.aestronglyMeasurable.mk g
  have heq : g =ᵐ[μ] g' := hg.aestronglyMeasurable.ae_eq_mk
  have horbit : ∀ᵐ ω ∂μ, ∀ n : ℕ, g ((T^[n]) ω) = g' ((T^[n]) ω) := by
    rw [ae_all_iff]
    intro n
    exact (hT.iterate n).quasiMeasurePreserving.ae_eq_comp heq
  filter_upwards [c20_measurable_integrable_orbit_div_nat_ae μ T hT g'
    hg.aestronglyMeasurable.measurable_mk (hg.congr heq), horbit] with ω hω heqω
  simpa only [heqω] using hω


end EinsteinFull.Blueprint
