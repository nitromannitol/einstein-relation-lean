import EinsteinRelation.Correctors.AKMSublinearWeakPotential
import EinsteinRelation.Correctors.SpatialWeakDilation
import EinsteinRelation.Correctors.SpatialLocalL2Dilation
import EinsteinRelation.Correctors.SublinearOscillationDilation

/-!
# Rescaling the actual sublinear weak potential

Source: `paper/main.tex:693-702,727-729`. The physical potential is
multiplied by `(2 r₀)⁻¹` and evaluated at `r₀ x`. Its gradient is half
the canonical gradient. Every Sobolev and sublinearity characterization
is transported on the raw coefficient law.
-/
open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport ReductionImageV3

/-- Produce the correctly normalized raw gradient and actual sublinear
weak potentials, before imposing stationarity or harmonicity. -/
theorem exists_akm_sublinear_characterized_gradient
    (hP : BallPoincareEstimate) {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ g : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d,
      Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g p.1 p.2) ∧
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        (2 : ℝ) • (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate (r₀ • y) (reduce ω.1))).ofLp) ∧
      ∀ᵐ a ∂actualCoefficientLaw Q, ∃ u : Vec d → ℝ,
        HasWeakGradient Set.univ u (g a) ∧
        (∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) ∧
          MemLp (g a) 2 (volume.restrict (ball 0 R))) ∧
        Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
          (u x - ⨍ y in ball 0 R, u y ∂volume)^2 ∂volume)) atTop (𝓝 0) := by
  obtain ⟨G, hG, hpot, hid⟩ := exists_akm_sublinear_global_weakPotential hP Q i
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  let g := fun (a : Coefficient d (AKMUpperEllipticity L)) (x : Vec d) =>
    (1 / 2 : ℝ) • (G a (r₀ • x)).ofLp
  have hg : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g p.1 p.2) :=
    (J.continuous.measurable.comp
      (hG.comp (measurable_fst.prodMk (measurable_snd.const_smul r₀)))).const_smul (1 / 2 : ℝ)
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  refine ⟨g, hg, ?_, ?_⟩
  · filter_upwards [hid] with ω hω
    have hs := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) hr.ne').ae hω
    filter_upwards [hs] with y hy
    dsimp only [g]
    rw [hy]
    ext j
    by_cases hj : j = i <;> simp [halfDirection, correctorUnitVector, unitVector,
      PiLp.add_apply, hj]
    all_goals ring
  · filter_upwards [hpot] with a ha
    obtain ⟨v, hw, hv, hsub⟩ := ha.2
    let c : ℝ := (2 * r₀)⁻¹
    have hGc (R : ℝ) (hR : 0 < R) : MemLp (fun x => (G a x).ofLp) 2
        (volume.restrict (ball 0 R)) := J.comp_memLp' (ha.1 R hR)
    have hcr : c * r₀ = 1 / 2 := by dsimp only [c]; field_simp
    refine ⟨fun x => c * v (r₀ • x), ?_, ?_, ?_⟩
    · simpa only [hcr, g] using
        hasWeakGradient_dilation v (fun x => (G a x).ofLp) hv hGc hw r₀ c hr
    · intro R hR
      exact ⟨by simpa only [smul_eq_mul] using
        memLp_two_on_euclidean_balls_dilation v hv r₀ c hr R hR,
        memLp_two_on_euclidean_balls_dilation _ hGc r₀ (1 / 2) hr R hR⟩
    · exact sublinear_oscillation_dilation v hv hsub r₀ c hr

end EinsteinRelation.Correctors
