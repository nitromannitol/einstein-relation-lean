import EinsteinRelation.Correctors.CanonicalColumnStationaryLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Spatial subsequences of the actual canonical column approximation

Source: `paper/main.tex:800–808,842–849`. Strong stationary L2 convergence
has an almost-sure subsequence along spatial orbits. Its realization uses
the same zero-based actual column integrals, with the physical range scale.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- A stationary L2 limit admits one subsequence converging along almost
every actual physical spatial orbit. Source: `paper/main.tex:800–808`. -/
theorem exists_subseq_ae_physical_orbit_tendsto
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (Y : ℕ → Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (Z : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (hY : Tendsto Y atTop (𝓝 Z)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        Tendsto (fun n => Y (s n) (translate (r₀ • x) (reduce ω.1))) atTop
          (𝓝 (Z (translate (r₀ • x) (reduce ω.1)))) := by
  obtain ⟨s,hs,hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hY).exists_seq_tendsto_ae
  have hsp := ae_ae_translate_of_ae _ (reducedEnvironmentLaw_stationary Q) hpoint
  have hphys := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae hsp
  refine ⟨s,hs,?_⟩
  filter_upwards [hphys] with ω hω
  exact (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (zero_lt_one.trans_le Q.range_parameter).ne').ae hω

/-- The actual column integrals have a spatial almost-sure subsequence
converging to the canonical stationary gradient. No spatial identification
is assumed. Source: `paper/main.tex:800–808,842–849`. -/
theorem exists_actual_column_subseq_canonical_gradient
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (d : ℕ) (hd : 2 ≤ d) (L r₀ : ℝ) (hL : 1 ≤ L)
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hu : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => u p.1 p.2))
    (hG : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G p.1 p.2))
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    (hweak : ∀ᵐ A ∂actualCoefficientLaw Q, ∀ t : ℝ, 0 < t →
      HasWeakGradient Set.univ (fun x => u A (t,x)) (fun x => G A (t,x))) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        Tendsto (fun n => WithLp.toLp 2 (fun j => ∫ t in Set.Ioo 0 ((s n : ℝ)+1),
          G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,x) j)) atTop
          (𝓝 ((canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate (r₀ • x) (reduce ω.1)))) := by
  obtain ⟨v,Y,f,_,he,_,hY⟩ := exists_canonical_column_stationary_approximation
    hdecay hreg d hd L r₀ hL Q i u G hu hG hflow hweak
  obtain ⟨s,hs,hsp⟩ := exists_subseq_ae_physical_orbit_tendsto Q Y _ hY
  refine ⟨s,hs,?_⟩
  have he' := ae_all_iff.mpr fun n => (he (s n)).mono fun ω hω =>
    (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
      (zero_lt_one.trans_le Q.range_parameter).ne').ae hω
  filter_upwards [hsp,he'] with ω hω heω
  filter_upwards [hω,ae_all_iff.mpr heω] with x hx hex
  apply hx.congr
  intro n
  apply WithLp.ofLp_injective
  simpa only [WithLp.ofLp_toLp,smul_smul,
    inv_mul_cancel₀ (zero_lt_one.trans_le Q.range_parameter).ne',one_smul] using (hex n).2.1

end EinsteinRelation.Correctors
