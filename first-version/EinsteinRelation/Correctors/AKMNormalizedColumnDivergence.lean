import EinsteinRelation.Correctors.AKMCountableObservationIdentification
import EinsteinRelation.Correctors.ReducedCoefficientColumnDivergence
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Correctors.CoefficientColumnDivergenceMeasurability

/-! # Bounded initial divergence on the normalized coefficient law

Source: `paper/main.tex:787–792,850–852`. The actual AKM law is a law of
raw measurable coefficients. A continuous reconstruction transfers the
physical Lipschitz bound without claiming that raw point evaluations are
measurable. Spatial almost-everywhere equality then transfers the weak
column divergence to the literal raw coefficient.
-/

open MeasureTheory Set
open scoped NNReal

namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport

private theorem entry_lipschitz_rescale {d : ℕ} {M : ℝ≥0}
    {a : CoefficientField d} (c r : ℝ) (j k : Fin d)
    (h : LipschitzWith M (fun x => a x j k)) :
    LipschitzWith (‖c‖₊ * M * ‖r‖₊)
      (fun x => rescaleCoefficientField c r a x j k) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  change dist (c * a (r • x) j k) (c * a (r • y) j k) ≤ _
  rw [dist_eq_norm, ← mul_sub, norm_mul, ← dist_eq_norm]
  calc
    _ ≤ ‖c‖ * ((M : ℝ) * dist (r • x) (r • y)) :=
      mul_le_mul_of_nonneg_left (h.dist_le_mul _ _) (norm_nonneg _)
    _ = _ := by
      rw [dist_eq_norm, ← smul_sub, norm_smul, ← dist_eq_norm]
      simp only [NNReal.coe_mul, coe_nnnorm]
      ring

/-- The deterministic entrywise Lipschitz constant after AKM normalization
and spatial dilation. Source: `paper/main.tex:789–792,850–852`. -/
noncomputable def akmColumnLipschitzConstant (d : ℕ) (L r₀ : ℝ) : ℝ≥0 :=
  ‖ellipticityScale L‖₊ *
    ⟨Real.exp (2 * L) * (|L| + 2 * L ^ 2) * ((d : ℝ) + 1), by positivity⟩ * ‖r₀‖₊

/-- Reconstruction preserves the physical Lipschitz bound under the actual
normalized law. Source: `paper/main.tex:789–792,850–852`. -/
theorem ae_akm_reconstruction_entry_lipschitz {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d) (hR : Measurable R)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩) :
    ∀ᵐ a ∂actualCoefficientLaw Q, ∀ j k : Fin d,
      LipschitzWith (akmColumnLipschitzConstant d L r₀) (fun x => R a x j k) := by
  have hclosed : IsClosed {a : CoefficientField d | ∀ j k : Fin d,
      LipschitzWith (akmColumnLipschitzConstant d L r₀) (fun x => a x j k)} := by
    simp only [lipschitzWith_iff_dist_le_mul, Set.setOf_forall]
    refine isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_iInter fun x => isClosed_iInter fun y => ?_
    have he (z : Vec d) : Continuous (fun a : CoefficientField d => a z j k) :=
      (continuous_eval_const z).matrix_elem j k
    exact isClosed_le ((he x).dist (he y)) continuous_const
  have hmeas : MeasurableSet {a : Coefficient d (AKMUpperEllipticity L) | ∀ j k : Fin d,
      LipschitzWith (akmColumnLipschitzConstant d L r₀) (fun x => R a x j k)} :=
    hclosed.measurableSet.preimage hR
  apply (ae_map_iff (measurable_project Q.ellipticity_parameter).aemeasurable hmeas).mpr
  have hphys := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_reducedCoefficient_entry_lipschitz Q)
  filter_upwards [hphys] with ω hω
  rw [akmContinuousReconstruction_project Q.ellipticity_parameter R hReq ω]
  intro j k
  have h := entry_lipschitz_rescale (ellipticityScale L) r₀ j k (hω j k)
  simpa only [akmColumnLipschitzConstant, abs_of_nonneg (zero_le_one.trans Q.ellipticity_parameter)]
    using h

/-- A normalized coefficient column has an everywhere bounded scalar weak
divergence, defined from the continuous reconstruction. The equation is
for the actual raw column. Source: `paper/main.tex:787–792,850–852`. -/
theorem ae_akm_column_bounded_weak_divergence {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d) (hR : Measurable R)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩) :
    ∀ᵐ a ∂actualCoefficientLaw Q, ∀ i : Fin d,
      HasWeakDivergence univ (fun x => (a x).mulVec (unitVector i))
        (divergence (fun x j => R a x j i)) ∧
      ∀ x : Vec d, |divergence (fun y j => R a y j i) x| ≤
        (d : ℝ) * akmColumnLipschitzConstant d L r₀ := by
  filter_upwards [ae_akm_reconstruction_entry_lipschitz Q R hR hReq,
    ae_akm_field_eq_reconstruction Q R hR hReq] with a ha heq
  intro i
  have hdiv := hasWeakDivergence_of_coordinate_derivatives isOpen_univ
    (fun j => lipschitzWith_hasWeakPartialDerivative (ha j i) j)
  refine ⟨hasWeakDivergence_congr_ae isOpen_univ hdiv ?_ Filter.EventuallyEq.rfl,
    abs_divergence_le_of_lipschitz_components (fun j => ha j i)⟩
  rw [Measure.restrict_univ]
  filter_upwards [heq] with x hx
  ext j
  rw [hx]
  simp only [Matrix.mulVec, unitVector, dotProduct_single, mul_one]

/-- The actual normalized coefficient law has jointly measurable bounded
initial divergence data for all columns simultaneously. The deterministic
bound is independent of the law and column.
Source: `paper/main.tex:787–792,850–852`. -/
theorem exists_akm_measurable_bounded_column_divergence {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    ∃ b : Fin d → Coefficient d (AKMUpperEllipticity L) → Vec d → ℝ,
      (∀ i, Measurable (fun z : Coefficient d (AKMUpperEllipticity L) × Vec d =>
        b i z.1 z.2)) ∧
      ∀ᵐ a ∂actualCoefficientLaw Q, ∀ i : Fin d,
        HasWeakDivergence univ (fun x => (a x).mulVec (unitVector i)) (b i a) ∧
        ∀ x : Vec d, |b i a x| ≤ (d : ℝ) * akmColumnLipschitzConstant d L r₀ := by
  obtain ⟨R, hR, hReq⟩ := exists_measurable_continuous_reconstruction
    (d := d) (K := AKMUpperEllipticity L)
  refine ⟨fun i a => divergence (fun x j => R a x j i), ?_,
    ae_akm_column_bounded_weak_divergence Q R hR hReq⟩
  intro i
  exact (measurable_coefficient_column_divergence d i).comp
    ((hR.comp measurable_fst).prodMk measurable_snd)

end EinsteinRelation.Correctors
