import EinsteinRelation.Correctors.AKMNormalizedColumnDivergence
import EinsteinRelation.Correctors.AKMCanonicalFlowWeightedEnergy
import EinsteinRelation.Correctors.AKMInitialFluxObservation
import EinsteinRelation.Correctors.AKMLocalCorrectorSpecialization

/-! # Paired initial energy on the actual normalized law

Source: `paper/main.tex:817–850`. The physical coefficient regularity supplies
all bounded-divergence initial data. A specified canonical pair therefore
has continuous weighted energy through zero on any coefficient-agreement
domain. Selection and identification of that canonical flow remain separate
internal obligations.
-/

open MeasureTheory Set
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Raw coefficient columns are strongly measurable in space despite the
coefficient carrier observing them only through test integrals.
Source: `paper/main.tex:787–792`. -/
theorem coefficientColumn_aestronglyMeasurable {d : ℕ} {K : ℝ}
    (A : Coefficient d K) (i : Fin d) :
    AEStronglyMeasurable (fun x => (A x).mulVec (unitVector i)) volume := by
  have hcol : AEStronglyMeasurable (fun x j => A x j i) volume :=
    (aemeasurable_pi_lambda _ fun j =>
      (A.locally_integrable j i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  simpa only [unitVector, Matrix.mulVec_single_one, Matrix.col] using hcol

/-- The actual Euclidean column bound has no dimension loss.
Source: `paper/main.tex:194–207,787–792`. -/
theorem coefficientColumn_euclideanNorm_le {d : ℕ} {K : ℝ} (hK : 0 < K)
    (A : Coefficient d K) (i : Fin d) (x : Vec d) :
    euclideanNorm ((A x).mulVec (unitVector i)) ≤ K := by
  have h := mulVec_euclideanNorm_le_of_quadratic (A x) hK (A.symmetric x)
    (fun ξ => (euclideanSq_nonneg_coords ξ).trans (A.elliptic x ξ).1)
    (fun ξ => (A.elliptic x ξ).2) (unitVector i)
  simpa only [euclideanNorm_unitVector_eq_one, mul_one] using h

/-- Physical regularity bounds the specified canonical column flow at every
positive time, including the initial time layer. No small-time estimate is
assumed. Source: `paper/main.tex:850–852`. -/
theorem ae_actualCoefficientLaw_canonical_column_bound
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) :
    ∀ᵐ A ∂actualCoefficientLaw Q, ∀ t : ℝ, 0 < t → ∀ x : Vec d,
      |u A (t,x)| ≤ (d : ℝ) * akmColumnLipschitzConstant d L r₀ := by
  obtain ⟨b, hbm, hb⟩ := exists_akm_measurable_bounded_column_divergence Q
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  filter_upwards [hflow, hb] with A hA hbA
  obtain ⟨P, hP, hrep, _⟩ := akm_canonical_kernel_package_of_bounded_divergence
    hA.1 hA.2 (hbA i).1 (coefficientColumn_aestronglyMeasurable A i)
    (Filter.Eventually.of_forall (coefficientColumn_euclideanNorm_le hK A i))
    ((hbm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (hbA i).2)
  intro t ht x
  rw [hrep t ht x]
  obtain ⟨hi, hp, hm⟩ := hP t ht x
  exact (paired_kernel_average_bound hi hp hm
    ((hbm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (hbA i).2)).2

/-- Every coupling of the actual normalized law inherits the continuous
zero-initial weighted energy of a specified canonical column flow. The
initial divergence and its bound are conclusions of coefficient regularity,
not premises. Source: `paper/main.tex:817–850`. -/
theorem actualCoefficientLaw_paired_canonical_continuous_weighted_energy
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    (μ : Measure (Coefficient d (AKMUpperEllipticity L) ×
      Coefficient d (AKMUpperEllipticity L)))
    (hfst : MeasurePreserving Prod.fst μ (actualCoefficientLaw Q))
    (hsnd : MeasurePreserving Prod.snd μ (actualCoefficientLaw Q))
    {U : Set (Vec d)} (hU : IsOpen U) (hUc : IsCompact (closure U))
    [IsFiniteMeasure (volume.restrict U)]
    (hEq : ∀ᵐ A ∂μ, Set.EqOn A.1 A.2 U)
    {χ : Vec d → ℝ} (hχ : MemLp χ ∞ (volume.restrict U)) :
    ∀ᵐ A ∂μ, ∃ F : ℝ → ℝ,
      ContinuousOn F (Ici 0) ∧ F 0 = 0 ∧ (∀ t, 0 ≤ F t) ∧
        ∀ t : ℝ, 0 < t →
          F t = ∫ x in U, χ x^2 * (u A.1 (t,x) - u A.2 (t,x))^2 := by
  obtain ⟨b, hbm, hb⟩ := exists_akm_measurable_bounded_column_divergence Q
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  have hD : 0 ≤ (d : ℝ) * akmColumnLipschitzConstant d L r₀ := by positivity
  filter_upwards [hfst.quasiMeasurePreserving.ae hflow,
    hsnd.quasiMeasurePreserving.ae hflow, hfst.quasiMeasurePreserving.ae hb,
    hsnd.quasiMeasurePreserving.ae hb, hEq] with A h₁ h₂ hb₁ hb₂ hA
  apply paired_canonicalSemigroup_continuous_weighted_energy
    h₁.1 h₂.1 h₁.2 h₂.2 (hb₁ i).1 (hb₂ i).1
    (coefficientColumn_aestronglyMeasurable A.1 i)
    (coefficientColumn_aestronglyMeasurable A.2 i)
    (Filter.Eventually.of_forall (coefficientColumn_euclideanNorm_le hK A.1 i))
    (Filter.Eventually.of_forall (coefficientColumn_euclideanNorm_le hK A.2 i))
    ((hbm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    ((hbm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    hD hD (Filter.Eventually.of_forall (hb₁ i).2)
    (Filter.Eventually.of_forall (hb₂ i).2) hU hUc ?_ hχ
  intro x hx
  exact congrArg (fun M : Mat d => M.mulVec (unitVector i)) (hA hx)

end EinsteinRelation.Correctors
