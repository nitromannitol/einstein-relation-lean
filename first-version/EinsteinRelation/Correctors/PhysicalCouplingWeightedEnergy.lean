import EinsteinRelation.Correctors.AKMActualPairedEnergyTrace
import EinsteinRelation.Correctors.PhysicalCouplingLift
import EinsteinRelation.Correctors.CanonicalPairedWeightedEnergyBound

/-! # Weighted energy on physical couplings

Source: `paper/main.tex:823–848,850–852`. The bounded weak divergence of
the actual coefficient columns supplies the strong initial trace. Both
samples remain on the physical carrier, where pointwise coefficient
agreement is available without an off-image representative.
Identification of the chosen flow with the canonical kernel remains explicit.
-/

open MeasureTheory Set
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Coefficient regularity gives a strong zero local L² trace for every
canonical pair drawn with the actual marginals. No scalar divergence,
initial bound or initial convergence is assumed.
Source: `paper/main.tex:823–838,850–852`. -/
theorem physicalCoupling_paired_canonical_zero_L2_trace
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    (μ : Measure (PhysicalField d L × PhysicalField d L))
    (hfst : MeasurePreserving Prod.fst μ (physicalReferenceLaw Q))
    (hsnd : MeasurePreserving Prod.snd μ (physicalReferenceLaw Q))
    {U : Set (Vec d)} (hU : IsOpen U) [IsFiniteMeasure (volume.restrict U)]
    (hEq : ∀ᵐ A ∂μ, Set.EqOn (project (r₀ := r₀) Q.ellipticity_parameter A.1) (project (r₀ := r₀) Q.ellipticity_parameter A.2) U) :
    ∀ᵐ A ∂μ, ∃ v : ℝ → Lp ℝ 2 (volume.restrict U),
      ContinuousWithinAt v (Ici 0) 0 ∧ v 0 = 0 ∧
      (∀ t : ℝ, 0 < t → (v t : Vec d → ℝ) =ᵐ[volume.restrict U]
        fun x => u (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - u (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x)) ∧
      Filter.Tendsto (fun t => ∫ x in U, (u (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - u (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x))^2)
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  obtain ⟨b, hbm, hb⟩ := exists_akm_measurable_bounded_column_divergence Q
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  have hD : 0 ≤ (d : ℝ) * akmColumnLipschitzConstant d L r₀ := by positivity
  filter_upwards [((measurePreserving_akmProject Q).comp hfst).quasiMeasurePreserving.ae hflow,
    ((measurePreserving_akmProject Q).comp hsnd).quasiMeasurePreserving.ae hflow, ((measurePreserving_akmProject Q).comp hfst).quasiMeasurePreserving.ae hb,
    ((measurePreserving_akmProject Q).comp hsnd).quasiMeasurePreserving.ae hb, hEq] with A h₁ h₂ hb₁ hb₂ hA
  apply paired_canonicalSemigroup_exists_zero_L2_extension
    h₁.1 h₂.1 h₁.2 h₂.2 (hb₁ i).1 (hb₂ i).1
    (coefficientColumn_aestronglyMeasurable (project (r₀ := r₀) Q.ellipticity_parameter A.1) i)
    (coefficientColumn_aestronglyMeasurable (project (r₀ := r₀) Q.ellipticity_parameter A.2) i)
    (Filter.Eventually.of_forall (coefficientColumn_euclideanNorm_le hK (project (r₀ := r₀) Q.ellipticity_parameter A.1) i))
    (Filter.Eventually.of_forall (coefficientColumn_euclideanNorm_le hK (project (r₀ := r₀) Q.ellipticity_parameter A.2) i))
    ((hbm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    ((hbm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    hD hD (Filter.Eventually.of_forall (hb₁ i).2)
    (Filter.Eventually.of_forall (hb₂ i).2) hU
  intro x hx
  exact congrArg (fun M : Mat d => M.mulVec (unitVector i)) (hA hx)

/-- The literal paired weighted energy and dissipation estimate on the
actual normalized law. The only flow-identification premise describes the
same flow whose weak equation is used. Source: `paper/main.tex:823–848`. -/
theorem physicalCoupling_paired_canonical_weighted_energy_bound
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    (μ : Measure (PhysicalField d L × PhysicalField d L))
    (hfst : MeasurePreserving Prod.fst μ (physicalReferenceLaw Q))
    (hsnd : MeasurePreserving Prod.snd μ (physicalReferenceLaw Q))
    {U : Set (Vec d)} (hU : IsOpen U) (hUc : IsCompact (closure U))
    [IsFiniteMeasure (volume.restrict U)]
    (hEq : ∀ᵐ A ∂μ, Set.EqOn (project (r₀ := r₀) Q.ellipticity_parameter A.1) (project (r₀ := r₀) Q.ellipticity_parameter A.2) U)
    {T : ℝ} (hT : 0 < T) {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ)
    (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {M : ℝ} (hD : ∀ x, euclideanSq (gradient χ x) ≤ M^2)
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ A ∂μ,
      let E := fun t => ∫ x in U, χ x^(2*n) * euclideanSq (G (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - G (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x))
      let B := (4 * (n : ℝ)^2 * (AKMUpperEllipticity L)^2 * M^2) * ∫ t in (0 : ℝ)..T,
        (∫ x in U, (u (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - u (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x))^2)^((n : ℝ)⁻¹)
      IntegrableOn E (Icc 0 T) ∧
        (∀ t ∈ Ioc 0 T, (∫ x in U, χ x^(2*n) * (u (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - u (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x))^2) ≤ B^n) ∧
        (∫ t in (0 : ℝ)..T, E t) ≤ B^n := by
  obtain ⟨b, hbm, hb⟩ := exists_akm_measurable_bounded_column_divergence Q
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  have hDb : 0 ≤ (d : ℝ) * akmColumnLipschitzConstant d L r₀ := by positivity
  filter_upwards [((measurePreserving_akmProject Q).comp hfst).quasiMeasurePreserving.ae hflow,
    ((measurePreserving_akmProject Q).comp hsnd).quasiMeasurePreserving.ae hflow, ((measurePreserving_akmProject Q).comp hfst).quasiMeasurePreserving.ae hb,
    ((measurePreserving_akmProject Q).comp hsnd).quasiMeasurePreserving.ae hb, hEq] with A h₁ h₂ hb₁ hb₂ hA
  apply paired_canonicalSemigroup_weighted_energy_bound hK hT
    h₁.1 h₂.1 h₁.2 h₂.2 (hb₁ i).1 (hb₂ i).1
    (coefficientColumn_aestronglyMeasurable (project (r₀ := r₀) Q.ellipticity_parameter A.1) i)
    (coefficientColumn_aestronglyMeasurable (project (r₀ := r₀) Q.ellipticity_parameter A.2) i)
    (Filter.Eventually.of_forall (coefficientColumn_euclideanNorm_le hK (project (r₀ := r₀) Q.ellipticity_parameter A.1) i))
    (Filter.Eventually.of_forall (coefficientColumn_euclideanNorm_le hK (project (r₀ := r₀) Q.ellipticity_parameter A.2) i))
    ((hbm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    ((hbm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    hDb hDb (Filter.Eventually.of_forall (hb₁ i).2)
    (Filter.Eventually.of_forall (hb₂ i).2) hU hUc ?_ hA hχ hχb hD n hn
  intro x hx
  exact congrArg (fun M : Mat d => M.mulVec (unitVector i)) (hA hx)

end EinsteinRelation.Correctors
