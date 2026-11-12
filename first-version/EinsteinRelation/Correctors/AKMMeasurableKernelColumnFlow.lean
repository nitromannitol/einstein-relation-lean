import EinsteinRelation.Correctors.AKMBoundedCanonicalFlow
import EinsteinRelation.Correctors.AKMActualPairedEnergyTrace
import EinsteinRelation.Correctors.KernelDataMeasurability
import EinsteinRelation.Correctors.SemigroupGradientFromPointwiseExistence

/-! # Canonical column flows from a coefficient-measurable scalar kernel

Source: AKM (9.2), p. 347; `paper/main.tex:787–806,850–852`.
The scalar flow is constructed by the bounded-divergence kernel formula.
Its coefficient measurability follows from that formula. The gradient is
recovered from this same scalar flow. Measurability of the supplied scalar
kernel in the coefficient remains an explicit internal construction premise.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A measurable family of E.1 scalar kernels constructs a jointly
measurable canonical coefficient-column flow and its prescribed-time
weak gradient. Bounded divergence and the initial bound follow from the
actual coefficient regularity. No measurable selection of PDE witnesses
or kernel derivative representatives is assumed.
Source: `paper/main.tex:787–806,850–852`. -/
theorem actualCoefficientLaw_canonical_column_of_measurable_kernel
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (C : ℝ → ℝ)
    (hC : ∀ α, 0 < α → α < (AKMUpperEllipticity L)⁻¹ → 0 < C α)
    (P : Coefficient d (AKMUpperEllipticity L) → ℝ → Vec d → Vec d → ℝ)
    (hPm : Measurable (fun z :
      (Coefficient d (AKMUpperEllipticity L) × (ℝ × Vec d)) × Vec d =>
        P z.1.1 z.1.2.1 z.1.2.2 z.2))
    (hP : ∀ᵐ A ∂actualCoefficientLaw Q,
      ∃ (X Y : ℝ → Vec d → Vec d → Vec d)
        (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A (P A) X Y H C) :
    ∃ (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
      (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => u z.1 z.2) ∧
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => G z.1 z.2) ∧
      ∀ᵐ A ∂actualCoefficientLaw Q,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A) ∧
        (∀ t : ℝ, 0 < t → HasWeakGradient Set.univ
          (fun x => u A (t,x)) (fun x => G A (t,x))) ∧
        ∀ t : ℝ, 0 < t → ∀ x : Vec d,
          |u A (t,x)| ≤ (d : ℝ)*akmColumnLipschitzConstant d L r₀ := by
  obtain ⟨b, hbm, hb⟩ := exists_akm_measurable_bounded_column_divergence Q
  let u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ :=
    fun A z => ∫ y, P A z.1 z.2 y*b i A y ∂volume
  have hum : Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => u z.1 z.2) :=
    measurable_kernel_data_average volume
      (p := fun A z y => P A z.1 z.2 y) hPm (hbm i)
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  have hD : 0 ≤ (d : ℝ)*akmColumnLipschitzConstant d L r₀ := by positivity
  have hpoint : ∀ᵐ A ∂actualCoefficientLaw Q,
      ∃ G : ℝ × Vec d → Vec d,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) G ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A) ∧
        ∀ t : ℝ, 0 < t → ∀ x : Vec d,
          |u A (t,x)| ≤ (d : ℝ)*akmColumnLipschitzConstant d L r₀ := by
    filter_upwards [hb, hP] with A hbA hPA
    obtain ⟨X, Y, H, hPA⟩ := hPA
    have hgb : ∀ᵐ y ∂volume, ‖(A y).mulVec (unitVector i)‖ ≤ AKMUpperEllipticity L :=
      Filter.Eventually.of_forall fun y =>
        (pi_norm_le_iff_of_nonneg hK.le).mpr fun j => by
          rw [Real.norm_eq_abs]
          exact (Regeneration.coordinate_abs_le_euclideanNorm _ j).trans
            (coefficientColumn_euclideanNorm_le hK A i y)
    have hfm : Measurable (fun y => b i A y) :=
      (hbm i).comp (measurable_const.prodMk measurable_id)
    obtain ⟨G, _, hsol, hrep, hbound⟩ :=
      akm_heatKernel_bounded_divergence_canonical_semigroup hK hC hPA (hbA i).1
        (coefficientColumn_aestronglyMeasurable A i) hfm hgb hD (hbA i).2
    exact ⟨G, hsol, hrep, hbound⟩
  obtain ⟨G, hGm, hG⟩ := exists_measurable_semigroupGradient_of_pointwise_existence
    hK (actualCoefficientLaw Q) id
      (fun A x => (A x).mulVec (unitVector i)) u hum
      (hpoint.mono fun _ h => ⟨h.choose, h.choose_spec.1⟩)
  refine ⟨u, G, hum, hGm, ?_⟩
  filter_upwards [hpoint, hG] with A hA hGA
  exact ⟨hGA.1, hA.choose_spec.2.1, hGA.2, hA.choose_spec.2.2⟩

end EinsteinRelation.Correctors
