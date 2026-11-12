import EinsteinRelation.Correctors.SpatialWeakDilationUniv
import EinsteinRelation.Correctors.SemigroupZeroDivergence

/-! # Physical-scale zero-based column equations

Source: `paper/main.tex:693–702,800–808`. Undo the literal coefficient
normalization and spatial dilation in the actual finite-time column
potential and flux equations. The endpoint scalar residual is retained.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The actual finite-time equations restored to physical space. The
potential carries one factor of the range, and the residual carries the
inverse range and inverse ellipticity normalization.
Source: `paper/main.tex:693–702,800–808`. -/
theorem ae_physical_column_zero_time_weak_equations
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ T : ℝ, 0 < T →
      HasWeakGradient Set.univ
        (fun x => r₀ * ∫ t in Set.Ioo 0 T,
          u (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x))
        (fun x j => ∫ t in Set.Ioo 0 T,
          G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) j) ∧
      HasWeakDivergence Set.univ
        (fun x => ((reduce ω.1).1 x).mulVec (unitVector i +
          (fun j => ∫ t in Set.Ioo 0 T,
            G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) j)))
        (fun x => ((ellipticityScale L)⁻¹*r₀⁻¹) *
          u (project (r₀ := r₀) Q.ellipticity_parameter ω) (T,r₀⁻¹ • x)) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  have hκ : ellipticityScale L ≠ 0 := (ellipticityScale_pos Q.ellipticity_parameter).ne'
  have he := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae
    (ae_actual_column_zero_time_weak_equations Q i u G hflow)
  filter_upwards [he] with ω hω
  intro T hT
  obtain ⟨hp,hf⟩ := hω T hT
  constructor
  · have hh := hasWeakGradient_univ_dilation hp r₀⁻¹ r₀ (inv_pos.mpr hr)
    simpa only [mul_inv_cancel₀ hr.ne',one_smul] using hh
  · have hh := hasWeakDivergence_dilation hf r₀⁻¹ (ellipticityScale L)⁻¹
      (inv_pos.mpr hr)
    have hA (x : Vec d) :
        (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) =
          ellipticityScale L • ((reduce ω.1).1 x) := by
      change ellipticityScale L • reducedCoefficient ω.1 (r₀ • (r₀⁻¹ • x)) = _
      rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
      rfl
    simp only [hA,Matrix.smul_mulVec,smul_smul,inv_mul_cancel₀ hκ,one_smul] at hh
    exact hh

end EinsteinRelation.Correctors
