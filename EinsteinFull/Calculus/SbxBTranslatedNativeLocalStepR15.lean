import EinsteinFull.Calculus.SbxBActualContinuousDensityExtensionR14
import EinsteinFull.Calculus.SbxBFullDurationNativeLowerClosureR15
import EinsteinFull.Calculus.SbxBContinuousRhoNativeCertificateClosureR15
import EinsteinFull.Calculus.SbxBTranslatedPhysicalCoefficientsR13

open EinsteinRelation MeasureTheory
open EinsteinRelation.Regeneration EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat

namespace EinsteinFull.Calculus

/-- Uniform local endpoint-density lower bound for the actual coefficients,
expressed in coordinates translated to the center of the killed ball. -/
theorem b_translated_actual_native_local_step_r15
    (d : ℕ) (hd : 2 ≤ d) (Λ l T : ℝ)
    (hΛ : 1 ≤ Λ) (hl : 0 < l) (hT : 0 < T) :
    ∃ κ a : ℝ, 0 < κ ∧ 0 < a ∧ ∀ (R lam : ℝ), 0 < R → lam ≠ 0 →
    l = |lam| * R → ∀ (center : Vec d) (ω : FieldPair d), IsRegular Λ ω →
    ∃ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α ∧ Continuous ρ ∧ Continuous α ∧
      (∀ z ∈ sourceBall center (6*R),
        ρ z = s4PhysicalRho hd ω lam z / physicalForceWeight hd lam center ∧
        α z = (physicalForceWeight hd lam center)⁻¹ • s4PhysicalAlpha hd ω lam z) ∧
      ∃ (s : DirichletSpectralResolution (fun z => ρ (center+z))
          (fun z => α (center+z)) R)
        (G : ℝ → Vec d → Vec d → Vec d),
        IsSpectralDirichletFundamentalSolution (fun z => ρ (center+z))
          (fun z => α (center+z)) R (bNativeSpectralKernelR13 s) G ∧
        (∀ z ∈ sourceBall 0 R,
          ρ (center+z) = s4PhysicalRho hd (translate center ω) lam z ∧
          α (center+z) = s4PhysicalAlpha hd (translate center ω) lam z) ∧
        ∀ x ∈ sourceBall 0 (l/2), ∀ y ∈ sourceBall 0 (l/2),
          a ≤ (|lam|⁻¹)^d *
            bNativeSpectralKernelR13 s (T/lam^2) (|lam|⁻¹ • x) (|lam|⁻¹ • y) /
              ρ (center + |lam|⁻¹ • y) ∧
          a ≤ (|lam|⁻¹)^d *
            ((ρ (center + |lam|⁻¹ • x) / ρ (center + |lam|⁻¹ • y)) *
              bNativeSpectralKernelR13 s (T/lam^2) (|lam|⁻¹ • x) (|lam|⁻¹ • y)) := by
  obtain ⟨κ, hκ, hκ1, hext⟩ := b_actual_continuous_coefficient_extension hd Λ l hΛ hl
  obtain ⟨c, hc, hlower⟩ := b_full_duration_native_lower_closure_r15 d hd κ l T hκ hl hT
  refine ⟨κ, κ*c, hκ, mul_pos hκ hc, ?_⟩
  intro R lam hR hlam hscale center ω hω
  obtain ⟨ρ, α, hell, hρ, hα, hcoeff⟩ := hext R lam hR hscale center ω hω
  let ρ' : Vec d → ℝ := fun z => ρ (center+z)
  let α' : Vec d → Mat d := fun z => α (center+z)
  have hshift : Continuous (fun z : Vec d => center+z) := continuous_const.add continuous_id
  have hell' : IsUniformlyElliptic κ ρ' α' :=
    ⟨hell.1.comp hshift.measurable, hell.2.1.comp hshift.measurable, fun z => hell.2.2 _⟩
  have hρ' : Continuous ρ' := hρ.comp hshift
  obtain ⟨s, G, hcert⟩ :=
    EinsteinFull.b_continuous_rho_native_certificate_of_ellipticity_r15 hd hκ hR hell' hρ'
  refine ⟨ρ, α, hell, hρ, hα, hcoeff, s, G, hcert, ?_, ?_⟩
  · intro z hz
    have hz' : center + z ∈ sourceBall center (6*R) := by
      change euclideanNorm (center + z - center) < 6*R
      have hz'' : euclideanNorm z < R := by simpa [sourceBall] using hz
      have heq : center + z - center = z := by abel
      rw [heq]
      linarith
    obtain ⟨hρeq, hαeq⟩ := hcoeff (center+z) hz'
    have hw : physicalForceWeight hd lam center ≠ 0 :=
      ne_of_gt (physicalForceWeight_pos hd lam center)
    constructor
    · rw [hρeq, b_translated_physical_rho]
      field_simp
    · rw [hαeq, b_translated_physical_alpha, smul_smul, inv_mul_cancel₀ hw, one_smul]
  intro x hx y hy
  have habs : 0 < |lam| := abs_pos.mpr hlam
  have hbnd := (hlower R |lam| hR habs hscale ρ' α' hell' hρ' s x hx y hy).1
  constructor
  · have hca : κ*c ≤ c := by nlinarith
    have hnative := hca.trans hbnd
    simpa only [sq_abs] using hnative
  have hm := mul_le_mul (hell'.2.2 (|lam|⁻¹ • x)).1 hbnd hc.le
    (hκ.le.trans (hell'.2.2 (|lam|⁻¹ • x)).1)
  calc
    κ*c ≤ ρ' (|lam|⁻¹ • x) * ((|lam|⁻¹)^d *
        bNativeSpectralKernelR13 s (T/|lam|^2) (|lam|⁻¹ • x) (|lam|⁻¹ • y) /
          ρ' (|lam|⁻¹ • y)) := hm
    _ = (|lam|⁻¹)^d *
        ((ρ (center + |lam|⁻¹ • x) / ρ (center + |lam|⁻¹ • y)) *
          bNativeSpectralKernelR13 s (T/lam^2) (|lam|⁻¹ • x) (|lam|⁻¹ • y)) := by
      rw [sq_abs]
      dsimp [ρ']
      ring

#print axioms b_translated_actual_native_local_step_r15

end EinsteinFull.Calculus
