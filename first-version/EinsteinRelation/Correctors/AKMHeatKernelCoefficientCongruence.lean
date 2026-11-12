import EinsteinRelation.Correctors.AKMHeatKernelUniqueness
import EinsteinRelation.Environment.AKMCoefficientObservationUniqueness

/-! # Heat kernels depend only on the observed coefficient class

Source: `paper/main.tex:699–704,787–792,850`; AKM (0.11) and
Proposition E.1. The parabolic equation uses the coefficient only up to
spatial null sets. Together with scalar kernel uniqueness, this proves
that the source observations determine every positive-time kernel value.
This congruence result does not assert measurable parameter dependence.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Spatial almost-everywhere coefficient changes preserve the actual
parabolic equation and its energy class.
Source: `paper/main.tex:787–792,822–840`. -/
theorem parabolicSolution_congr_coefficient_ae
    {d : ℕ} {K : ℝ} {A B : Coefficient d K}
    (hAB : A.field =ᵐ[volume] B.field)
    {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G) :
    IsParabolicSolution B I U u G := by
  have hprod : (fun z : ℝ × Vec d => A z.2) =ᵐ[volume]
      (fun z => B z.2) := by
    simpa only [← Measure.volume_eq_prod] using
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (Vec d)))).ae hAB
  refine ⟨hsol.1, hsol.2.1, hsol.2.2.1, hsol.2.2.2.1, ?_⟩
  intro ψ hψ hψc hψs
  calc
    _ = ∫ z in I ×ˢ U, -(u z) * fderiv ℝ ψ z (1, 0) +
        dot ((A z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hprod] with z hz
      rw [hz]
    _ = 0 := hsol.2.2.2.2 ψ hψ hψc hψs

/-- The point-mass initial trace is independent of coefficient values on
spatial null sets. Source: `paper/main.tex:787–792`; AKM (E.1)–(E.3). -/
theorem fundamentalSolution_congr_coefficient_ae
    {d : ℕ} {K : ℝ} {A B : Coefficient d K}
    (hAB : A.field =ᵐ[volume] B.field)
    {y : Vec d} {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsFundamentalSolution A y u G) :
    IsFundamentalSolution B y u G :=
  ⟨fun a b R ha hab hR =>
    parabolicSolution_congr_coefficient_ae hAB (hsol.1 a b R ha hab hR), hsol.2⟩

/-- All E.1 properties survive changes of the coefficient on a spatial
null set. Source: `paper/main.tex:787–792,850`; AKM Proposition E.1. -/
theorem heatKernelProperties_congr_coefficient_ae
    {d : ℕ} {K : ℝ} {A B : Coefficient d K}
    (hAB : A.field =ᵐ[volume] B.field)
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C) :
    HeatKernelProperties B P X Y H C := by
  rcases hP with ⟨hc,hpos,hX,hY,hsym,hmass,hmixed,hbound,htrace⟩
  exact ⟨hc,hpos,fun y => fundamentalSolution_congr_coefficient_ae hAB (hX y),
    fun x => fundamentalSolution_congr_coefficient_ae hAB (hY x),
    hsym,hmass,hmixed,hbound,htrace⟩

/-- Equal source test-integral observations determine the same scalar
kernel at every positive time. No coefficient point evaluation or choice
of a measurable kernel family is assumed.
Source: `paper/main.tex:699–704,787–792,850`; AKM (0.11), Proposition E.1. -/
theorem akm_heatKernel_eq_of_testIntegral_eq
    {d : ℕ} {K : ℝ} (hK : 0 < K) {A B : Coefficient d K}
    (hAB : ∀ (ψ : SmoothCompactTest d) (i j : Fin d),
      testIntegral A ψ i j = testIntegral B ψ i j)
    {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties B Q X₂ Y₂ H₂ C₂) :
    ∀ t : ℝ, 0 < t → ∀ x y : Vec d, P t x y = Q t x y := by
  have hfield := coefficient_field_ae_eq_of_testIntegral_eq A B hAB
  exact akm_heatKernel_unique hK (heatKernelProperties_congr_coefficient_ae hfield hP) hQ

end EinsteinRelation.Correctors
