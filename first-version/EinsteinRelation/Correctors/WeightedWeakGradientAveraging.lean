import EinsteinRelation.Correctors.WeakEquationAveraging

open MeasureTheory

namespace EinsteinRelation

open Correctors

private lemma HasWeakPartialDerivative.const_smul {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {f g : Vec d → ℝ} (h : HasWeakPartialDerivative U i f g) (c : ℝ) :
    HasWeakPartialDerivative U i (c • f) (c • g) := by
  refine ⟨fun x hx => (h.1 x hx).smul c, fun x hx => (h.2.1 x hx).smul c, ?_⟩
  intro φ hφ
  calc
    (∫ x in U, (c • f) x * coordinateDerivative i φ x) =
        (∫ x in U, c * (f x * coordinateDerivative i φ x)) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp [smul_eq_mul, mul_assoc]
    _ = c * (∫ x in U, f x * coordinateDerivative i φ x) := by rw [integral_const_mul]
    _ = c * (-(∫ x in U, g x * φ x)) := by rw [h.2.2 φ hφ]
    _ = -(c * (∫ x in U, g x * φ x)) := by ring
    _ = -(∫ x in U, c * (g x * φ x)) := by rw [integral_const_mul]
    _ = -(∫ x in U, (c • g) x * φ x) := by
      refine congrArg (fun t => -t) (integral_congr_ae (ae_of_all _ fun x => ?_))
      simp [smul_eq_mul, mul_assoc]

private lemma HasWeakGradient.const_smul {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ} {g : Vec d → Vec d} (h : HasWeakGradient U f g) (c : ℝ) :
    HasWeakGradient U (c • f) (c • g) := by
  intro i
  exact h i |>.const_smul c

end EinsteinRelation

namespace EinsteinRelation.Correctors

/-- Signed temporal averaging commutes with actual spatial weak gradients.
Source: `paper/main.tex:798–806`; both a mollifier and its derivative are used. -/
theorem hasWeakGradient_signed_weighted_integral {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [SFinite μ] (U : Set (Vec d))
    (ρ : Ω → ℝ) (u : Ω → Vec d → ℝ) (G : Ω → Vec d → Vec d)
    (hu : Integrable (fun z : Ω × Vec d => ρ z.1 * u z.1 z.2)
      (μ.prod (volume.restrict U)))
    (hG : ∀ j, Integrable (fun z : Ω × Vec d => ρ z.1 * G z.1 z.2 j)
      (μ.prod (volume.restrict U)))
    (hw : ∀ᵐ ω ∂μ, HasWeakGradient U (u ω) (G ω)) :
    HasWeakGradient U (fun x => ∫ ω, ρ ω * u ω x ∂μ)
      (fun x j => ∫ ω, ρ ω * G ω x j ∂μ) := by
  let u' : Ω → Vec d → ℝ := fun ω x => ρ ω * u ω x
  let G' : Ω → Vec d → Vec d := fun ω x j => ρ ω * G ω x j
  have hu' : Integrable (Function.uncurry u') (μ.prod (volume.restrict U)) := by
    simpa [u', Function.uncurry] using hu
  have hG' : ∀ j : Fin d, Integrable (fun z : Ω × Vec d => G' z.1 z.2 j) (μ.prod (volume.restrict U)) := by
    intro j
    simpa [G'] using hG j
  have hweak' : ∀ᵐ ω ∂μ, HasWeakGradient U (u' ω) (G' ω) := by
    filter_upwards [hw] with ω hω
    have := hω.const_smul (ρ ω)
    simpa [u', G', smul_eq_mul] using this
  exact hasWeakGradient_integral μ U u' G' hu' hG' hweak'

end EinsteinRelation.Correctors
