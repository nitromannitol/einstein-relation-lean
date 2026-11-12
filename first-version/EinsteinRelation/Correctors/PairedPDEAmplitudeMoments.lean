import EinsteinRelation.Correctors.PairedPDEBallNormalization
import Mathlib.MeasureTheory.Integral.Prod

/-! # Planar centered-amplitude moments from paired gradient energy

Source: `paper/main.tex:872–883`. The continuous representatives, their
actual weak PDEs, and the spatial centering kernel remain explicit. The
probability estimate follows from the deterministic GT bound for the same
fields. No energy-decay estimate is postulated as a literature input.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- A genuine weighted centered value is measurable for a jointly measurable
random scalar field. Source: `paper/main.tex:872–883`. -/
theorem measurable_centered_spatial_value {Ω : Type*} [MeasurableSpace Ω]
    (u : Ω → Vec 2 → ℝ) (hu : Measurable (fun z : Ω × Vec 2 => u z.1 z.2))
    {w : Vec 2 → ℝ} (hw : Measurable w) (x₀ : Vec 2) :
    Measurable (fun ω => u ω x₀ - ∫ x, w x * u ω x) := by
  apply Measurable.sub
  · exact hu.comp (measurable_id.prodMk measurable_const)
  · have hm : Measurable (fun z : Ω × Vec 2 => w z.2 * u z.1 z.2) :=
      (hw.comp measurable_snd).mul hu
    exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The normalized planar GT bound controls every probability moment of
the centered value by `C R` times the paired gradient-energy moment. The
constant is independent of the radius, law, coefficients and kernel.
Source: `paper/main.tex:872–883`. -/
theorem paired_harmonic_centered_amplitude_moments_of_gt
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (a : Ω → Vec 2 → Mat 2) (u : Ω → Vec 2 → ℝ) (G : Ω → Vec 2 → Vec 2),
        Measurable (fun z : Ω × Vec 2 => u z.1 z.2) →
        (∀ᵐ ω ∂P, EllipticBound (ball 0 (2*R)) (a ω) lam Λ ∧
          WeakSolution (ball 0 (2*R)) (a ω) (u ω) (G ω) ∧
          ContinuousOn (u ω) (ball 0 R)) →
        ∀ (w : Vec 2 → ℝ), Measurable w → Integrable w volume →
          (∀ᵐ ω ∂P, Integrable (fun x => w x * u ω x) volume) →
          (∀ x, 0 ≤ w x) → (∫ x, w x) = 1 → Function.support w ⊆ ball 0 R →
          ∀ x₀ ∈ ball 0 R, ∀ p : ℝ≥0∞,
            MemLp (fun ω => vectorRms volume (ball 0 (2*R)) (G ω)) p P →
            MemLp (fun ω => u ω x₀ - ∫ x, w x * u ω x) p P ∧
              eLpNorm (fun ω => u ω x₀ - ∫ x, w x * u ω x) p P ≤
                ENNReal.ofReal (C*R) *
                  eLpNorm (fun ω => vectorRms volume (ball 0 (2*R)) (G ω)) p P := by
  obtain ⟨C, hC, hbound⟩ := paired_harmonic_centered_amplitude_planar_of_gt h817 hP hlam hΛ
  refine ⟨C, hC, ?_⟩
  intro R hR Ω _ P a u G hum hdata w hwm hwi hwui hw0 hw1 hws x₀ hx₀ p hGp
  have hdom : ∀ᵐ ω ∂P,
      ‖u ω x₀ - ∫ x, w x * u ω x‖ ≤
        (C*R) * ‖vectorRms volume (ball 0 (2*R)) (G ω)‖ := by
    filter_upwards [hdata, hwui] with ω hω hwu
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ vectorRms volume (ball 0 (2*R)) (G ω) from Real.sqrt_nonneg _),
      mul_assoc]
      using hbound R hR (a ω) (u ω) (G ω) hω.1 hω.2.1 hω.2.2
        w hwi hwu hw0 hw1 hws x₀ hx₀
  refine ⟨hGp.of_le_mul (measurable_centered_spatial_value u hum hwm x₀).aestronglyMeasurable
    hdom, ?_⟩
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom p

end EinsteinRelation.Correctors
