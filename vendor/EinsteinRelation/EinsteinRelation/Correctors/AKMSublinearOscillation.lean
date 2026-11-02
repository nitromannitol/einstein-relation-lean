import EinsteinRelation.External.GilbargTrudinger

/-!
# Vanishing oscillation for sublinear harmonic functions

Source: `paper/main.tex:693-698,727-729`. AKM Theorem 3.3, (3.17),
p. 75, implies that every admissible fixed-scale oscillation of a
sublinear harmonic function vanishes. This implication does not assert
existence of an AKM corrector or identify its coefficient carrier.
-/

open MeasureTheory Filter Topology

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- On the common AKM event, sublinearity annihilates every large-scale
mean-square oscillation. The threshold is shared by all weak solutions. -/
theorem ae_sublinear_harmonic_zero_oscillation
    (h33 : LargeScaleOscillationEstimate) (d : ℕ) (hd : 2 ≤ d)
    (K : ℝ) (hK : 1 < K) (P : Measure (Coefficient d K)) (hP : LawHypotheses P) :
    ∀ᵐ a ∂P, ∃ X : ℝ, 1 ≤ X ∧
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
        (∀ R : ℝ, 0 < R →
          External.GilbargTrudinger.WeakSolution (ball 0 R) a.field u g) →
        Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
          (u x - ⨍ y in ball 0 R, u y ∂volume) ^ 2 ∂volume)) atTop (𝓝 0) →
        ∀ r : ℝ, X ≤ r →
          (⨍ x in ball 0 r,
            (u x - ⨍ y in ball 0 r, u y ∂volume) ^ 2 ∂volume) = 0 := by
  obtain ⟨C, _, hC⟩ := h33 d hd K hK
  filter_upwards [hC P hP] with a ha
  obtain ⟨X, hX, hscale⟩ := ha
  refine ⟨X, hX, ?_⟩
  intro u g hweak hsub r hr
  have hrpos : 0 < r := zero_lt_one.trans_le (hX.trans hr)
  have hle : r⁻¹ * Real.sqrt (⨍ x in ball 0 r,
      (u x - ⨍ y in ball 0 r, u y ∂volume) ^ 2 ∂volume) ≤ 0 := by
    apply ge_of_tendsto (by simpa only [mul_zero] using hsub.const_mul C)
    filter_upwards [eventually_ge_atTop X, eventually_ge_atTop r] with R hXR hrR
    have hw := hweak R (zero_lt_one.trans_le (hX.trans hXR))
    simpa only [mul_assoc] using hscale R hXR u g hw.1 hw.2.1 hw.2.2.1 hw.2.2.2 r hr hrR
  have hz : Real.sqrt (⨍ x in ball 0 r,
      (u x - ⨍ y in ball 0 r, u y ∂volume) ^ 2 ∂volume) = 0 := by
    have hn := Real.sqrt_nonneg (⨍ x in ball 0 r,
      (u x - ⨍ y in ball 0 r, u y ∂volume) ^ 2 ∂volume)
    exact le_antisymm (nonpos_of_mul_nonpos_right hle (inv_pos.mpr hrpos)) hn
  apply (Real.sqrt_eq_zero ?_).mp hz
  exact integral_nonneg fun _ => sq_nonneg _

end EinsteinRelation.Correctors
