import EinsteinRelation.Correctors.RootIntegralMoments
import EinsteinRelation.Correctors.PairedEnergySquareRoot

/-! # Probability estimate for the paired weighted energy

Source: `paper/main.tex:841–849`. The deterministic energy and time
Cauchy--Schwarz bounds enter sample by sample. Minkowski in probability
then gives the exact time integral of the scalar RMS moment majorant.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- The weighted energy estimate transfers to probability moments of the
integrated gradient RMS. The hypotheses `henergy` and `hcs` are the
samplewise conclusions of spatial coercivity and time Cauchy--Schwarz,
respectively. Source: `paper/main.tex:841–849`. -/
theorem paired_energy_moment_le {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ν : Measure X) [SigmaFinite ν] {p C R T : ℝ} {n : ℕ}
    (hp : 2 ≤ p) (hn : 2 ≤ n) (hC : 0 ≤ C) (hR : 0 < R) (hT : 0 ≤ T)
    (H : X → ℝ) (hHm : Measurable H) (hH : ∀ x, 0 ≤ H x)
    (hHi : Integrable (fun x => (H x)^(2/(n : ℝ))) ν)
    (a : X × Ω → ℝ) (ha : Measurable a) (han : ∀ z, 0 ≤ a z)
    (hmom : ∀ x, MemLp (fun ω => a (x,ω)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => a (x,ω)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (H x))
    (F E : Ω → ℝ) (hFm : Measurable F) (hFn : ∀ ω, 0 ≤ F ω)
    (hEn : ∀ᵐ ω ∂Q, 0 ≤ E ω)
    (henergy : ∀ᵐ ω ∂Q,
      E ω ≤ (C / R^2 * ∫ x, (a (x,ω))^(2/(n : ℝ)) ∂ν)^n)
    (hcs : ∀ᵐ ω ∂Q, (F ω)^2 ≤ T * E ω) :
    MemLp F (ENNReal.ofReal p) Q ∧
      eLpNorm F (ENNReal.ofReal p) Q ≤
        ENNReal.ofReal (Real.sqrt T * (Real.sqrt C)^n * R^(-(n : ℝ)) *
          (∫ x, (H x)^(2/(n : ℝ)) ∂ν)^((n : ℝ)/2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hq : 0 < 2/(n : ℝ) := div_pos (by norm_num) hn0
  have hq1 : 2/(n : ℝ) ≤ 1 := (div_le_one hn0).mpr (by exact_mod_cast hn)
  obtain ⟨_, hmem, hnorm⟩ := root_integral_moment_le Q ν (by linarith : 1 ≤ p)
    hq hq1 H hHm hH hHi a ha han hmom
  have he : 1 / (2/(n : ℝ)) = (n : ℝ)/2 := by field_simp
  rw [he] at hmem hnorm
  let B := Real.sqrt T * (Real.sqrt C)^n * R^(-(n : ℝ))
  have hBn : 0 ≤ B := by dsimp [B]; positivity
  have hdom : ∀ᵐ ω ∂Q, ‖F ω‖ ≤ B * ‖(∫ x, (a (x,ω))^(2/(n : ℝ)) ∂ν)^((n : ℝ)/2)‖ := by
    filter_upwards [hEn, henergy, hcs] with ω hE he hc
    have hJ : 0 ≤ ∫ x, (a (x,ω))^(2/(n : ℝ)) ∂ν :=
      integral_nonneg fun x => Real.rpow_nonneg (han (x,ω)) _
    have h := paired_energy_sqrt_bound hE hC hR hT hJ he hc
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hFn ω),
      abs_of_nonneg (Real.rpow_nonneg hJ _), B] using h
  refine ⟨hmem.of_le_mul hFm.aestronglyMeasurable hdom, ?_⟩
  calc
    eLpNorm F (ENNReal.ofReal p) Q ≤
        ENNReal.ofReal B * eLpNorm
          (fun ω => (∫ x, (a (x,ω))^(2/(n : ℝ)) ∂ν)^((n : ℝ)/2))
          (ENNReal.ofReal p) Q := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom _
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal ((∫ x, (H x)^(2/(n : ℝ)) ∂ν)^((n : ℝ)/2)) :=
      mul_le_mul_right hnorm _
    _ = _ := (ENNReal.ofReal_mul hBn).symm

end EinsteinRelation.Correctors
