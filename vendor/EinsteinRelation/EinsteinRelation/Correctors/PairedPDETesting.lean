import EinsteinRelation.Correctors.PairedParabolicEquation

/-! # Compact solution tests for the paired parabolic equation

Source: `paper/main.tex:812–830`. Tensor cutoffs localize a smooth
solution test in both variables. Every flux pairing below is genuinely
integrable for the existing energy-class weak equation.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- A positive spatial cutoff power and a temporal cutoff jointly give
compact support, even when the multiplied field has no bounded support.
Source: `paper/main.tex:822–830`. -/
theorem hasCompactSupport_tensor_cutoff {d : ℕ} {η : ℝ → ℝ}
    {χ : Vec d → ℝ} (hη : HasCompactSupport η) (hχ : HasCompactSupport χ)
    (k : ℕ) (hk : 0 < k) (f : ℝ × Vec d → ℝ) :
    HasCompactSupport (fun z : ℝ × Vec d => η z.1 * χ z.2 ^ k * f z) := by
  apply (hη.prod hχ).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal ?_ ((isClosed_tsupport η).prod (isClosed_tsupport χ))
  intro z hz
  have he : η z.1 ≠ 0 := by
    intro he
    exact hz (by simp only [he, zero_mul])
  have hc : χ z.2 ≠ 0 := by
    intro hc
    exact hz (by simp only [hc, zero_pow hk.ne', mul_zero, zero_mul])
  exact ⟨subset_tsupport _ he, subset_tsupport _ hc⟩

/-- A smooth compactly supported multiplier can be paired with each
coordinate of the actual weak flux. Source: `paper/main.tex:822–830`. -/
theorem parabolicSolution_flux_mul_integrable {d : ℕ} {K : ℝ}
    (hK : 0 < K) (A : Coefficient d K) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {f : ℝ × Vec d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (j : Fin d) :
    Integrable (fun z : ℝ × Vec d => ((A z.2).mulVec (G z)) j * f z)
      (volume.restrict (I ×ˢ U)) := by
  have hm : MemLp f 2 (volume.restrict (I ×ˢ U)) :=
    (hf.memLp_of_hasCompactSupport hfc).mono_measure Measure.restrict_le_self
  exact (parabolicSolution_flux_coordinate_memLp hK A hsol j).integrable_mul hm

/-- Spatial cutoff powers can be multiplied by an arbitrary smooth field
inside a flux pairing. Source: `paper/main.tex:822–830`. -/
theorem parabolicSolution_flux_tensor_integrable {d : ℕ} {K : ℝ}
    (hK : 0 < K) (A : Coefficient d K) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {η : ℝ → ℝ} {χ : Vec d → ℝ} {f : ℝ × Vec d → ℝ}
    (hη : Continuous η) (hχ : Continuous χ) (hf : Continuous f)
    (hηc : HasCompactSupport η) (hχc : HasCompactSupport χ)
    (k : ℕ) (hk : 0 < k) (j : Fin d) :
    Integrable (fun z : ℝ × Vec d => ((A z.2).mulVec (G z)) j *
      (η z.1 * χ z.2 ^ k * f z)) (volume.restrict (I ×ˢ U)) := by
  exact parabolicSolution_flux_mul_integrable hK A hsol
    (((hη.comp continuous_fst).mul ((hχ.comp continuous_snd).pow k)).mul hf)
    (hasCompactSupport_tensor_cutoff hηc hχc k hk f) j

end EinsteinRelation.Correctors
