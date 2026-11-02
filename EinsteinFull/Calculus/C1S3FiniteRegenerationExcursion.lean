import EinsteinRelation.Regeneration.FirstRegenerationFiniteness
import EinsteinRelation.Regeneration.ForcedBitGeometry

open EinsteinRelation Regeneration MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

/-- A finite first regeneration entails a prestart excursion of at least `2 * R`. -/
theorem c1_s3_excursion_of_finite_first_regeneration
    {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ)
    (hlam : 0 < lam) (hR : 0 < R) (z : CoupledSample d) (i : Fin d)
    (hfin : firstRegenerationTime Δ lam R z i ≠ ⊤) :
    ∃ t : ℝ≥0, 2 * R ≤ z.1 t i - z.1 0 i := by
  obtain ⟨m, hm⟩ := firstRegenerationTime_eq_succ_grid_of_ne_top Δ hΔ lam R z i hfin
  obtain ⟨hΓ, _, _⟩ :=
    (firstRegenerationTime_eq_iff_forcedBitTrialEvent Δ hΔ lam R z i m).mp hm
  exact ⟨(m : ℝ≥0) * Δ, (forcedBitTrialEvent_geometry Δ hΔ lam R hlam hR i m z hΓ).2⟩

end EinsteinFull.Blueprint
