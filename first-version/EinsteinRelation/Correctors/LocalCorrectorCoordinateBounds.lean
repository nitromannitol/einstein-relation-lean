import EinsteinRelation.Correctors.CanonicalGradientMomentBounds
import EinsteinRelation.Correctors.CoordinateMomentProjections

/-! # Coordinate estimates for the local corrector data

Source: `paper/main.tex:1070–1082`. The genuine geometric moment estimates
of Proposition 5.3 and Lemma 5.1 supply scalar Hölder factors uniformly.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- Project the two local-corrector moment estimates onto every scalar
coordinate (`paper/main.tex:1070–1082`). -/
theorem localCorrector_coordinate_moments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {A B G r a : ℝ}
    (hB : 0 ≤ B) (hG : 0 ≤ G) (hr : 1 ≤ r)
    {φ : Ω → ℝ} {S : Ω → Mat d} {F V W : Ω → Vec d}
    (hV : Measurable V) (hW : Measurable W)
    (hφS : eLpNorm φ p μ + eLpNorm (fun ω => frobeniusNorm (S ω)) p μ ≤
      ENNReal.ofReal (A * a))
    (hFW : eLpNorm (fun ω => euclideanNorm (F ω)) p μ +
      eLpNorm (fun ω => euclideanNorm (W ω - V ω)) p μ ≤ ENNReal.ofReal (B * r⁻¹))
    (hVb : eLpNorm (fun ω => euclideanNorm (V ω)) p μ ≤ ENNReal.ofReal G) :
    eLpNorm φ p μ ≤ ENNReal.ofReal (A * a) ∧
    (∀ i j, eLpNorm (fun ω => S ω i j) p μ ≤ ENNReal.ofReal (A * a)) ∧
    (∀ i, eLpNorm (fun ω => F ω i) p μ ≤ ENNReal.ofReal (B * r⁻¹)) ∧
    (∀ i, eLpNorm (fun ω => W ω i) p μ ≤ ENNReal.ofReal (G + B)) := by
  have hφ : eLpNorm φ p μ ≤ ENNReal.ofReal (A * a) := (le_add_right le_rfl).trans hφS
  have hS : eLpNorm (fun ω => frobeniusNorm (S ω)) p μ ≤ ENNReal.ofReal (A * a) :=
    (le_add_left le_rfl).trans hφS
  have hF : eLpNorm (fun ω => euclideanNorm (F ω)) p μ ≤ ENNReal.ofReal (B * r⁻¹) :=
    (le_add_right le_rfl).trans hFW
  have hWb : eLpNorm (fun ω => euclideanNorm (W ω - V ω)) p μ ≤ ENNReal.ofReal (B * r⁻¹) :=
    (le_add_left le_rfl).trans hFW
  exact ⟨hφ, fun i j => (eLpNorm_entry_le S i j).trans hS,
    fun i => (eLpNorm_coordinate_le F i).trans hF,
    fun i => (eLpNorm_coordinate_le W i).trans
      (eLpNorm_localGradient_le_of_error hp hG hB hr hV hW hVb hWb)⟩

end EinsteinRelation.Correctors
