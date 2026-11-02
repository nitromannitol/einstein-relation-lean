import EinsteinRelation.Correctors.ReferenceSpatialCutoff
import EinsteinRelation.Correctors.RescaledSpatialCutoff

/-! A uniform Euclidean cutoff for paired energy, `paper/main.tex:818–824`. -/
namespace EinsteinRelation.Correctors
open External.AKM

/-- A cutoff in `B₄R` equals one on `B₂R` and has gradient of size `D/R`,
with `D` chosen before the scale. Source: `paper/main.tex:818–824`. -/
theorem exists_paired_euclidean_spatial_cutoff (d : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 0 < R →
      ∃ χ : Vec d → ℝ,
        IsSpatialTest (originBall d (4*R)) χ ∧
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
        (∀ x ∈ originBall d (2*R), χ x = 1) ∧
        ∀ x, euclideanSq (gradient χ x) ≤ (D/R)^2 := by
  obtain ⟨χ,D,hD,hχ,hχb,hχ1,hχD⟩ := exists_nonnegative_reference_spatial_cutoff d
  exact ⟨D,hD,fun R hR => ⟨_,rescale_reference_spatial_cutoff hR hχ hχb hχ1 hχD⟩⟩

end EinsteinRelation.Correctors
