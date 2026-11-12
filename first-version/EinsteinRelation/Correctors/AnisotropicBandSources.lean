import EinsteinRelation.Correctors.AnisotropicAverageMass
import EinsteinRelation.Correctors.KernelConvolutionBands

/-! # Telescoping sources of the anisotropic dyadic bands

Source: `paper/main.tex:1019–1025,1041–1042`. The averaging sources
cancel at the actual scales used in the global construction.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- The anisotropic sources telescope without any regularity assumption
on the scalar field (`paper/main.tex:1019–1025`). -/
theorem sum_anisotropicBand_sources {d : ℕ} (B : Vec d ≃L[ℝ] Vec d)
    (N : ℕ) (f : FieldPair d → ℝ) (ω : FieldPair d) :
    (∑ k ∈ Finset.range N,
      (horizontalMollify (anisotropicAverage B ((2 : ℝ) ^ k)) f ω -
        horizontalMollify (anisotropicAverage B (2 * (2 : ℝ) ^ k)) f ω)) =
      horizontalMollify (anisotropicAverage B 1) f ω -
        horizontalMollify (anisotropicAverage B ((2 : ℝ) ^ N)) f ω := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ, mul_comm ((2 : ℝ) ^ N) 2]
    ring

end EinsteinRelation.Correctors
