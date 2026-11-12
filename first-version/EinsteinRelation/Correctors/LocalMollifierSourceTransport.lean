import EinsteinRelation.Calculus.SourceMollifierSupport
import EinsteinRelation.Calculus.HorizontalTranslationLpGen

/-! # Agreement with the source mollifier carrier

Source: `paper/main.tex:762–764,921–925`. The coordinate mollifier used in
the local corrections is the same fixed mollifier already transported to
`SourceMollifier`, with the same scaling and center.
-/

namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport

/-- The source's normalized spatial kernel and the coordinate kernel have
identical values after Euclidean transport. Source: `paper/main.tex:762–764`. -/
theorem canonicalSourceKernel_eq_coordinateMollifier {d : ℕ} (R : ℝ)
    (y x : Vec d) :
    sourceScaledMollifierKernel (canonicalSourceMollifier d) R
      (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
        Calculus.unitMassScaledMollifier d R (x - y) := by
  simp [sourceScaledMollifierKernel, canonicalSourceMollifier,
    transportedSourceMollifierDensity, Calculus.unitMassScaledMollifier]

end EinsteinRelation.Correctors
