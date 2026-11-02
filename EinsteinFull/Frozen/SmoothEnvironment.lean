import EinsteinFull.Frozen.EnvironmentLaw
import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothWithBounds

open MeasureTheory

namespace EinsteinFull

/-- Assumption 1.2 on the environment law, with all derivative orders on one
almost-sure event and the fixed deterministic bounds of the structural data. -/
def HasSmoothBounds {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) : Prop :=
  ∀ᵐ ω ∂Q.measure, IsSmoothWithBounds D.derivativeBound ω

end EinsteinFull
