import EinsteinFull.External.AKMSublinearCorrectors
import EinsteinFull.External.Draft.AKMSublinearCorrectors
import EinsteinRelation.External.AKMSourceCorrectorIdentification

/-!
Carrier transport for the sublinear-pair proof. The source and vendor flux
correctors retain exactly the same potentials, gradients and heat selection.
The vendor scalar corrector has already proved cell-flux integrability; forgetting
that field introduces no extra hypothesis into the admitted source estimate.
-/

open MeasureTheory

namespace EinsteinFull.Calculus.C2SublinearSource
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- Retype a source flux potential over its existing vendor scalar corrector. -/
def toFluxCorrector {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} {φ : Corrector P e}
    (S : External.Source.AKM.SourceFluxCorrector φ.toSourceCorrector) :
    FluxCorrector φ where
  potential := S.potential
  grad := S.grad
  measurable_potential := S.measurable_potential
  measurable_grad := S.measurable_grad
  weak_gradient := S.weak_gradient
  locally_square_integrable := S.locally_square_integrable
  heat_selected := S.heat_selected

/-- Forget only the scalar corrector's cell-integrability field. -/
def toSourceFluxCorrector {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} {φ : Corrector P e} (S : FluxCorrector φ) :
    External.Source.AKM.SourceFluxCorrector φ.toSourceCorrector where
  potential := S.potential
  grad := S.grad
  measurable_potential := S.measurable_potential
  measurable_grad := S.measurable_grad
  weak_gradient := S.weak_gradient
  locally_square_integrable := S.locally_square_integrable
  heat_selected := S.heat_selected

/-- The admitted source estimate applies to the existing integrable vendor
correctors, with its constants, random radius and normalized norms unchanged. -/
theorem sublinearCorrectors : External.Draft.akmSublinearCorrectorsStmt := by
  intro d hd K hK
  obtain ⟨β, C, hβ, hC, h⟩ := External.akm_sublinear_correctors d hd K hK
  refine ⟨β, C, hβ, hC, ?_⟩
  intro s hs hsd
  obtain ⟨Cs, hCs, h⟩ := h s hs hsd
  refine ⟨Cs, hCs, ?_⟩
  intro P hP e he φ
  obtain ⟨hS, h⟩ := h P hP e he φ.toSourceCorrector
  refine ⟨hS.map toFluxCorrector, ?_⟩
  intro S
  exact h (toSourceFluxCorrector S)

end EinsteinFull.Calculus.C2SublinearSource
