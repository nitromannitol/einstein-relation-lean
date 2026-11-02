import EinsteinRelation.External.AKMEnergyDensitySources
import EinsteinRelation.External.AKMCorrectorOscillation

open MeasureTheory

noncomputable section
namespace EinsteinFull.External.Source.AKM
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The literal source mean cell flux. This total integral imposes no
integrability premise on the corrector. Its integrability and identification
with the homogenized flux must be derived separately. -/
def sourceMeanFlux {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)} {e : Vec d}
    (φ : SourceCorrector P e) : Vec d :=
  ∫ a, ∫ x in unitCell d, (a x).mulVec (e + φ.grad a x) ∂volume ∂P

/-- The source flux in (6.7). The spatial Gaussian Hessian annihilates the
constant centering vector. No cell integrability or expected-flux equality
is a hypothesis of this definition or the heat-selected carrier below. -/
def sourceCenteredFlux {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : SourceCorrector P e) (a : Coefficient d K) (x : Vec d) : Vec d :=
  (a x).mulVec (e + φ.grad a x) - sourceMeanFlux φ

/-- The source flux potential selected up to constants by AKM (6.7), printed
p.246. This is the existing literal heat selection, weak gradient and local
Sobolev carrier retyped over `SourceCorrector`; it assumes no quantitative
bound or derived annealed cell-flux integrability. -/
structure SourceFluxCorrector {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : SourceCorrector P e) where
  /-- The spatial matrix-valued flux potential, defined up to constants. -/
  potential : Coefficient d K → Vec d → Mat d
  /-- The weak spatial gradient of each matrix entry. -/
  grad : Coefficient d K → Fin d → Fin d → Vec d → Vec d
  measurable_potential : Measurable
    (fun p : Coefficient d K × Vec d => potential p.1 p.2)
  measurable_grad : ∀ j k, Measurable
    (fun p : Coefficient d K × Vec d => grad p.1 j k p.2)
  weak_gradient : ∀ᵐ a ∂P, ∀ j k,
    HasWeakGradient Set.univ (fun x => potential a x j k) (grad a j k)
  locally_square_integrable : ∀ᵐ a ∂P, ∀ R : ℝ, 0 < R → ∀ j k,
    MemLp (fun x => potential a x j k) 2 (volume.restrict (ball 0 R)) ∧
    MemLp (grad a j k) 2 (volume.restrict (ball 0 R))
  heat_selected : ∀ᵐ a ∂P, IsHeatSelectedFluxGradient (sourceCenteredFlux φ a) (grad a)

end EinsteinFull.External.Source.AKM
