import EinsteinFull.Blueprint.G3.Proofs.C6CoarseIdentification
import EinsteinFull.Calculus.C6CoarsePhysicalGaussianFlux
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Correctors EinsteinRelation.ReductionImageV3
open EinsteinRelation.Environment.AKMTestIntegralSupport
theorem coarse_gaussian_commutator_integrable :
    ∀ (_hmom : node_corrector_u2D_construction_u23_smooth_u2D_momentsStmt)
      (d : ℕ) (_hd : 2 ≤ d) (D : StructuralData d)
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ r : ℝ, D.dependenceRange ≤ r →
      ∀ (x : Vec d) (j k : Fin d),
      ∀ᵐ ω ∂reducedLaw Q, Integrable (fun z : Vec d =>
        heatKernel 0 r z * commutatorObservation Q j k (translate (x-z) ω)) := by
  intro _hmom d _hd D Q _hs r hr x j k
  exact (coarseCommutator_heatKernel_integrable_mean_zero Q j k x
    (lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange) hr)).1
end EinsteinFull.Blueprint
