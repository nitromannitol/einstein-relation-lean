import EinsteinRelation.External.AKMEnergyDensitySources
import Homogenization.Sobolev.H1.Definitions

/-!
# Weak gradients in the Dirichlet problem

The distributional gradients in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (1.7),
agree with the weak gradients used for the Sobolev spaces of CoarseGraining.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation

/-- The two coordinate formulations of a weak gradient agree under the local
integrability required by the source formulation. -/
theorem hasWeakGradient_iff {d : ℕ} {U : Set (Vec d)}
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : LocallyIntegrableOn u U volume)
    (hg : ∀ i, LocallyIntegrableOn (fun x => g x i) U volume) :
    HasWeakGradient U u g ↔ _root_.Homogenization.HasWeakGradientOn U u g := by
  constructor
  · intro h i φ hφ hc hs
    simpa only [coordinateDerivative, unitVector, _root_.Homogenization.basisVec] using
      (h i).2.2 φ ⟨hφ, hc, hs⟩
  · intro h i
    refine ⟨hu, hg i, ?_⟩
    intro φ hφ
    simpa only [coordinateDerivative, unitVector, _root_.Homogenization.basisVec] using
      h i φ hφ.1 hφ.2.1 hφ.2.2

/-- For square-integrable functions the local integrability required by the
source weak-gradient formulation follows automatically. -/
theorem hasWeakGradient_iff_of_memLp {d : ℕ} {U : Set (Vec d)}
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U)) :
    HasWeakGradient U u g ↔ _root_.Homogenization.HasWeakGradientOn U u g := by
  apply hasWeakGradient_iff
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict (hu.locallyIntegrable one_le_two)
  · intro i
    exact locallyIntegrableOn_of_locallyIntegrable_restrict ((hg i).locallyIntegrable one_le_two)

/-- The weak gradient of a CoarseGraining Sobolev function satisfies the
source definition, including local integrability. -/
theorem h1_hasWeakGradient {d : ℕ} {U : Set (Vec d)}
    (u : _root_.Homogenization.H1Function U) :
    HasWeakGradient U u.toFun u.grad :=
  (hasWeakGradient_iff_of_memLp u.memL2 u.gradMemL2).mpr u.hasWeakGradient

/-- A source Dirichlet competitor determines a CoarseGraining Sobolev function
with the same function and gradient. -/
def sourceH01ToH1 {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (h : External.AKM.SourceH01 U u g) :
    _root_.Homogenization.H1Function U where
  toFun := u
  grad := g
  memL2 := h.1
  gradMemL2 := by
    intro i
    exact (MeasureTheory.memLp_pi_iff.mp h.2.1) i
  hasWeakGradient := by
    intro i φ hφ hc hs
    simpa only [coordinateDerivative, unitVector, _root_.Homogenization.basisVec] using
      (h.2.2.1 i).2.2 φ ⟨hφ, hc, hs⟩

end EinsteinFull.Homogenization
