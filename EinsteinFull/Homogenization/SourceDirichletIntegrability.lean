import EinsteinFull.Homogenization.CoefficientEllipticity
import EinsteinFull.Homogenization.SourceDirichletSobolev
import Homogenization.Sobolev.PotentialSolenoidalL2

/-!
# Integrability of Dirichlet energies

The Dirichlet integrands in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (1.7),
are integrable for zero-boundary Sobolev competitors on finite-volume domains.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The energy density of an affine loading plus an L² gradient is integrable
on every measurable finite-volume domain. -/
theorem integrableOn_sourceDirichletDensity {d : ℕ} {K : ℝ}
    (a : Coefficient d K) {U : Set (Vec d)} (hU : MeasurableSet U)
    [IsFiniteMeasure (_root_.Homogenization.volumeMeasureOn U)]
    (e : Vec d) {g : Vec d → Vec d}
    (hg : _root_.Homogenization.MemVectorL2 U g) :
    IntegrableOn (fun x => (1 / 2 : ℝ) * dot (e + g x)
      ((a x).mulVec (e + g x))) U := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hk' : K ≤ (k : ℝ) + 1 := by linarith
  have hEll := regularCoefficient_aeeQuantitativeEllipticSlice U hU k hk' a
  have hf : _root_.Homogenization.MemVectorL2 U (fun x => e + g x) := by
    exact (memLp_const e).add hg
  have hAg := hEll.memVectorL2_matVecMul hf
  have hint := (_root_.Homogenization.integrableOn_vecDot_of_memVectorL2 hf hAg).const_mul
    (1 / 2 : ℝ)
  apply hint.congr
  filter_upwards [ae_restrict_of_ae (regularCoefficient_ae_eq a)] with x hx
  change (1 / 2 : ℝ) * dot (e + g x)
      (((regularCoefficient a).toFun x).mulVec (e + g x)) = _
  rw [hx]

/-- Every source zero-boundary Sobolev competitor has an integrable
Dirichlet energy density. -/
theorem integrableOn_sourceDirichletDensity_of_sourceH01 {d : ℕ} {K : ℝ}
    (a : Coefficient d K) {U : Set (Vec d)} (hU : MeasurableSet U)
    [IsFiniteMeasure (_root_.Homogenization.volumeMeasureOn U)]
    (e : Vec d) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hg : External.AKM.SourceH01 U u g) :
    IntegrableOn (fun x => (1 / 2 : ℝ) * dot (e + g x)
      ((a x).mulVec (e + g x))) U :=
  integrableOn_sourceDirichletDensity a hU e hg.2.1

end EinsteinFull.Homogenization
