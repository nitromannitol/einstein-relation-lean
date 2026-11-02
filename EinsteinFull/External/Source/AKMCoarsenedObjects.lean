import EinsteinRelation.External.AKMEnergyDensity

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace EinsteinFull.External.Source.AKM
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The source class A₁: whole-space weak a-harmonic H1_loc functions with
subquadratic normalized L2 growth, AKM (3.38), printed p.82. The gradient is
an actual weak spatial gradient; no finite test family replaces the class. -/
structure SubquadraticHarmonic {d : ℕ} {K : ℝ} (a : Coefficient d K) where
  /-- The actual whole-space weak harmonic potential. -/
  potential : Vec d → ℝ
  /-- Its weak spatial gradient, identified by `weak_gradient`. -/
  grad : Vec d → Vec d
  weak_gradient : HasWeakGradient Set.univ potential grad
  local_energy : ∀ R : ℝ, 0 < R →
    MemLp potential 2 (volume.restrict (ball 0 R)) ∧
    MemLp (fun x => euclideanNorm (grad x)) 2 (volume.restrict (ball 0 R))
  harmonic : HasWeakDivergence Set.univ (fun x => (a x).mulVec (grad x)) (fun _ => 0)
  growth : Tendsto
    (fun R : ℝ => R ^ (-2 : ℤ) * Real.sqrt (⨍ x in ball 0 R, |potential x| ^ 2))
    atTop (𝓝 0)

/-- The weighted variational energy (4.8), printed p.126. Its source uses a
nonnegative integrable unit-mass mask. This definition is total; source
theorems must retain those mask hypotheses. The supremum is over all of A₁. -/
def energyJ1 {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (mask : Vec d → ℝ) (p q : Vec d) : ℝ :=
  sSup {e : ℝ | ∃ w : SubquadraticHarmonic a,
    e = ∫ x, mask x * (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
      dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))}

/-- Gaussian J₁ with the source heat-kernel normalization (4.1), variance 2r². -/
def gaussianEnergyJ1 {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (z : Vec d) (r : ℝ) (p q : Vec d) : ℝ :=
  energyJ1 a (heatKernel z r) p q

/-- Matrix entries of Definition5.23, (5.62), printed p.216. A is the source
homogenized matrix, to be identified in each application. The SECOND load is
A e_j in both energies. Full bilinear polarization remains an internal proof. -/
def coarsenedCoefficient {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (A : Mat d) (z : Vec d) (r : ℝ) : Mat d := fun j k =>
  (gaussianEnergyJ1 a z r (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
    gaussianEnergyJ1 a z r (unitVector j - unitVector k) (A.mulVec (unitVector j))) / 2

/-- The actual centering operation (5.86) on a selected source localization.
Existence, locality and approximation of that localization are separate inputs. -/
def centeredLocalizedEnergy {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K))
    (Jloc : Coefficient d K → Vec d → ℝ → Vec d → Vec d → ℝ)
    (a : Coefficient d K) (z : Vec d) (r : ℝ) (p q : Vec d) : ℝ :=
  Jloc a z r p q - ∫ a', Jloc a' z r p q ∂P

/-- Literal entry normalization, without a quadraticity or homogenization axiom. -/
theorem coarsenedCoefficient_apply {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (A : Mat d) (z : Vec d) (r : ℝ) (j k : Fin d) :
    coarsenedCoefficient a A z r j k =
      (gaussianEnergyJ1 a z r (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
        gaussianEnergyJ1 a z r (unitVector j - unitVector k) (A.mulVec (unitVector j))) / 2 := rfl

end EinsteinFull.External.Source.AKM
