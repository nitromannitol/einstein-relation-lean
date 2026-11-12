import Mathlib.MeasureTheory.Integral.Average
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.Weak
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.HeatSmoothing
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.AKMTestIntegralSupport

/-! Restated from the library module `EinsteinRelation.External.AKMEnergyDensity`:
the declarations of that module that the statement of
`EinsteinRelationAudit.MobilityRate.mobility_rate` depends on, in their module context. -/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.External.AKM
open Environment.AKMTestIntegralSupport
/-- The open Euclidean ball in the coordinate carrier. -/
def ball {d : ℕ} (x : Vec d) (r : ℝ) : Set (Vec d) :=
  {y | euclideanNorm (y - x) < r}
/-- The centered unit cell; its boundary has Lebesgue measure zero. -/
def unitCell (d : ℕ) : Set (Vec d) := Set.pi Set.univ (fun _ => Set.Ico (-1 / 2) (1 / 2))
/-- AKM (0.10)--(0.11), pp. xvii--xviii. Normalized symmetric ellipticity
(0.6) is built into `Coefficient`; no full real-translation stationarity is assumed. -/
def LawHypotheses {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K)) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P) ∧
  AKMFiniteRange P
/-- A spatial first-order corrector in direction `e`, characterized as in AKM
Section 3.4. The sublinearity uses the normalized L² oscillation. The last
integrability condition makes the expected unit-cell flux an ordinary integral;
it holds for AKM's correctors, but is not an estimate such as (4.4). -/
structure Corrector {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K)) (e : Vec d) where
  potential : Coefficient d K → Vec d → ℝ
  grad : Coefficient d K → Vec d → Vec d
  measurable_grad : Measurable (fun p : Coefficient d K × Vec d => grad p.1 p.2)
  weak_gradient : ∀ᵐ a ∂P, HasWeakGradient Set.univ (potential a) (grad a)
  locally_square_integrable : ∀ᵐ a ∂P, ∀ R : ℝ, 0 < R →
    MemLp (potential a) 2 (volume.restrict (ball 0 R)) ∧
    MemLp (grad a) 2 (volume.restrict (ball 0 R))
  stationary : ∀ z : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
    grad a (x + latticeShift z) = grad (translateCoefficient (latticeShift z) a) x
  harmonic : ∀ᵐ a ∂P,
    HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + grad a x)) (fun _ => 0)
  sublinear : ∀ᵐ a ∂P, Filter.Tendsto
    (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (potential a x - ⨍ y in ball 0 R, potential a y ∂volume) ^ 2 ∂volume))
    Filter.atTop (nhds 0)
  cell_integrable : Integrable
    (fun a => ∫ x in unitCell d, (a x).mulVec (e + grad a x) ∂volume) P
/-- AKM's homogenized flux `ā e`, expressed by the expected unit-cell flux. -/
def meanFlux {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)} {e : Vec d}
    (φ : Corrector P e) : Vec d :=
  ∫ a, ∫ x in unitCell d, (a x).mulVec (e + φ.grad a x) ∂volume ∂P
/-- AKM's kernel `Φ_{x,r}(y) = Φ(r²,y-x)`, (4.1), p. 124.
It is the kernel of `exp(t Δ)`, with variance `2t` in each coordinate. -/
def heatKernel {d : ℕ} (x : Vec d) (r : ℝ) (y : Vec d) : ℝ :=
  Correctors.euclideanHeatKernel (r ^ 2) (y - x)
/-- AKM Appendix A, (A.1)--(A.2), p. 455. Positivity of `s, θ` is explicit;
`X₊ = max X 0`. This notation itself supplies no stochastic estimate. -/
def OsBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (s θ : ℝ) : Prop :=
  Measurable X ∧ 0 < s ∧ 0 < θ ∧
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P) ≤ 2
end EinsteinRelation.External.AKM
