import EinsteinRelation.External.AKMEnergyDensity
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Separate AKM energy and mean-flux source statements

Application: `paper/main.tex:693-698,727-729`. References are to AKM,
*Quantitative Stochastic Homogenization and Large-Scale Regularity* (2019).
The source corrector is a stationary potential field as in Definitions
3.14--3.15 and Lemma 3.16, printed pp. 98--100. The matrix is characterized
by Definition 1.2 and (1.22), printed p. 11, using the Dirichlet minimum
(1.7), printed p. 5. Neither object is defined using a flux identity or an
energy-fluctuation estimate. The two source propositions below retain
(4.4), p. 124, and (3.93), p. 101, as separate inputs.

The source objects are parameters with their mathematical characterizations;
this module makes no choice, existence claim, or uniqueness assumption.
These propositions are source transcriptions, not admitted theorems.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.External.AKM
open Environment.AKMTestIntegralSupport

/-- The open triadic cube of AKM (0.20), used in (1.22). -/
def sourceTriadicCube (d n : ℕ) : Set (Vec d) :=
  Set.pi Set.univ (fun _ => Set.Ioo (-((3 : ℝ) ^ n) / 2) (((3 : ℝ) ^ n) / 2))

/-- A zero-boundary Sobolev function together with its actual weak gradient.
The closure of smooth compactly supported functions is taken simultaneously
in the scalar and gradient L² norms, the definition of `H¹₀(U)` used in
AKM (1.7), printed p. 5. -/
def SourceH01 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ)
    (g : Vec d → Vec d) : Prop :=
  MemLp u 2 (volume.restrict U) ∧ MemLp g 2 (volume.restrict U) ∧
    HasWeakGradient U u g ∧
    ∃ v : ℕ → Vec d → ℝ, (∀ n, IsSpatialTest U (v n)) ∧
      Tendsto (fun n => ∫ x in U, (v n x - u x)^2 ∂volume) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x in U,
        euclideanSq (gradient (v n) x - g x) ∂volume) atTop (𝓝 0)

/-- The Dirichlet energy minimum `μ(U,e)`, AKM (1.7), p. 5.
The admissible potentials are `e·x + u` with `u ∈ H¹₀(U)`. -/
def sourceDirichletEnergy {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Set (Vec d)) (e : Vec d) : ℝ :=
  sInf {E : ℝ | ∃ (u : Vec d → ℝ) (g : Vec d → Vec d), SourceH01 U u g ∧
    E = ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ∂volume}

/-- The source first-order corrector characterization. Definitions 3.14--3.15,
Lemma 3.16 and its proof, pp. 98--100: a stationary local H¹ potential
gradient, affine harmonicity and centered sublinear L² oscillation.
No cell-flux integrability or mean-flux formula is a defining property. -/
structure SourceCorrector {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K))
    (e : Vec d) where
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
  sublinear : ∀ᵐ a ∂P, Tendsto
    (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (potential a x - ⨍ y in ball 0 R, potential a y ∂volume)^2 ∂volume))
    atTop (𝓝 0)

/-- The characterized objects used in AKM (4.4) and (3.93).
The matrix characterization is the symmetric quadratic-form identity of
Definition 1.2 with the limit (1.22), rather than a corrector-flux formula. -/
structure SourceObjects {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K)) where
  corrector : ∀ e : Vec d, SourceCorrector P e
  homogenized : Mat d
  symmetric : homogenized.transpose = homogenized
  variational_limit : ∀ e : Vec d,
    Tendsto (fun n : ℕ => ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P)
      atTop (𝓝 ((1 / 2 : ℝ) * dot e (homogenized.mulVec e)))

/-- Source objects are supplied only on AKM's domain of dimensions,
ellipticity constants and laws. This is data, not a theorem or a selection. -/
abbrev SourceFamily := ∀ (d : ℕ), 2 ≤ d → ∀ (K : ℝ), 1 < K →
  ∀ (P : Measure (Coefficient d K)), LawHypotheses P → SourceObjects P

/-- The literal Gaussian-weighted scalar energy of a source corrector. -/
def sourceEnergyAverage {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : SourceCorrector P e) (x : Vec d) (r : ℝ)
    (a : Coefficient d K) : ℝ :=
  ∫ y, heatKernel x r y *
    ((1 / 2 : ℝ) * dot (e + φ.grad a y) ((a y).mulVec (e + φ.grad a y))) ∂volume

/-- AKM Theorem 4.1, (4.4), printed p. 124, for its characterized source
corrector and homogenized matrix. The source's ordinary spatial integral
is required to exist; the stochastic estimate uses Appendix A's `O_s`.
The constant precedes the law, direction, center and scale. -/
def EnergyDensitySource (S : SourceFamily) : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K), 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient d K)) (hP : LawHypotheses P),
      ∀ (e : Vec d), euclideanNorm e < 1 → ∀ (x : Vec d) (r : ℝ), 1 ≤ r →
        (∀ᵐ a ∂P, Integrable (fun y => heatKernel x r y *
          ((1 / 2 : ℝ) * dot (e + ((S d hd K hK P hP).corrector e).grad a y)
            ((a y).mulVec (e + ((S d hd K hK P hP).corrector e).grad a y)))) volume) ∧
        OsBound P (fun a => |sourceEnergyAverage ((S d hd K hK P hP).corrector e) x r a -
          (1 / 2 : ℝ) * dot e ((S d hd K hK P hP).homogenized.mulVec e)|)
          s (C * r ^ (-(d : ℝ) / 2))

/-- AKM Remark 3.18, (3.93), printed p. 101. The spatial cell is literally
`[0,1]^d`. Existence of the expected vector integral is explicit; no
centered-cell conversion, energy estimate or corrector identification is assumed. -/
def MeanFluxSource (S : SourceFamily) : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 1 < K)
    (P : Measure (Coefficient d K)) (hP : LawHypotheses P) (e : Vec d),
    Integrable (fun a => ∫ x in Set.Icc (0 : Vec d) 1,
      (a x).mulVec (e + ((S d hd K hK P hP).corrector e).grad a x) ∂volume) P ∧
    (S d hd K hK P hP).homogenized.mulVec e =
      ∫ a, ∫ x in Set.Icc (0 : Vec d) 1,
        (a x).mulVec (e + ((S d hd K hK P hP).corrector e).grad a x) ∂volume ∂P

end EinsteinRelation.External.AKM
