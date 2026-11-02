import EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinRelation.Calculus.Weak
import EinsteinRelation.Correctors.HeatSmoothing
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# The energy-density estimate of Armstrong--Kuusi--Mourrat

Source for `EnergyDensityEstimate`: AKM, *Quantitative Stochastic Homogenization
and Large-Scale Regularity* (2019), Theorem 4.1, (4.4), printed p. 124;
`paper/References/AKM.pdf`. Application: `paper/main.tex:727-729`.
This is a proposed, unfrozen literature contract, not an admitted theorem.

The coefficient carrier and its test-integral sigma algebra are the literal
normalized objects (0.6)--(0.11). Correctors below are spatial potentials on that
carrier, not the project's horizontal correctors. Their characterization is
Section 3.4, Definitions 3.14--3.15 and Lemma 3.16, pp. 98--100.
All spatial integrals use coordinate Lebesgue measure. Balls and vector lengths
are Euclidean. The cell has side length one and volume one. Additive constants
in the scalar potential have no effect. The homogenized flux is its expected
unit-cell flux, as in Remark 3.18, (3.93), p. 101. The centered-cell
convention additionally requires a cell-change proof before source identification. Identifying these objects with the project's
canonical correctors is a separate internal obligation.
-/

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

/-- The actual heat average of the energy density, with its factor `1/2`. -/
def energyAverage {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)} {e : Vec d}
    (φ : Corrector P e) (x : Vec d) (r : ℝ) (a : Coefficient d K) : ℝ :=
  ∫ y, heatKernel x r y *
    ((1 / 2 : ℝ) * dot (e + φ.grad a y) ((a y).mulVec (e + φ.grad a y))) ∂volume

/-- AKM Appendix A, (A.1)--(A.2), p. 455. Positivity of `s, θ` is explicit;
`X₊ = max X 0`. This notation itself supplies no stochastic estimate. -/
def OsBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (s θ : ℝ) : Prop :=
  Measurable X ∧ 0 < s ∧ 0 < θ ∧
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P) ≤ 2

/-- AKM Theorem 4.1, (4.4), p. 124, with its own normalized law and
spatial corrector. Constants precede the law, direction, center and scale.
The source uses `e ∈ B₁` (the open ball), `r ≥ 1`, and `0 < s < 2`.
The centered quantity is the energy deviation, not a local gradient norm.
The expected-flux expression for `ā e` is spelled out in `meanFlux`.
No canonical-gradient identification or continuum stationarity is built in. -/
def EnergyDensityEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (K s : ℝ), 1 < K → 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
      ∀ (e : Vec d), euclideanNorm e < 1 → ∀ (φ : Corrector P e)
        (x : Vec d) (r : ℝ), 1 ≤ r →
        OsBound P (fun a => |energyAverage φ x r a - (1 / 2 : ℝ) * dot e (meanFlux φ)|)
          s (C * r ^ (-(d : ℝ) / 2))

/-- Proposed, unfrozen consequence of AKM Theorem 3.3, (3.17), printed
p. 75 (PDF p. 110), with stochastic exponent `s = 1`. Application:
`paper/main.tex:693-698,727-729`. The strict source restriction `K > 1`
is retained. The constant precedes the law, and a single almost surely
finite threshold works for every solution and both radii. Only the
oscillation estimate is retained; the stronger threshold moment bound
is not needed for a sublinear Liouville argument. The four weak-solution
hypotheses are exactly the scalar `H¹` equation, without a regularity,
growth or corrector-identification assumption. This declaration is a
literature proposition, not a theorem or a frozen input. -/
def LargeScaleOscillationEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (K : ℝ), 1 < K →
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient d K)),
      LawHypotheses P → ∀ᵐ a ∂P, ∃ X : ℝ, 1 ≤ X ∧
        ∀ (R : ℝ), X ≤ R →
          ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
            MemLp u 2 (volume.restrict (ball 0 R)) →
            MemLp g 2 (volume.restrict (ball 0 R)) →
            HasWeakGradient (ball 0 R) u g →
            HasWeakDivergence (ball 0 R)
              (fun x => (a.field x).mulVec (g x)) (fun _ => 0) →
            ∀ (r : ℝ), X ≤ r → r ≤ R →
              r⁻¹ * Real.sqrt (⨍ x in ball 0 r,
                (u x - ⨍ y in ball 0 r, u y ∂volume) ^ 2 ∂volume) ≤
              C * R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
                (u x - ⨍ y in ball 0 R, u y ∂volume) ^ 2 ∂volume)

/-- The actual rescaled coefficient law already meets the probabilistic AKM
hypotheses; no further mixing or invariance assumption is necessary. -/
theorem lawHypotheses_actualCoefficientLaw {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) : LawHypotheses (actualCoefficientLaw Q) :=
  ⟨actualCoefficientLaw_probability Q, actualCoefficientLaw_translation_invariant Q,
    actualCoefficientLaw_finiteRange Q⟩

/-- An elementary exponential domination used to convert Appendix A's
`O₁` bound into arbitrary real moments. -/
theorem rpow_le_exp_mul {x p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) :
    x ^ p ≤ p ^ p * Real.exp x := by
  by_cases hx0 : x = 0
  · simp [hx0, Real.zero_rpow hp.ne', Real.rpow_nonneg hp.le]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  rw [Real.rpow_def_of_pos hxpos, Real.rpow_def_of_pos hp, ← Real.exp_add,
    Real.exp_le_exp]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hxpos hp)
  rw [Real.log_div hx0 hp.ne'] at hlog
  have h := mul_le_mul_of_nonneg_right hlog hp.le
  have hcancel : x / p * p = x := div_mul_cancel₀ x hp.ne'
  nlinarith

/-- Finite real moments from AKM Appendix A, with an explicit constant.
Only `s = 1` is needed to use (4.4) for Lemma 5.1. -/
theorem OsBound.moment_pos_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {θ p : ℝ}
    (h : OsBound P X 1 θ) (hp : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal ((max (X ω) 0) ^ p) ∂P) ≤
      ENNReal.ofReal (2 * θ ^ p * p ^ p) := by
  have hθ : 0 < θ := h.2.2.1
  have hpt (ω : Ω) : (max (X ω) 0) ^ p ≤
      (θ ^ p * p ^ p) * Real.exp (θ⁻¹ * max (X ω) 0) := by
    have hdom := rpow_le_exp_mul (mul_nonneg (inv_nonneg.mpr hθ.le)
      (le_max_right (X ω) 0)) hp
    have hscale : max (X ω) 0 = θ * (θ⁻¹ * max (X ω) 0) := by
      rw [← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul]
    calc (max (X ω) 0) ^ p = θ ^ p * (θ⁻¹ * max (X ω) 0) ^ p := by
          conv_lhs => rw [hscale]
          exact Real.mul_rpow hθ.le (by positivity)
      _ ≤ θ ^ p * (p ^ p * Real.exp (θ⁻¹ * max (X ω) 0)) :=
          mul_le_mul_of_nonneg_left hdom (Real.rpow_nonneg hθ.le _)
      _ = _ := by ring
  have hexp : (∫⁻ ω, ENNReal.ofReal
      (Real.exp (θ⁻¹ * max (X ω) 0)) ∂P) ≤ 2 := by
    simpa only [Real.rpow_one] using h.2.2.2
  calc (∫⁻ ω, ENNReal.ofReal ((max (X ω) 0) ^ p) ∂P)
      ≤ ∫⁻ ω, ENNReal.ofReal ((θ ^ p * p ^ p) *
          Real.exp (θ⁻¹ * max (X ω) 0)) ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (θ ^ p * p ^ p) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp (θ⁻¹ * max (X ω) 0)) ∂P) := by
      simp_rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hθ.le _)
        (Real.rpow_nonneg hp.le _))]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (θ ^ p * p ^ p) * 2 := mul_le_mul_right hexp _
    _ = ENNReal.ofReal (2 * θ ^ p * p ^ p) := by
      rw [show (2 * θ ^ p * p ^ p) = (θ ^ p * p ^ p) * 2 by ring,
        ENNReal.ofReal_mul (by positivity : 0 ≤ θ ^ p * p ^ p), ENNReal.ofReal_ofNat]

end EinsteinRelation.External.AKM

#print axioms EinsteinRelation.External.AKM.lawHypotheses_actualCoefficientLaw
#print axioms EinsteinRelation.External.AKM.OsBound.moment_pos_le
