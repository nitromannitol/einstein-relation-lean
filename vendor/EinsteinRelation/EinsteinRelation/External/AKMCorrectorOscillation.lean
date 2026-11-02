import EinsteinRelation.External.AKMEnergyDensity
import EinsteinRelation.Correctors.HeatSelectedSkewMeaningSupport
import EinsteinRelation.Environment.MatrixNorm

/-!
# AKM scalar and flux corrector oscillation estimates

Proposed, unfrozen literature propositions from Armstrong--Kuusi--Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity* (2019),
`paper/References/AKM.pdf`. Application: `paper/main.tex:704-749`.

All laws below use AKM's coefficient carrier and test-integral sigma algebra,
normalized ellipticity, lattice stationarity and unit range. No canonical
corrector identification, spatial rescaling, pointwise regularity, or passage
to spatial Lᵐ estimates is assumed. These remain internal proof obligations.
The norms with an overbar in AKM are normalized spatial L² norms.

The scalar stationary estimate is (4.5), printed p. 124 (PDF page 159).
The two-dimensional estimates are (4.6)--(4.7), on that same page, and
Proposition 4.27, (4.147), printed p. 181 (PDF page 216).
The flux gradient estimate is Lemma 6.1, (6.8), printed p. 246 (PDF page 281).
Its gradient is selected by (6.7) on that page. The stationary flux estimate
is Proposition 6.2, (6.14), printed p. 250 (PDF page 285); the difference of
heat averages is (6.16), on the same page. In particular, (6.14) is a bound
on the **square** of the normalized L² norm. No signed Poisson or divergence
identity is imported from this source.
-/

open MeasureTheory
open scoped Topology
noncomputable section
namespace EinsteinRelation.External.AKM
open Environment.AKMTestIntegralSupport

/-- AKM Appendix A's stochastic bound for an almost-everywhere measurable
representative. Corrector potentials are specified only almost surely, so
their stochastic estimates must be unchanged by null-set modifications. -/
def AEOsBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (s θ : ℝ) : Prop :=
  AEMeasurable X P ∧ 0 < s ∧ 0 < θ ∧
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P) ≤ 2

/-- Convolution against AKM's standard Euclidean heat kernel, (4.1). -/
def scalarHeatAverage {d : ℕ} (u : Vec d → ℝ) (x : Vec d) (r : ℝ) : ℝ :=
  ∫ z, heatKernel x r z * u z ∂volume

/-- Entrywise convolution; the matrix norm below is the Frobenius norm. -/
def fluxHeatAverage {d : ℕ} (S : Vec d → Mat d) (x : Vec d) (r : ℝ) : Mat d :=
  fun j k => scalarHeatAverage (fun z => S z j k) x r

/-- Lattice stationarity of the values of a scalar random field. -/
def ScalarStationary {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K))
    (u : Coefficient d K → Vec d → ℝ) : Prop :=
  ∀ z : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
    u a (x + latticeShift z) = u (translateCoefficient (latticeShift z) a) x

/-- AKM Theorem 4.1, (4.5), printed p. 124. The stationary representative
has the original corrector gradient, and its expected unit-cell mean is zero.
The exponent and constant precede the law and direction. -/
def ScalarStationaryEstimate : Prop :=
  ∀ (d : ℕ), 2 < d → ∀ (K : ℝ), 1 < K →
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
        ∀ (e : Vec d), euclideanNorm e < 1 → ∀ (φ : Corrector P e),
          ∃ ψ : Corrector P e,
            Measurable (fun p : Coefficient d K × Vec d => ψ.potential p.1 p.2) ∧
            (∀ᵐ a ∂P, ψ.grad a =ᵐ[volume] φ.grad a) ∧
            ScalarStationary P ψ.potential ∧
            (∫ a, ⨍ x in unitCell d, ψ.potential a x ∂volume ∂P) = 0 ∧
            OsBound P (fun a => Real.sqrt
              (⨍ x in unitCell d, |ψ.potential a x| ^ 2 ∂volume)) (2 + δ) C

/-- AKM Theorem 4.1, (4.6), printed p. 124: `r ≥ 2`, centered at the
heat average of scale `r` at the origin, in dimension two. -/
def ScalarPlanarL2Estimate : Prop :=
  ∀ (K s : ℝ), 1 < K → 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e < 1 → ∀ (φ : Corrector P e)
        (r : ℝ), 2 ≤ r →
        AEOsBound P (fun a => Real.sqrt (⨍ x in ball 0 r,
          |φ.potential a x - scalarHeatAverage (φ.potential a) 0 r| ^ 2 ∂volume))
          s (C * Real.sqrt (Real.log r))

/-- AKM Theorem 4.1, (4.7), printed p. 124, retaining both centers
and the restrictions `2 ≤ r ≤ R`. -/
def ScalarHeatDifferenceEstimate : Prop :=
  ∀ (K s : ℝ), 1 < K → 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e < 1 → ∀ (φ : Corrector P e)
        (r R : ℝ), 2 ≤ r → r ≤ R → ∀ (x y : Vec 2),
        AEOsBound P (fun a => |scalarHeatAverage (φ.potential a) x r -
          scalarHeatAverage (φ.potential a) y R|) s
          (C * Real.sqrt (Real.log (2 + (R + euclideanNorm (x - y)) / r)))

/-- AKM Proposition 4.27, (4.147), printed p. 181, with its stricter
restriction `2r ≤ R`. This is not a scale-one assertion. -/
def ScalarConcentricHeatDifferenceEstimate : Prop :=
  ∀ (K s : ℝ), 1 < K → 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e < 1 → ∀ (φ : Corrector P e)
        (r R : ℝ), 2 ≤ r → 2 * r ≤ R →
        AEOsBound P (fun a => |scalarHeatAverage (φ.potential a) 0 r -
          scalarHeatAverage (φ.potential a) 0 R|) s
          (C * Real.sqrt (Real.log (R / r)))

/-- The centered flux appearing in AKM (6.7), on the original coefficient carrier. -/
def centeredFlux {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : Corrector P e) (a : Coefficient d K) (x : Vec d) : Vec d :=
  (a x).mulVec (e + φ.grad a x) - meanFlux φ

/-- The local L² interpretation of the iterated positive-time integral
(6.7). Space is integrated first; the two time endpoints vary independently.
The integrability clauses ensure that both integrals are genuine integrals. -/
def IsHeatSelectedFluxGradient {d : ℕ} (g : Vec d → Vec d)
    (G : Fin d → Fin d → Vec d → Vec d) : Prop :=
  ∀ j k ℓ : Fin d, ∀ R : ℕ,
    let μ : Measure (Vec d) := volume.restrict (ball 0 (R + 1))
    (∀ m n : ℕ, ∀ᵐ x ∂μ,
      (∀ᵐ t ∂(volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))),
        Integrable (fun y =>
          Correctors.HeatSelectedSkewMeaning.akmHeatGradientDensity g t j k ℓ x y)
          volume) ∧
      Integrable (fun t =>
        Correctors.HeatSelectedSkewMeaning.akmHeatGradientSpaceIntegral g t j k ℓ x)
        (volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ)))) ∧
    (∀ m n : ℕ, MemLp
      (fun x => Correctors.HeatSelectedSkewMeaning.iteratedAKMHeatGradientTruncation
        g m n j k ℓ x) 2 μ) ∧
    MemLp (fun x => G j k x ℓ) 2 μ ∧
    Filter.Tendsto (fun mn : ℕ × ℕ => eLpNorm
      (fun x => Correctors.HeatSelectedSkewMeaning.iteratedAKMHeatGradientTruncation
        g mn.1 mn.2 j k ℓ x - G j k x ℓ) 2 μ) Filter.atTop (nhds 0)

/-- The potential selected, up to constants, by AKM (6.7). No estimate is
part of this carrier. The weak gradient, local Sobolev membership, and heat
selection describe the source object on the source coefficient law. -/
structure FluxCorrector {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : Corrector P e) where
  potential : Coefficient d K → Vec d → Mat d
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
  heat_selected : ∀ᵐ a ∂P, IsHeatSelectedFluxGradient (centeredFlux φ a) (grad a)

/-- AKM Lemma 6.1, (6.8), printed p. 246. The direction is on the
unit sphere, as printed, and the gradient norm is unsquared. -/
def FluxGradientEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (K : ℝ), 1 < K →
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
        ∀ (e : Vec d), euclideanNorm e = 1 → ∀ (φ : Corrector P e),
          Nonempty (FluxCorrector φ) ∧
          ∀ (S : FluxCorrector φ) (j k : Fin d),
            OsBound P (fun a => Real.sqrt
              (⨍ x in ball 0 1, euclideanSq (S.grad a j k x) ∂volume)) (2 + δ) C

/-- AKM Proposition 6.2, (6.14), printed p. 250. The squared normalized
L² norm is retained. Stationarity and zero expected cell mean fix the value gauge. -/
def FluxStationaryEstimate : Prop :=
  ∀ (d : ℕ), 2 < d → ∀ (K : ℝ), 1 < K →
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
        ∀ (e : Vec d), euclideanNorm e = 1 → ∀ (φ : Corrector P e)
          (S : FluxCorrector φ), ∃ T : FluxCorrector φ,
            (∀ᵐ a ∂P, ∀ j k, T.grad a j k =ᵐ[volume] S.grad a j k) ∧
            (∀ j k, ScalarStationary P (fun a x => T.potential a x j k)) ∧
            (∀ j k, (∫ a, ⨍ x in unitCell d, T.potential a x j k ∂volume ∂P) = 0) ∧
            OsBound P (fun a => ⨍ x in unitCell d,
              frobeniusNorm (T.potential a x) ^ 2 ∂volume) (2 + δ) C

/-- AKM Proposition 6.2, (6.16), printed p. 250. The printed range is
`1 ≤ r < R / √2`. Both heat centers are retained; this norm is unsquared. -/
def FluxHeatDifferenceEstimate : Prop :=
  ∀ (K s : ℝ), 1 < K → 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e = 1 → ∀ (φ : Corrector P e)
        (S : FluxCorrector φ) (r R : ℝ), 1 ≤ r → r < R / Real.sqrt 2 →
        ∀ (x y : Vec 2), OsBound P (fun a =>
          frobeniusNorm (fluxHeatAverage (S.potential a) x r -
            fluxHeatAverage (S.potential a) y R)) s
          (C * Real.sqrt (Real.log (2 + (R + euclideanNorm (x - y)) / r)))

/-- Proposed, unfrozen radius-at-least-two specialization of AKM
Proposition 6.2, (6.15), printed p. 250 (PDF page 284 in the local copy).
The source bounds the **squared** normalized L² norm by `C √(log r)`.
Its auxiliary restriction `r < R / √2` can be met by choosing `R = 2r`;
`R` does not occur in (6.15). The restriction `r ≥ 2` avoids the printed
endpoint and suffices for the fixed-radius-four use at
`paper/main.tex:718-723`. The stochastic bound uses an a.e. measurable
representative, as do the scalar planar contracts. -/
def FluxPlanarL2Estimate : Prop :=
  ∀ (K s : ℝ), 1 < K → 0 < s → s < 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e = 1 → ∀ (φ : Corrector P e)
        (S : FluxCorrector φ) (r : ℝ), 2 ≤ r →
        AEOsBound P (fun a => ⨍ x in ball 0 r,
          frobeniusNorm (S.potential a x -
            fluxHeatAverage (S.potential a) 0 r) ^ 2 ∂volume)
          s (C * Real.sqrt (Real.log r))

end EinsteinRelation.External.AKM
