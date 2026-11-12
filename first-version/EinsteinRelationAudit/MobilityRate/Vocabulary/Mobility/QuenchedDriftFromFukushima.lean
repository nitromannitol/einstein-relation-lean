import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Probability.Distributions.Exponential
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.Generator
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.HorizontalSobolev
import EinsteinRelationAudit.MobilityRate.Vocabulary.Calculus.HorizontalTranslationLp
import EinsteinRelationAudit.MobilityRate.Vocabulary.Carriers.DensityAnnealedTwins
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.EllipticOperatorBound
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.HorizontalH1EuclideanGradient
import EinsteinRelationAudit.MobilityRate.Vocabulary.Diffusion.GMPFamily
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Basic
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Bounds
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.SourceReducedBoundSupport
import EinsteinRelationAudit.MobilityRate.Vocabulary.External.GantertSection7Support
import EinsteinRelationAudit.MobilityRate.Vocabulary.Mobility.VelocityRateFromSteps
import EinsteinRelationAudit.MobilityRate.Vocabulary.Probability.LocalSigma
import EinsteinRelationAudit.MobilityRate.Vocabulary.Probability.ReductionLocality
import EinsteinRelationAudit.MobilityRate.Vocabulary.Probability.ValidAnnealedLawSupport

/-! Restated from the library module `EinsteinRelation.Mobility.QuenchedDriftFromFukushima`:
the declarations of that module that the statement of
`EinsteinRelationAudit.MobilityRate.mobility_rate` depends on, in their module context. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
open EinsteinRelation.External.GantertSection7Support
noncomputable section
namespace EinsteinRelation
open Carriers
variable {d : ℕ}
/-- The spatial gradient `∇u(x)` in coordinates. -/
def spatialGradient (u : Vec d → ℝ) (x : Vec d) : Vec d := fun k => fderiv ℝ u x (unitVector k)
/-- The martingale part `u(γ_t) - u(γ_0) - ∫₀ᵗ b(γ_s) ds` of a path for a function `u` with drift
`b`. -/
def pathMartingalePart (u b : Vec d → ℝ) (t : ℝ) (γ : Path d) : ℝ :=
  u (γ t.toNNReal) - u (γ 0) - ∫ s in (0 : ℝ)..t, b (γ s.toNNReal)
/-- `b` is the drift of `u` in the weak sense:
`E^{λ,ω}(u, v) = ½ ∫ ∇u · a ∇v dm_λ = -∫ b v dm_λ` for every compactly supported `C¹` function
`v`, where `m_λ = physicalReversibleMeasure ω hd lam` is the reversible measure. -/
def IsWeakDrift (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ) (u b : Vec d → ℝ) : Prop :=
  ∀ v : Vec d → ℝ, ContDiff ℝ 1 v → HasCompactSupport v →
    ∫ x, (1 / 2 : ℝ) * dot (spatialGradient u x) ((ω.1 x).mulVec (spatialGradient v x))
        ∂physicalReversibleMeasure ω hd lam =
      -∫ x, b x * v x ∂physicalReversibleMeasure ω hd lam
/-- **FOT Theorem 5.5.5 for a `C¹` function with bounded gradient** (Fukushima, Oshima and Takeda
2011, Theorem 5.5.5, p. 275, under the absolute continuity condition (4.2.9), p. 165; GMP 2012,
Section 7, p. 32, and Lemma 7.1, p. 33). For a regular pair `ω` with constant `K`, every GMP
Section 7 realization `r` at force `0 ≤ λ ≤ 1`, every `C¹` function `u` with `|∇u| ≤ G` and every
bounded Borel `b` that is the weak drift of `u`, the process `u(Y_t) - u(Y_0) - ∫₀ᵗ b(Y_s) ds` from
the origin is square integrable with second moment at most `K G² t` and mean zero.

FOT (5.5.8)-(5.5.9) give `u(Y_t) - u(Y_0) = M_t + ∫₀ᵗ b(Y_s) ds` almost surely from every starting
point, and (5.5.11) gives `E_x[M_{t∧τ_G}²] = E_x[∫₀^{t∧τ_G} ∇u·a∇u(Y_s) ds] ≤ K G² t` for every
relatively compact open `G ∋ x`; Fatou's lemma along balls `G ↑ ℝ^d` gives the bound at `t`.
(5.5.10) gives `E_x[M_{t∧τ_G}] = 0`; the uniform `L²` bound makes `M_{t∧τ_G}` uniformly integrable
along balls, so `E₀[M_t] = 0`. The heat-kernel density of the realization is (4.2.9). -/
def FukushimaDecompositionInput : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 1 ≤ K) (ω : FieldPair d) (hω : IsRegular K ω) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (r : GantertFixedEnvironmentRealization hd K hK ω hω lam h0 h1)
    (u : Vec d → ℝ) (G : ℝ), ContDiff ℝ 1 u → (∀ x, euclideanNorm (spatialGradient u x) ≤ G) →
    ∀ b : Vec d → ℝ, Measurable b → (∃ B : ℝ, ∀ x, |b x| ≤ B) → IsWeakDrift hd ω lam u b →
    ∀ t : ℝ, 0 ≤ t →
      MemLp (pathMartingalePart u b t) 2 (r.pathLaw 0) ∧
        ∫ γ, pathMartingalePart u b t γ ^ 2 ∂r.pathLaw 0 ≤ K * G ^ 2 * t ∧
        ∫ γ, pathMartingalePart u b t γ ∂r.pathLaw 0 = 0
end EinsteinRelation
