import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.AKMLocalizedEnergy
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Draft.AKMLocalizedEnergy
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Source.AKMCoarsenedObjects
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Source.AKMLocalizedEnergy
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Correctors.HeatSmoothing
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMEnergyDensity
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.AKMLocalCorrectors

/-! Vocabulary for `EinsteinFull.External.Source.AKMSelectedLocalizedEnergy`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

noncomputable section

namespace EinsteinFull.External.Source.AKM

open EinsteinRelation EinsteinRelation.External.AKM

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The source parameters (5.82) and the part of (5.83) needed by Lemma5.29.
The auxiliary eta2 exists because eta1 is strictly below (1+delta)^(-1). -/
def blockParameterWindow (d : ℕ) (s δ γ η : ℝ) : Prop :=
  1 < s ∧ s < 2 ∧ 0 < δ ∧
  (d : ℝ) / 2 * (1 + δ) < γ ∧
  γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ) ∧
  1 / 2 < η ∧ η * γ > (d : ℝ) / 2 ∧ η < (1 + δ)⁻¹

/-- Structural source choices and genuine minimizing bases furnished by (5.85).
This is the same choice order as the actual covariance construction, on the
source coefficient space itself. No block estimate is part of the choice. -/
def sourceLocalizationSelection (d : ℕ) (hd : 2 ≤ d)
    (K s δ γ : ℝ) (hK : 1 < K) (hs : 1 < s) (hs' : s < 2)
    (hδ : 0 < δ) (hγ : (d : ℝ) / 2 * (1 + δ) < γ)
    (hγ' : γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ)) :
    Σ α σ θ C₀ : ℝ,
      ∀ P : Measure (Coefficient d K), LawHypotheses P →
        ∀ (a : Coefficient d K) (z : Vec d) (r : ℝ), 2 ≤ r →
          LocalizedBasis a z (localizationOuterRadius δ r)
            (localizationIntermediateRadius δ α γ r) σ θ C₀ := by
  let hex := EinsteinFull.External.akm_localized_energy d hd K s δ γ
    hK hs hs' hδ hγ hγ'
  let α := Classical.choose hex
  let hα := Classical.choose_spec hex
  let σ := Classical.choose hα
  let hσ := Classical.choose_spec hα
  let θ := Classical.choose hσ
  let hθ := Classical.choose_spec hσ
  let C₀ := Classical.choose hθ
  let hC₀ := Classical.choose_spec hθ
  let C := Classical.choose hC₀
  let hC := Classical.choose_spec hC₀
  exact ⟨α, σ, θ, C₀, fun P hP => Classical.choose
    (hC.2.2.2.2.2.2.2.2.2 P hP)⟩

/-- The actual selected energy, extended by zero only below its source domain
r>=2. Every source block statement explicitly retains r>=2. -/
def sourceSelectedLocalizedEnergy (d : ℕ) (hd : 2 ≤ d)
    (K s δ γ : ℝ) (hK : 1 < K) (hs : 1 < s) (hs' : s < 2)
    (hδ : 0 < δ) (hγ : (d : ℝ) / 2 * (1 + δ) < γ)
    (hγ' : γ < min ((d : ℝ) / s) ((d : ℝ) / 2 * (1 + δ) + δ))
    (P : Measure (Coefficient d K)) (hP : LawHypotheses P)
    (a : Coefficient d K) (z : Vec d) (r : ℝ) (p q : Vec d) : ℝ :=
  if hr : 2 ≤ r then
    localizedEnergyJ1 ((sourceLocalizationSelection d hd K s δ γ
      hK hs hs' hδ hγ hγ').2.2.2.2 P hP a z r hr) r p q
  else 0

/-- Source cube of side R, with the convention of AKM (0.27). -/
def sourceBlockCube {d : ℕ} (z : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | ∀ i, |x i - z i| < R / 2}

/-- The volume-normalized block in (5.90)--(5.92), not its CLT normalization.
J is the genuine source localization in every application below. -/
def sourceCenteredBlock {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K))
    (J : Coefficient d K → Vec d → ℝ → Vec d → Vec d → ℝ)
    (a : Coefficient d K) (z : Vec d) (R r : ℝ) (f : Vec d → ℝ)
    (p q : Vec d) : ℝ :=
  R ^ (-(d : ℝ)) * ∫ x in sourceBlockCube z R,
    f x * centeredLocalizedEnergy P J a x r p q

end EinsteinFull.External.Source.AKM
