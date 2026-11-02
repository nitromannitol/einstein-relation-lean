import EinsteinRelation.Regeneration.RenewalCarriers
import Mathlib.Probability.Independence.Basic

/-! Literal fixed-environment objects of GMP Proposition 5.4, printed p.23.
The family is indexed by spatial starting points. No joint environment kernel,
finite-range factorization, regeneration theorem or one-interval bridge formula
is included in its meaning. -/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.External.Source.GMP
open EinsteinRelation EinsteinRelation.Regeneration

/-- The actual source conditional path law, conditioned on the first coin. -/
def conditionalPathLaw {d : ℕ} (K : Vec d → Measure (CoupledSample d))
    (x : Vec d) (b : Bool) : Measure (Path d) :=
  (ProbabilityTheory.cond (K x) {z | z.2 0 = b}).map Prod.fst

/-- Source `F_(m Delta) x S_m`: the full path past and coins through m.
The existing finite-history sigma algebra contains only coins strictly before m. -/
def currentCoinHistory {d : ℕ} (Δ : ℝ≥0) (m : ℕ) :
    MeasurableSpace (CoupledSample d) :=
  finiteHistorySigma Δ m ⊔
    MeasurableSpace.comap (fun z : CoupledSample d => z.2 m) inferInstance

/-- Integrated form of the actual killed-density minorization (GMP (5.3)),
with its factor 2 delta and the source Euclidean balls U_x and B_x. -/
def HasSourceMinorization {d : ℕ} (P : Vec d → Measure (Path d))
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) : Prop :=
  ∀ x : Vec d, ∀ A : Set (Vec d), MeasurableSet A →
    ENNReal.ofReal (2 * δ) *
        ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) A ≤
      P x {γ | (∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R x) ∧ γ Δ ∈ A}

/-- The conclusions of GMP Proposition 5.4(i)--(iii) on its fixed-environment
path/coin space. Coin independence uses the entire future sequence; restart
conditions on the current coin, while successful support and the uniform
endpoint are statements about the actual first-coin conditional path law. -/
def IsSourceSplitCoupling {d : ℕ} (P : Vec d → Measure (Path d))
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (K : Vec d → Measure (CoupledSample d)) : Prop :=
  ∀ x : Vec d,
    IsProbabilityMeasure (K x) ∧
    (K x).map Prod.fst = P x ∧
    (∀ (F : Finset ℕ) (b : ℕ → Bool),
      K x {z | ∀ k ∈ F, z.2 k = b k} =
        ∏ k ∈ F, ENNReal.ofReal (if b k then δ else 1 - δ)) ∧
    (∀ m : ℕ,
      ProbabilityTheory.Indep
        (MeasurableSpace.comap
          (fun z : CoupledSample d => fun n : ℕ => z.2 (m + n)) inferInstance)
        (finiteHistorySigma Δ m) (K x)) ∧
    (∀ (m : ℕ) (H : CoupledSample d → ℝ) (F : Path d → ℝ),
      @Measurable (CoupledSample d) ℝ (currentCoinHistory Δ m) inferInstance H →
      BoundedRealTest H → Measurable F → BoundedRealTest F →
      Integrable (fun z => H z *
        ∫ γ, F γ ∂conditionalPathLaw K (z.1 ((m : ℝ≥0) * Δ)) (z.2 m)) (K x) ∧
      (∫ z, H z * F (pathTimeShift z.1 ((m : ℝ≥0) * Δ)) ∂K x) =
        ∫ z, H z *
          (∫ γ, F γ ∂conditionalPathLaw K (z.1 ((m : ℝ≥0) * Δ)) (z.2 m)) ∂K x) ∧
    (∀ᵐ γ ∂conditionalPathLaw K x true,
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R x) ∧
    (conditionalPathLaw K x true).map (fun γ => γ Δ) =
      ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x)

end EinsteinFull.External.Source.GMP
