import EinsteinRelationAudit.MobilityRate.Vocabulary.Regeneration.Construction

/-! Restated from the library module `EinsteinRelation.Regeneration.Coupling`:
the declarations of that module that the statement of
`EinsteinRelationAudit.MobilityRate.mobility_rate` depends on, in their module context. -/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinRelation.Regeneration
/-- A kernel restricted to the actual starting origin. -/
def originCoupledLaw {d : ℕ} (K : CoupledQuenchedLaws d) :
    ProbabilityTheory.Kernel (FieldPair d) (CoupledSample d) :=
  K.comap (fun ω => (0, ω)) (measurable_const.prodMk measurable_id)
/-- Actual joint annealed law, retaining both the physical environment and sample. -/
def annealedCoupledLaw {d : ℕ} (Q : Measure (FieldPair d))
    (K : CoupledQuenchedLaws d) : Measure (FieldPair d × CoupledSample d) :=
  Q.compProd (Probability.probabilityPart (originCoupledLaw K))
/-- Explicit bounded-test predicate used in the conditional kernel statements. -/
def BoundedRealTest {α : Type*} (f : α → ℝ) : Prop :=
  ∃ C : ℝ, ∀ x, |f x| ≤ C
/-- The off-origin reduced martingale law has product-a.e. spatial qualifiers. -/
def IsProductAEReducedLaw {d : ℕ} (Q : Measure (FieldPair d)) (i : Fin d)
    (lam : ℝ) (P : QuenchedPathLaws d) : Prop :=
  ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q),
    SolvesMartingaleProblem (reducedGenerator i xω.2 lam) xω.1 (P xω)
/-- GMP Prop.5.4 path marginal, explicitly at origin and product-a.e. elsewhere. -/
def HasPathMarginals {d : ℕ} (Q : Measure (FieldPair d))
    (K : CoupledQuenchedLaws d) (P : QuenchedPathLaws d) : Prop :=
  (∀ᵐ ω ∂Q, Measure.map Prod.fst (K (0, ω)) = P (0, ω)) ∧
  ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q),
    Measure.map Prod.fst (K xω) = P xω
/-- Exact probability qualifiers, including the origin not inferable from spatial a.e. -/
def HasProbabilityLaws {d : ℕ} (Q : Measure (FieldPair d))
    (K : CoupledQuenchedLaws d) : Prop :=
  (∀ᵐ ω ∂Q, IsProbabilityMeasure (K (0, ω))) ∧
  ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q), IsProbabilityMeasure (K xω)
/-- The actual annealed construction has mass one from its origin-a.e. clause.
Probability-part normalization leaves every source probability fibre unchanged. -/
theorem annealedCoupledLaw_isProbabilityMeasure {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) : IsProbabilityMeasure (annealedCoupledLaw Q K) :=
  Probability.isProbabilityMeasure_compProd_probabilityPart Q (originCoupledLaw K) hK.1
/-- GMP Prop.5.4(ii), the fresh bit identity against the exact finite past. -/
def FreshBitsAt {d : ℕ} (Δ : ℝ≥0) (δ : ℝ)
    (K : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d) : Prop :=
    ∀ (n : ℕ) (H : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H →
      BoundedRealTest H →
      (∫ z, H z * (if z.2 n = true then (1 : ℝ) else 0) ∂K xω) =
        δ * ∫ z, H z ∂K xω
/-- GMP Prop.5.4(ii), averaged over the fresh bit; it never uses a strong Markov
claim at the non-stopping regeneration time. Only deterministic grid times occur. -/
def DeterministicRestartAt {d : ℕ} (Δ : ℝ≥0)
    (K : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d) : Prop :=
    ∀ (n : ℕ) (H Φ : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H →
      BoundedRealTest H → Measurable Φ → BoundedRealTest Φ →
      (∫ z, H z * Φ (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂K xω) =
        ∫ z, H z * (∫ z', Φ z' ∂K (z.1 ((n : ℝ≥0) * Δ), xω.2)) ∂K xω
/-- The coupling support sets use the actual Euclidean norm from the source. -/
def couplingRegion {d : ℕ} (i : Fin d) (R : ℝ) (x : Vec d) : Set (Vec d) :=
  {y | euclideanNorm (y - (x + (5 * R) • unitVector i)) < 6 * R}
def endpointBall {d : ℕ} (i : Fin d) (R : ℝ) (x : Vec d) : Set (Vec d) :=
  {y | euclideanNorm (y - (x + (9 * R) • unitVector i)) < R}
def endpointAverage {d : ℕ} (i : Fin d) (R : ℝ) (x : Vec d)
    (φ : Vec d → ℝ) : ℝ :=
  (∫ y in endpointBall i R x, φ y) / (volume (endpointBall i R x)).toReal
/-- GMP Prop.5.4(iii) support, restarted at deterministic grid times. -/
def SuccessfulBridgeSupportAt {d : ℕ} (Δ : ℝ≥0)
    (i : Fin d) (R : ℝ) (K : CoupledQuenchedLaws d)
    (xω : Vec d × FieldPair d) : Prop :=
  ∀ᵐ z ∂K xω,
    ∀ n : ℕ, z.2 n = true → ∀ t : ℝ≥0,
      (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
      z.1 t ∈ couplingRegion i R (z.1 ((n : ℝ≥0) * Δ))
/-- Actual uniform endpoint statement in integral form, not a chosen random endpoint. -/
def UniformSuccessfulEndpointAt {d : ℕ} (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (K : CoupledQuenchedLaws d)
    (xω : Vec d × FieldPair d) : Prop :=
    ∀ (n : ℕ) (H : CoupledSample d → ℝ) (φ : Vec d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H →
      BoundedRealTest H → Measurable φ → BoundedRealTest φ →
      (∫ z, H z * (if z.2 n = true then (1 : ℝ) else 0) *
        φ (z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) ∂K xω) =
      δ * ∫ z, H z * endpointAverage i R (z.1 ((n : ℝ≥0) * Δ)) φ ∂K xω
/-- GMP Lemma5.8(5.22), attached to the ACTUAL trial-defined first regeneration. -/
def HasFirstRegenerationTail {d : ℕ} (Q : Measure (FieldPair d)) (Δ : ℝ≥0)
    (lam R c C : ℝ) (i : Fin d) (K : CoupledQuenchedLaws d) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    annealedCoupledLaw Q K {ωz |
      ENNReal.ofReal t < firstRegenerationTime Δ lam R ωz.2 i} ≤
        ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t))
/-- The no-backtracking mass lower bound, with its actual path event. -/
def HasNoBacktrackingMass {d : ℕ} (Q : Measure (FieldPair d))
    (R c : ℝ) (i : Fin d) (K : CoupledQuenchedLaws d) : Prop :=
  ENNReal.ofReal c ≤ annealedCoupledLaw Q K {ωz | NoBacktracking R ωz.2.1 i}
/-- Fresh-bit assertions retain the origin as well as product-a.e. versions. -/
def HasFreshBits {d : ℕ} (Q : Measure (FieldPair d)) (Δ : ℝ≥0) (δ : ℝ)
    (K : CoupledQuenchedLaws d) : Prop :=
  (∀ᵐ ω ∂Q, FreshBitsAt Δ δ K (0, ω)) ∧
  ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q), FreshBitsAt Δ δ K xω
def HasDeterministicRestart {d : ℕ} (Q : Measure (FieldPair d)) (Δ : ℝ≥0)
    (K : CoupledQuenchedLaws d) : Prop :=
  (∀ᵐ ω ∂Q, DeterministicRestartAt Δ K (0, ω)) ∧
  ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q), DeterministicRestartAt Δ K xω
def HasSuccessfulBridgeSupport {d : ℕ} (Q : Measure (FieldPair d)) (Δ : ℝ≥0)
    (i : Fin d) (R : ℝ) (K : CoupledQuenchedLaws d) : Prop :=
  (∀ᵐ ω ∂Q, SuccessfulBridgeSupportAt Δ i R K (0, ω)) ∧
  ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q), SuccessfulBridgeSupportAt Δ i R K xω
def HasUniformSuccessfulEndpoint {d : ℕ} (Q : Measure (FieldPair d)) (Δ : ℝ≥0)
    (δ R : ℝ) (i : Fin d) (K : CoupledQuenchedLaws d) : Prop :=
  (∀ᵐ ω ∂Q, UniformSuccessfulEndpointAt Δ δ R i K (0, ω)) ∧
  ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q), UniformSuccessfulEndpointAt Δ δ R i K xω
end EinsteinRelation.Regeneration
