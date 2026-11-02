import EinsteinRelation.Regeneration.Construction

/-! # Actual coupled kernels and the path-only locality boundary

Source `paper/main.tex:265–279,326–334,377–403`; GMP Proposition5.4,
Lemma5.8 and Shen2004 items1–4. These are literal kernel properties, with
origin and product-a.e. qualifiers explicit. No coupled-kernel existence input
is asserted or frozen by this module. Renewal and occupation remain internal.

The future-environment product extension below is proved from path/bit locality
and actual local measurability of the reduction. It is not an external premise.
-/

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

/-- A bounded measurable joint observation has exactly its quenched-then-annealed
integral; no s-finiteness premise on exceptional source fibres is added. -/
theorem integral_annealedCoupledLaw {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (F : FieldPair d × CoupledSample d → ℝ)
    (hF : Measurable F) (hb : BoundedRealTest F) :
    (∫ ωz, F ωz ∂annealedCoupledLaw Q K) =
      ∫ ω, ∫ z, F (ω, z) ∂K (0, ω) ∂Q :=
  Probability.integral_compProd_probabilityPart Q (originCoupledLaw K) hK.1 F hF hb

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

/-- Spatial recentering is separate from the deterministic time shift. -/
def recenterSample {d : ℕ} (x : Vec d) (z : CoupledSample d) : CoupledSample d :=
  (⟨fun t => z.1 t - x, z.1.continuous.sub continuous_const⟩, z.2)

/-- Required covariance of the canonical coupled construction; source audit must
justify this choice, rather than silently substituting spatial-a.e. claims at zero. -/
def HasTranslationCovariance {d : ℕ} (Q : Measure (FieldPair d))
    (K : CoupledQuenchedLaws d) : Prop :=
  ∀ x : Vec d, ∀ᵐ ω ∂Q,
    Measure.map (recenterSample x) (K (x, ω)) = K (0, translate x ω)

/-- Shen2004(3)–(4), as an a.e. version statement with joint starting-point
measurability. This is finite-history kernel locality, not renewal factorization. -/
def HasPastHalfSpaceVersions {d : ℕ} (Q : Measure (FieldPair d)) (Δ : ℝ≥0)
    (i : Fin d) (R : ℝ) (K : CoupledQuenchedLaws d) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (v : ℝ) (F : CoupledSample d → ℝ),
    @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance F →
    BoundedRealTest F →
    (∀ z, F z ≠ 0 → ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → z.1 t i ≤ v) →
    ∃ A : Vec d × FieldPair d → ℝ,
      @Measurable (Vec d × FieldPair d) ℝ
        ((borel (Vec d)).prod (localSigma {x : Vec d | x i ≤ v + 3 * R}))
        inferInstance A ∧
      (∀ᵐ ω ∂Q, A (0, ω) = ∫ z, F z ∂K (0, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] fun xω => ∫ z, F z ∂K xω

/-- INTERNAL derived product-test locality target. The cited primitive below
contains only path/bit expectations; the local environment factor is proved here.
The general joint test extension stays an internal proof. -/
def HasFutureHalfSpaceVersions {d : ℕ} (Q : Measure (FieldPair d))
    (i : Fin d) (R : ℝ) (K : CoupledQuenchedLaws d) : Prop :=
  ∀ (F : CoupledSample d → ℝ) (g : FieldPair d → ℝ),
    Measurable F → BoundedRealTest F →
    @Measurable (FieldPair d) ℝ (localSigma {x : Vec d | -2 * R ≤ x i})
      inferInstance g → BoundedRealTest g →
    ∃ A : FieldPair d → ℝ,
      @Measurable (FieldPair d) ℝ (localSigma {x : Vec d | -2 * R ≤ x i})
        inferInstance A ∧
      A =ᵐ[Q] fun ω => ∫ z,
        (if NoBacktracking R z.1 i then F z * g (reduce ω) else 0) ∂K (0, ω)

/-- Literal killed path/bit expectation locality from Shen2004(2).
No local environment test has been inserted in this candidate cited primitive. -/
def HasKilledPathBitFutureVersions {d : ℕ} (Q : Measure (FieldPair d))
    (i : Fin d) (R : ℝ) (K : CoupledQuenchedLaws d) : Prop :=
  ∀ (F : CoupledSample d → ℝ), Measurable F → BoundedRealTest F →
    ∃ A : FieldPair d → ℝ,
      @Measurable (FieldPair d) ℝ (localSigma {x : Vec d | -2 * R ≤ x i})
        inferInstance A ∧
      A =ᵐ[Q] fun ω => ∫ z,
        (if NoBacktracking R z.1 i then F z else 0) ∂K (0, ω)

/-- The environment factor is quenched-constant. Thus its local measurable
product extension is a proof, rather than an enlarged external input. -/
theorem future_product_versions_of_killed_path_bit {d : ℕ}
    (Q : Measure (FieldPair d)) (i : Fin d) (R : ℝ) (K : CoupledQuenchedLaws d)
    (hK : HasKilledPathBitFutureVersions Q i R K) :
    HasFutureHalfSpaceVersions Q i R K := by
  intro F g hF hbF hg _hbg
  obtain ⟨A, hA, hAe⟩ := hK F hF hbF
  refine ⟨fun ω => A ω * g (reduce ω),
    hA.mul (hg.comp (Probability.measurable_reduce_local _)), ?_⟩
  filter_upwards [hAe] with ω hω
  rw [hω, ← integral_mul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : NoBacktracking R z.1 i <;> simp [hz]

/-- The literature construction observes only the reduced matrix coefficient.
This carrier does not allow arbitrary dependence on the physical clock field. -/
abbrev CoefficientCoupledLaws (d : ℕ) :=
  ProbabilityTheory.Kernel (Vec d × CoefficientField d) (CoupledSample d)

/-- Measurable physical lift of a coefficient-only construction, not an
existence assertion and not a new external hypothesis. -/
def liftCoefficientCoupling {d : ℕ} (K : CoefficientCoupledLaws d) : CoupledQuenchedLaws d :=
  K.comap (fun xω => (xω.1, reducedMatrixField xω.2))
    (measurable_fst.prodMk (measurable_reducedMatrixField.comp measurable_snd))

/-- The physical lift uses exactly the concrete reduced coefficient. -/
theorem liftCoefficientCoupling_apply {d : ℕ} (K : CoefficientCoupledLaws d)
    (x : Vec d) (ω : FieldPair d) :
    liftCoefficientCoupling K (x, ω) = K (x, reducedMatrixField ω) := rfl

/-- Changing the physical pair while preserving the reduced matrix cannot
change any coupled law in this lifted construction. -/
theorem liftCoefficientCoupling_eq_of_reducedMatrixField_eq {d : ℕ}
    (K : CoefficientCoupledLaws d) (x : Vec d) (ω ω' : FieldPair d)
    (h : reducedMatrixField ω = reducedMatrixField ω') :
    liftCoefficientCoupling K (x, ω) = liftCoefficientCoupling K (x, ω') := by
  simp only [liftCoefficientCoupling_apply, h]

end EinsteinRelation.Regeneration
