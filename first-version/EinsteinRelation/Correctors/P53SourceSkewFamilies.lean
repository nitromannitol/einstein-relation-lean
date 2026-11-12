import EinsteinRelation.Correctors.P53SourceSkewColumn
import EinsteinRelation.Correctors.P53SourceSkewScalarPotential
import EinsteinRelation.Correctors.WeakGradientCentering
import EinsteinRelation.Calculus.SourceMollifierSupport
import EinsteinRelation.Entropy.DivergenceSecondAssertion

/-!
# The normalized scalar and skew source families of Proposition 5.3

Source: `paper/main.tex:754-758,887-918`. Proposition 5.3 conditions the scalar
corrector minus its `ζ_R` average, and the skew flux corrector minus its average
against the scaled unit-mass mollifier, on coefficient balls. This module fixes,
for every environment law, radius `R ≥ 1` and direction, one jointly measurable
normalized scalar potential and one pointwise skew, heat-selected flux corrector
with zero mollifier average. Inputs: `FluxGradientEstimate` (AKM Lemma 6.1) and
`BallPoincareEstimate` (Gilbarg–Trudinger (7.45)).
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning NormalizedSpatialRepresentativeSupport
open NormalizedScalarPhysicalLawTransportSupport

variable {d : ℕ}

private theorem integral_coordLaplacian_eq_zero {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, ∑ l, coordinateDerivative l (coordinateDerivative l ψ) x = 0 := by
  rw [integral_finset_sum _ fun l _ =>
    (contDiff_coordinateDerivative' (contDiff_coordinateDerivative' hψ l) l).continuous
      |>.integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative' (hasCompactSupport_coordinateDerivative' hψc l) l)]
  exact Finset.sum_eq_zero fun l _ => integral_coordinateDerivative_eq_zero
    (contDiff_coordinateDerivative' hψ l) (hasCompactSupport_coordinateDerivative' hψc l) l

/-- Subtracting a skew matrix depending only on the environment preserves the heat
selection, the skewness and both source identities. -/
theorem hasHeatSelectedSkewCorrectorColumn_sub {hd : 2 ≤ d} {L r₀ : ℝ}
    {Q : EnvironmentLaw d L r₀} {i : Fin d} {σ : FieldPair d → Vec d → Mat d}
    (hσ : HasHeatSelectedSkewCorrectorColumn hd Q i σ) (C : FieldPair d → Mat d)
    (hC : ∀ ω, (C ω).transpose = -(C ω)) :
    HasHeatSelectedSkewCorrectorColumn hd Q i (fun ω x => σ ω x - C ω) := by
  obtain ⟨F, hFm, hae⟩ := hσ
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hae] with ρ hρ
  obtain ⟨⟨hsk, hdiv, hpois⟩, hit, hrep⟩ := hρ
  refine ⟨⟨?_, fun ψ hψ hψc j => ?_, fun ψ hψ hψc j k => ?_⟩, hit,
    fun row col => hasWeakGradient_sub_const Set.univ (hrep row col) (C ρ row col)⟩
  · filter_upwards [hsk] with x hx
    rw [Matrix.transpose_sub, hx, hC, neg_sub_neg, neg_sub]
  · obtain ⟨h1, h2, h3⟩ := hdiv ψ hψ hψc j
    have hc (k : Fin d) : Integrable (fun x => C ρ j k * coordinateDerivative k ψ x) volume :=
      ((contDiff_coordinateDerivative' hψ k).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative' hψc k)).const_mul _
    have hcs : Integrable (fun x => ∑ k, C ρ j k * coordinateDerivative k ψ x) volume :=
      integrable_finset_sum _ fun k _ => hc k
    have hc0 : ∫ x, ∑ k, C ρ j k * coordinateDerivative k ψ x = 0 := by
      rw [integral_finset_sum _ fun k _ => hc k]
      exact Finset.sum_eq_zero fun k _ => by
        rw [integral_const_mul, integral_coordinateDerivative_eq_zero hψ hψc k, mul_zero]
    have heq : (fun x => ∑ k, (σ ρ x - C ρ) j k * coordinateDerivative k ψ x) =
        fun x => (∑ k, σ ρ x j k * coordinateDerivative k ψ x) -
          ∑ k, C ρ j k * coordinateDerivative k ψ x := by
      funext x
      simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    refine ⟨h1, ?_, ?_⟩
    · change Integrable (fun x => ∑ k, (σ ρ x - C ρ) j k * coordinateDerivative k ψ x) volume
      rw [heq]
      exact h2.sub hcs
    · change (∫ x, _) = -(∫ x, ∑ k, (σ ρ x - C ρ) j k * coordinateDerivative k ψ x)
      rw [heq, integral_sub h2 hcs, hc0, sub_zero]
      exact h3
  · obtain ⟨h1, h2, h3, h4⟩ := hpois ψ hψ hψc j k
    have hlapi : Integrable (fun x => -∑ l, coordinateDerivative l (coordinateDerivative l ψ) x)
        volume :=
      (integrable_finset_sum _ fun l _ =>
        (contDiff_coordinateDerivative' (contDiff_coordinateDerivative' hψ l) l).continuous
          |>.integrable_of_hasCompactSupport (hasCompactSupport_coordinateDerivative'
            (hasCompactSupport_coordinateDerivative' hψc l) l)).neg
    have hci : Integrable (fun x => C ρ j k *
        -∑ l, coordinateDerivative l (coordinateDerivative l ψ) x) volume :=
      hlapi.const_mul _
    have heq : (fun x => (σ ρ x - C ρ) j k *
        -∑ l, coordinateDerivative l (coordinateDerivative l ψ) x) =
        fun x => σ ρ x j k * (-∑ l, coordinateDerivative l (coordinateDerivative l ψ) x) -
          C ρ j k * -∑ l, coordinateDerivative l (coordinateDerivative l ψ) x := by
      funext x
      rw [Matrix.sub_apply, sub_mul]
    refine ⟨?_, h2, h3, ?_⟩
    · change Integrable (fun x => (σ ρ x - C ρ) j k *
        -∑ l, coordinateDerivative l (coordinateDerivative l ψ) x) volume
      rw [heq]
      exact h1.sub hci
    · change (∫ x, (σ ρ x - C ρ) j k *
        -∑ l, coordinateDerivative l (coordinateDerivative l ψ) x) = _
      rw [heq, integral_sub h1 hci, integral_const_mul, integral_neg,
        integral_coordLaplacian_eq_zero hψ hψc, neg_zero, mul_zero, sub_zero]
      exact h4

/-- The average of a matrix field against the scaled unit-mass mollifier. -/
def mollifierMatrixAverage (R : ℝ) (σ : Vec d → Mat d) : Mat d :=
  fun j k => ∫ y, Calculus.unitMassScaledMollifier d R y * σ y j k

theorem mollifierMatrixAverage_transpose {R : ℝ} {σ : Vec d → Mat d}
    (hσ : ∀ x, (σ x).transpose = -(σ x)) :
    (mollifierMatrixAverage R σ).transpose = -(mollifierMatrixAverage R σ) := by
  ext j k
  simp only [Matrix.transpose_apply, Matrix.neg_apply, mollifierMatrixAverage]
  rw [← integral_neg]
  congr 1
  funext y
  have h := congrFun (congrFun (hσ y) j) k
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  rw [h, mul_neg]

/-- Normalizing any heat-selected, jointly measurable, pointwise skew and locally
square-integrable flux corrector by its average against the scaled unit-mass
mollifier keeps all of these properties, gives zero average against the reflected
mollifier, and keeps spatial continuity. -/
theorem mollifierNormalized_skew_properties [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) {σ : FieldPair d → Vec d → Mat d}
    (hσ : HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ)
    (hσm : ∀ j k, Measurable (fun p : FieldPair d × Vec d => σ p.1 p.2 j k))
    (hσsk : ∀ ω x, (σ ω x).transpose = -(σ ω x))
    (hσL2 : ∀ᵐ ρ ∂reducedEnvironmentLaw Q, ∀ R : ℝ, 0 < R → ∀ j k,
      MemLp (fun x => σ ρ x j k) 2 (volume.restrict (ball 0 R)))
    {R : ℝ} (hR : 1 ≤ R) :
    HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i
        (fun ω x => σ ω x - mollifierMatrixAverage R (σ ω)) ∧
      (∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d =>
        (σ z.1 z.2 - mollifierMatrixAverage R (σ z.1)) j k)) ∧
      (∀ ω x, (σ ω x - mollifierMatrixAverage R (σ ω)).transpose =
        -(σ ω x - mollifierMatrixAverage R (σ ω))) ∧
      (∀ j k, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        (∫ z, Calculus.unitMassScaledMollifier d R (-z) *
          (σ ω (-z) - mollifierMatrixAverage R (σ ω)) j k) = 0) ∧
      (∀ ω, Continuous (σ ω) →
        Continuous (fun x => σ ω x - mollifierMatrixAverage R (σ ω))) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  refine ⟨hasHeatSelectedSkewCorrectorColumn_sub hσ _
      (fun ω => mollifierMatrixAverage_transpose (hσsk ω)), fun j k => ?_, fun ω x => ?_,
    fun j k => ?_, fun ω hω => hω.sub continuous_const⟩
  · have hc : Measurable (fun ω => mollifierMatrixAverage R (σ ω) j k) := by
      have hj : StronglyMeasurable (fun p : FieldPair d × Vec d =>
          Calculus.unitMassScaledMollifier d R p.2 * σ p.1 p.2 j k) :=
        (((Entropy.contDiff_unitMassScaledMollifier R).continuous.measurable.comp
          measurable_snd).mul (hσm j k)).stronglyMeasurable
      exact hj.integral_prod_right'.measurable
    exact ((hσm j k).sub (hc.comp measurable_fst)).stronglyMeasurable
  · rw [Matrix.transpose_sub, hσsk ω x, mollifierMatrixAverage_transpose (hσsk ω), neg_sub_neg,
      neg_sub]
  · filter_upwards [hσL2] with ω hω
    have hm : Integrable (fun y => Calculus.unitMassScaledMollifier d R y * σ ω y j k)
        volume := by
      have hloc : LocallyIntegrable (fun y => σ ω y j k) volume := by
        refine (locallyIntegrable_iff.mpr fun K hK => ?_)
        obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hK.isBounded
        obtain ⟨N, hN⟩ := exists_nat_cube_subset_ball (d := d) (r + 1)
        have hsub : K ⊆ ball 0 ((N : ℝ) + 1) := fun x hx => hN (by
          have := hr hx
          rw [Metric.mem_closedBall] at this
          rw [Metric.mem_ball]
          linarith)
        have hmem := hω ((N : ℝ) + 1) (by positivity) j k
        haveI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) ((N : ℝ) + 1))) :=
          isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp
            (ball_volume_pos_finite d _ (by positivity))).2.ne
        have hOn : IntegrableOn (fun y => σ ω y j k) (ball 0 ((N : ℝ) + 1)) volume :=
          hmem.integrable one_le_two
        exact hOn.mono_set hsub
      simpa only [smul_eq_mul] using hloc.integrable_smul_left_of_hasCompactSupport
        (Entropy.contDiff_unitMassScaledMollifier R).continuous
        (Entropy.hasCompactSupport_unitMassScaledMollifier hR0)
    have hneg := integral_neg_eq_self (fun z => Calculus.unitMassScaledMollifier d R z *
      (σ ω z - mollifierMatrixAverage R (σ ω)) j k) volume
    rw [hneg]
    simp only [Matrix.sub_apply, mul_sub]
    rw [integral_sub hm ((Entropy.contDiff_unitMassScaledMollifier R).continuous
      |>.integrable_of_hasCompactSupport
        (Entropy.hasCompactSupport_unitMassScaledMollifier hR0) |>.mul_const _),
      integral_mul_const, Entropy.integral_unitMassScaledMollifier' hR0, one_mul]
    simp only [mollifierMatrixAverage, sub_self]

/-- The source families of Proposition 5.3: for each law, radius and direction, a
normalized canonical scalar corrector and a heat-selected skew flux corrector,
jointly measurable, skew at every point, with zero average against the reflected
scaled mollifier. The statement is shaped for
`correctorLocalConstruction_of_canonical_sources_and_tails`; the mollifier average
is written as the literal integral defining `mollifierCenterMeasure`.
Inputs: `FluxGradientEstimate`, `BallPoincareEstimate`. -/
theorem exists_canonical_source_families (h68 : FluxGradientEstimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate) :
    ∃ (u : ∀ {d : ℕ} {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
        FieldPair d → Vec d → ℝ)
      (S : ∀ {d : ℕ} {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
        FieldPair d → Vec d → Mat d),
      (∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
        (Q : EnvironmentLaw d L r₀) (R : ℝ) (hR : 1 ≤ R) (i : Fin d),
        IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d) R hR 0
          (fun ω x => u Q R i ω x.ofLp)) ∧
      (∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
        (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i (S Q R i)) ∧
      (∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
        (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i j k : Fin d,
        StronglyMeasurable (fun z : FieldPair d × Vec d => S Q R i z.1 z.2 j k)) ∧
      (∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
        (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ (i : Fin d) (ω : FieldPair d)
          (x : Vec d), (S Q R i ω x).transpose = -(S Q R i ω x)) ∧
      (∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
        (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i j k : Fin d,
        ∀ᵐ ω ∂reducedEnvironmentLaw Q,
          (∫ z, Calculus.unitMassScaledMollifier d R (-z) * S Q R i ω (-z) j k) = 0) := by
  classical
  -- the scalar family
  let u : ∀ {d : ℕ} {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
      FieldPair d → Vec d → ℝ := fun {d} {L} {r₀} Q R i ω x =>
    if h : 2 ≤ d ∧ 1 ≤ R then
      haveI : Fact (2 ≤ d) := ⟨h.1⟩
      Classical.choose (exists_normalizedCanonicalScalarCorrector hP Q i
        (canonicalSourceMollifier d) R h.2 0) ω (WithLp.toLp 2 x)
    else 0
  -- the unnormalized skew family
  let σ : ∀ {d : ℕ} {L r₀ : ℝ}, EnvironmentLaw d L r₀ → Fin d →
      FieldPair d → Vec d → Mat d := fun {d} {L} {r₀} Q i =>
    if h : 2 ≤ d then
      haveI : Fact (2 ≤ d) := ⟨h⟩
      Classical.choose (exists_heatSelectedSkewCorrectorColumn h68 hP Q i)
    else fun _ _ => 0
  have hσspec : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
      (i : Fin d),
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i (σ Q i) ∧
      (∀ j k, Measurable (fun p : FieldPair d × Vec d => σ Q i p.1 p.2 j k)) ∧
      (∀ ω x, (σ Q i ω x).transpose = -(σ Q i ω x)) ∧
      ∀ᵐ ρ ∂reducedEnvironmentLaw Q, ∀ R : ℝ, 0 < R → ∀ j k,
        MemLp (fun x => σ Q i ρ x j k) 2 (volume.restrict (ball 0 R)) :=
    fun {d} [hd : Fact (2 ≤ d)] {L} {r₀} Q i => by
    have h : σ Q i = Classical.choose (exists_heatSelectedSkewCorrectorColumn h68 hP Q i) := by
      simp only [σ, dif_pos hd.out]
    rw [h]
    exact Classical.choose_spec (exists_heatSelectedSkewCorrectorColumn h68 hP Q i)
  let S : ∀ {d : ℕ} {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
      FieldPair d → Vec d → Mat d := fun {d} {L} {r₀} Q R i ω x =>
    σ Q i ω x - mollifierMatrixAverage R (σ Q i ω)
  refine ⟨u, S, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd L r₀ Q R hR i
    have h : (fun ω (x : Point d) => u Q R i ω x.ofLp) = Classical.choose
        (exists_normalizedCanonicalScalarCorrector hP Q i (canonicalSourceMollifier d) R hR 0) := by
      funext ω x
      simp only [u, dif_pos (And.intro hd.out hR), WithLp.toLp_ofLp]
    rw [h]
    exact Classical.choose_spec
      (exists_normalizedCanonicalScalarCorrector hP Q i (canonicalSourceMollifier d) R hR 0)
  · intro d hd L r₀ Q R hR i
    exact (mollifierNormalized_skew_properties Q i (hσspec Q i).1 (hσspec Q i).2.1
      (hσspec Q i).2.2.1 (hσspec Q i).2.2.2 hR).1
  · intro d hd L r₀ Q R hR i j k
    exact (mollifierNormalized_skew_properties Q i (hσspec Q i).1 (hσspec Q i).2.1
      (hσspec Q i).2.2.1 (hσspec Q i).2.2.2 hR).2.1 j k
  · intro d hd L r₀ Q R hR i ω x
    exact (mollifierNormalized_skew_properties Q i (hσspec Q i).1 (hσspec Q i).2.1
      (hσspec Q i).2.2.1 (hσspec Q i).2.2.2 hR).2.2.1 ω x
  · intro d hd L r₀ Q R hR i j k
    exact (mollifierNormalized_skew_properties Q i (hσspec Q i).1 (hσspec Q i).2.1
      (hσspec Q i).2.2.1 (hσspec Q i).2.2.2 hR).2.2.2.1 j k

end EinsteinRelation.Correctors
