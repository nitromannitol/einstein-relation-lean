import EinsteinFull.Calculus.U5SelfAdjointSemigroupAnalytic
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS1PastKernel
import EinsteinFull.Calculus.SunaS6GMPEnvironment
import Mathlib.Analysis.Analytic.Uniqueness

open MeasureTheory
open scoped NNReal
open EinsteinRelation EinsteinRelation.External.GantertSection7Support

namespace EinsteinFull

universe u

/-- Conditional analytic consumer for the actual supplied killed evolution. -/
theorem s6_requested_killed_orbit_analytic_of_semigroup_analytic
    (hana : ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hzero : T 0 = ContinuousLinearMap.id ℝ E)
    (hadd : ∀ s t, T (s+t) = (T s).comp (T t))
    (hcont : ∀ f, Continuous (fun t : ℝ≥0 => T t f))
    (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
    (hbound : ∀ t, ‖T t‖ ≤ 1) (g v : E),
    AnalyticOnNhd ℝ (fun t : ℝ => inner ℝ v (T t.toNNReal g)) (Set.Ioi 0))
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (g v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    AnalyticOnNhd ℝ (fun t : ℝ => inner ℝ v
      (gmpKilledL2Operator G U hU t.toNNReal g)) (Set.Ioi 0) := by
  let E := physicalZeroBoundaryL2 U hd ω lam L hω
  let T := gmpKilledInteriorOperator G U hU
  let p (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) : E :=
    ⟨physicalZeroBoundaryProjection U hd ω lam L hω f,
      physicalZeroBoundaryProjection_mem U hd ω lam L hω f⟩
  have hz : T 0 = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro f
    exact gmpKilledInteriorOperator_zero G U hU f
  have hb (t : ℝ≥0) : ‖T t‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    simpa only [one_mul] using gmpKilledInteriorOperator_norm_le G U hU t f
  letI : InnerProductSpace ℝ (ULift.{u} E) :=
    InnerProductSpace.induced (ULift.moduleEquiv (R := ℝ) (M := E)).toLinearMap
  let I : ULift.{u} E ≃L[ℝ] E := ContinuousLinearEquiv.ulift
  let S (t : ℝ≥0) : ULift.{u} E →L[ℝ] ULift.{u} E :=
    I.symm.toContinuousLinearMap.comp ((T t).comp I.toContinuousLinearMap)
  have sz : S 0 = ContinuousLinearMap.id ℝ (ULift.{u} E) := by
    apply ContinuousLinearMap.ext
    intro f
    change ULift.up (T 0 f.down) = f
    rw [hz]
    rfl
  have sa (s t : ℝ≥0) : S (s+t) = (S s).comp (S t) := by
    apply ContinuousLinearMap.ext
    intro f
    change ULift.up (T (s+t) f.down) = ULift.up (T s (T t f.down))
    have hst : T (s+t) = (T s).comp (T t) :=
      gmpKilledInteriorOperator_add_time G U hU s t
    rw [hst]
    rfl
  have sc (f : ULift.{u} E) : Continuous (fun t : ℝ≥0 => S t f) := by
    exact I.symm.continuous.comp (continuous_gmpKilledInteriorOperator_apply G U hU f.down)
  have ss (t : ℝ≥0) (a b : ULift.{u} E) :
      inner ℝ a (S t b) = inner ℝ (S t a) b := by
    exact ((gmpKilledInteriorOperator_isSymmetric G U hU t) a.down b.down).symm
  have sb (t : ℝ≥0) : ‖S t‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    simp only [one_mul]
    change ‖T t f.down‖ ≤ ‖f.down‖
    exact gmpKilledInteriorOperator_norm_le G U hU t f.down
  have ha := hana S sz sa sc ss sb (ULift.up (p g)) (ULift.up (p v))
  change AnalyticOnNhd ℝ (fun t : ℝ => inner ℝ (p v) (T t.toNNReal (p g)))
    (Set.Ioi 0) at ha
  have heq : (fun t : ℝ => inner ℝ (p v) (T t.toNNReal (p g))) =
      (fun t : ℝ => inner ℝ v (gmpKilledL2Operator G U hU t.toNNReal g)) := by
    funext t
    change inner ℝ (physicalZeroBoundaryProjection U hd ω lam L hω v)
      (gmpKilledL2 G U hU t.toNNReal (physicalZeroBoundaryProjection U hd ω lam L hω g)) = _
    rw [gmpKilledL2_projection]
    rw [← gmpKilledL2_zero G U hU v]
    change inner ℝ (gmpKilledL2Operator G U hU 0 v)
      (gmpKilledL2Operator G U hU t.toNNReal g) = _
    have hs := gmpKilledL2Operator_isSymmetric G U hU 0 v
      (gmpKilledL2Operator G U hU t.toNNReal g)
    change inner ℝ (gmpKilledL2Operator G U hU 0 v)
      (gmpKilledL2Operator G U hU t.toNNReal g) =
      inner ℝ v (gmpKilledL2Operator G U hU 0
        (gmpKilledL2Operator G U hU t.toNNReal g)) at hs
    rw [hs, ← ContinuousLinearMap.comp_apply, ← gmpKilledL2Operator_add_time, zero_add]
  rw [← heq]
  exact ha

/-- The actual supplied killed operator has a nonnegative quadratic form. -/
theorem s6_killed_operator_quadratic_nonneg
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    0 ≤ inner ℝ f (gmpKilledL2Operator G U hU t f) := by
  exact s6_symmetric_semigroup_quadratic_nonneg (gmpKilledL2Operator G U hU)
    (gmpKilledL2Operator_add_time G U hU)
    (fun t u v => (gmpKilledL2Operator_isSymmetric G U hU t u v).symm) t f


/-- An analytic scalar orbit that vanishes on an interval vanishes at every positive time. -/
theorem s6_analytic_scalar_orbit_zero_on_positive_times
    (f : ℝ → ℝ) (hf : AnalyticOnNhd ℝ f (Set.Ioi 0))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hz : ∀ t ∈ Set.Ioo a b, f t = 0) : ∀ t ∈ Set.Ioi 0, f t = 0 := by
  have hm : (a + b) / 2 ∈ Set.Ioo a b := by constructor <;> linarith
  have hn : f =ᶠ[nhds ((a + b) / 2)] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hm] with t ht
    exact hz t ht
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_Ioi (lt_trans ha hm.1) hn

/-- Conditional zero propagation for the scalar orbit of the actual supplied killed operator. -/
theorem s6_supplied_killed_scalar_orbit_zero_on_positive_times
    (hana : ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (T : ℝ≥0 → E →L[ℝ] E)
      (hzero : T 0 = ContinuousLinearMap.id ℝ E)
      (hadd : ∀ s t, T (s+t) = (T s).comp (T t))
      (hcont : ∀ f, Continuous (fun t : ℝ≥0 => T t f))
      (hsym : ∀ t u v, inner ℝ u (T t v) = inner ℝ (T t u) v)
      (hbound : ∀ t, ‖T t‖ ≤ 1) (g v : E),
      AnalyticOnNhd ℝ (fun t : ℝ => inner ℝ v (T t.toNNReal g)) (Set.Ioi 0))
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (g v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hz : ∀ t ∈ Set.Ioo a b, inner ℝ v (gmpKilledL2Operator G U hU t.toNNReal g) = 0) :
    ∀ t : ℝ, t ∈ Set.Ioi 0 → inner ℝ v (gmpKilledL2Operator G U hU t.toNNReal g) = 0 := by
  exact s6_analytic_scalar_orbit_zero_on_positive_times _
    (s6_requested_killed_orbit_analytic_of_semigroup_analytic hana hd L hL ω hω lam h0 h1
      G U hU g v) a b ha hab hz

#print axioms s6_killed_operator_quadratic_nonneg

#print axioms s6_requested_killed_orbit_analytic_of_semigroup_analytic

/-- Scalar pairings of the actual supplied killed evolution are analytic at positive times. -/
theorem s6_requested_killed_orbit_analytic
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (g v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    AnalyticOnNhd ℝ (fun t : ℝ => inner ℝ v
      (gmpKilledL2Operator G U hU t.toNNReal g)) (Set.Ioi 0) := by
  exact s6_requested_killed_orbit_analytic_of_semigroup_analytic.{0}
    (fun T hz ha hc hs hb g v =>
      u5_symmetric_contraction_semigroup_scalar_analytic T hz ha hc hs hb g v)
    hd L hL ω hω lam h0 h1 G U hU g v


end EinsteinFull
