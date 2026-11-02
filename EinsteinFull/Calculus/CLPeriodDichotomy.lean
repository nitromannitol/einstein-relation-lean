import EinsteinFull.Calculus.CLTranslationMixing
import EinsteinFull.Calculus.S4PolishSupport
import Mathlib.Order.Filter.CountableSeparatingOn

/-!
# Periods of a finite-range environment

The periods `x` with `translate x ω = ω` of a field pair form a closed set that does not change
under translation. Under a stationary ergodic law the event that some period lies in a given
compact set is trivial, so the period set is almost surely one fixed closed set. If it contains
a nonzero vector, every window event is independent of one of its translates and equal to it,
so the law is trivial and the environment is almost surely one constant field. Otherwise almost
every environment is aperiodic.
-/

open MeasureTheory Filter
open scoped Topology symmDiff

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

private theorem localSigma_translate_preimage_ball' (x : Vec d) {R : ℝ}
    {B : Set (FieldPair d)} (hB : MeasurableSet[localSigma (Metric.ball (0 : Vec d) R)] B) :
    MeasurableSet[localSigma (Metric.ball x R)] (translate x ⁻¹' B) := by
  have himage : (fun y : Vec d => x + y) '' Metric.ball (0 : Vec d) R ⊆ Metric.ball x R := by
    rintro z ⟨y, hy, rfl⟩
    apply Metric.mem_ball.mpr
    have hy' : dist y (0 : Vec d) < R := Metric.mem_ball.mp hy
    simpa [dist_eq_norm, add_comm, add_left_comm, add_assoc] using hy'
  have hlocal := Probability.measurable_translate_local x (Metric.ball (0 : Vec d) R)
  exact (Probability.localSigma_mono himage) _ (hlocal hB)

private theorem abs_coord_le_euclideanNorm' (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  have hsq : v i * v i ≤ ∑ j, v j * v j :=
    Finset.single_le_sum (f := fun j => v j * v j)
      (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact hsq

/-- A window event is independent of its translate by any vector with one coordinate of size at
least the range plus twice the window radius plus one. -/
theorem environmentLaw_indep_window_translate_coord (Q : EnvironmentLaw d Λ₀ r₀) {R : ℝ}
    {x : Vec d} (i : Fin d) (hx : r₀ + 2 * R + 1 ≤ |x i|) (B : Set (FieldPair d))
    (hB : MeasurableSet[localSigma (Metric.ball (0 : Vec d) R)] B) :
    Q.measure (B ∩ translate x ⁻¹' B) = Q.measure B * Q.measure B := by
  let U : Set (Vec d) := Metric.ball (0 : Vec d) R
  let W : Set (Vec d) := Metric.ball x R
  have hgap : ∃ t : ℝ, r₀ < t ∧ ∀ y ∈ U, ∀ z ∈ W, t ≤ euclideanNorm (y - z) := by
    refine ⟨r₀ + 1, by linarith, ?_⟩
    intro y hy z hz
    have hyNorm : ‖y‖ < R := by simpa [U, dist_eq_norm] using Metric.mem_ball.mp hy
    have hzNorm : ‖z - x‖ < R := by simpa [W, dist_eq_norm] using Metric.mem_ball.mp hz
    have hyCoord : |y i| < R := by
      have := (norm_le_pi_norm y i).trans_lt hyNorm
      simpa only [Real.norm_eq_abs] using this
    have hzCoord : |z i - x i| < R := by
      have := (norm_le_pi_norm (z - x) i).trans_lt hzNorm
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using this
    have hlower : r₀ + 1 ≤ |z i - y i| := by
      have h1 : |x i| ≤ |z i - y i| + |z i - x i| + |y i| := by
        calc |x i| = |(z i - y i) - (z i - x i) + y i| := by ring_nf
          _ ≤ |(z i - y i) - (z i - x i)| + |y i| := abs_add_le _ _
          _ ≤ |z i - y i| + |z i - x i| + |y i| := by
            gcongr
            exact abs_sub _ _
      linarith
    calc
      r₀ + 1 ≤ |z i - y i| := hlower
      _ = |(y - z) i| := by simp [Pi.sub_apply, abs_sub_comm]
      _ ≤ euclideanNorm (y - z) := abs_coord_le_euclideanNorm' (y - z) i
  have hind := Q.finiteRange U W Metric.isOpen_ball.measurableSet
    Metric.isOpen_ball.measurableSet hgap
  have hlocal : MeasurableSet[localSigma W] (translate x ⁻¹' B) :=
    localSigma_translate_preimage_ball' x hB
  have hfac := (ProbabilityTheory.Indep_iff (localSigma U) (localSigma W) Q.measure).1 hind
    B (translate x ⁻¹' B) hB hlocal
  have hBambient : MeasurableSet B := Probability.localSigma_le_borel U B hB
  have hpre : Q.measure (translate x ⁻¹' B) = Q.measure B := by
    rw [← Measure.map_apply (Probability.measurable_translate x) hBambient, Q.stationary]
  rw [hpre] at hfac
  exact hfac

private theorem eq_zero_or_one_of_eq_mul_self {a : ENNReal} (ha : a ≤ 1) (h : a = a * a) :
    a = 0 ∨ a = 1 := by
  have hfin : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hr : a.toReal = a.toReal * a.toReal := by
    rw [← ENNReal.toReal_mul, ← h]
  have h' : a.toReal * (a.toReal - 1) = 0 := by rw [mul_sub, mul_one]; linarith
  rcases mul_eq_zero.1 h' with h0 | h1
  · left
    exact (ENNReal.toReal_eq_zero_iff _).1 h0 |>.resolve_right hfin
  · right
    rw [← ENNReal.ofReal_toReal hfin, show a.toReal = 1 by linarith, ENNReal.ofReal_one]

/-- An almost-sure nonzero period makes every event of the environment law trivial. -/
theorem environmentLaw_trivial_of_period (Q : EnvironmentLaw d Λ₀ r₀) {p : Vec d}
    (hp : p ≠ 0) (hper : ∀ᵐ ω ∂Q.measure, translate p ω = ω) {U : Set (FieldPair d)}
    (hU : MeasurableSet U) : Q.measure U = 0 ∨ Q.measure U = 1 := by
  have hmul : ∀ m : ℕ, ∀ᵐ ω ∂Q.measure, translate (m • p) ω = ω := by
    intro m
    induction m with
    | zero => exact ae_of_all _ fun ω => by simp
    | succ m ih =>
      filter_upwards [ih, hper] with ω h1 h2
      rw [succ_nsmul, ← translate_add, h2, h1]
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hp (funext hcon)
  -- window events are trivial
  have hwin : ∀ (R : ℝ) (B : Set (FieldPair d)),
      MeasurableSet[localSigma (Metric.ball (0 : Vec d) R)] B →
      Q.measure B = 0 ∨ Q.measure B = 1 := by
    intro R B hB
    obtain ⟨m, hm⟩ := exists_nat_ge ((r₀ + 2 * R + 1) / |p i|)
    have hpos : 0 < |p i| := abs_pos.2 hi
    have hcoord : r₀ + 2 * R + 1 ≤ |(m • p) i| := by
      rw [Pi.smul_apply, nsmul_eq_mul, abs_mul, Nat.abs_cast]
      rwa [div_le_iff₀ hpos] at hm
    have hind := environmentLaw_indep_window_translate_coord Q i hcoord B hB
    have hBm : MeasurableSet B := Probability.localSigma_le_borel _ B hB
    have hae : B ∩ translate (m • p) ⁻¹' B =ᵐ[Q.measure] B := by
      filter_upwards [hmul m] with ω hω
      change (ω ∈ B ∧ translate (m • p) ω ∈ B) = (ω ∈ B)
      rw [hω, and_self]
    have hself : Q.measure (B ∩ translate (m • p) ⁻¹' B) = Q.measure B := measure_congr hae
    exact eq_zero_or_one_of_eq_mul_self prob_le_one (hself.symm.trans hind)
  -- every event is approximated by window events
  have hclose : ∀ ε : ℝ, 0 < ε →
      (Q.measure U).toReal < ε ∨ 1 - ε < (Q.measure U).toReal := by
    intro ε hε
    obtain ⟨n, B, hB, happrox⟩ :=
      Localization.environmentLaw_exists_boundedObservation_approx Q U hU ε hε
    have hBlocal : MeasurableSet[localSigma (Metric.ball (0 : Vec d) ((n : ℝ) + 1))] B := hB
    have hBm : MeasurableSet B := Probability.localSigma_le_borel _ B hB
    have he : (Q.measure (U ∆ B)).toReal < ε := ENNReal.toReal_lt_of_lt_ofReal happrox
    have h1 : (Q.measure U).toReal ≤ (Q.measure B).toReal + (Q.measure (U ∆ B)).toReal := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      apply ENNReal.toReal_mono (by finiteness)
      calc Q.measure U ≤ Q.measure (B ∪ U ∆ B) := measure_mono fun ω hω => by
            by_cases hb : ω ∈ B
            · exact Or.inl hb
            · exact Or.inr (Or.inl ⟨hω, hb⟩)
        _ ≤ _ := measure_union_le _ _
    have h2 : (Q.measure B).toReal ≤ (Q.measure U).toReal + (Q.measure (U ∆ B)).toReal := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      apply ENNReal.toReal_mono (by finiteness)
      calc Q.measure B ≤ Q.measure (U ∪ U ∆ B) := measure_mono fun ω hω => by
            by_cases hu : ω ∈ U
            · exact Or.inl hu
            · exact Or.inr (Or.inr ⟨hω, hu⟩)
        _ ≤ _ := measure_union_le _ _
    rcases hwin _ B hBlocal with h0 | h1'
    · left
      rw [h0, ENNReal.toReal_zero] at h1
      linarith
    · right
      rw [h1', ENNReal.toReal_one] at h2
      linarith
  have hp0 : 0 ≤ (Q.measure U).toReal := ENNReal.toReal_nonneg
  have hp1 : (Q.measure U).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := Q.measure) (s := U))
    rwa [ENNReal.toReal_one] at this
  by_cases hz : (Q.measure U).toReal = 0
  · left
    exact (ENNReal.toReal_eq_zero_iff _).1 hz |>.resolve_right (measure_ne_top _ _)
  · right
    have hpos : 0 < (Q.measure U).toReal := lt_of_le_of_ne hp0 (Ne.symm hz)
    have hone : (Q.measure U).toReal = 1 := by
      by_contra hne
      have hlt : (Q.measure U).toReal < 1 := lt_of_le_of_ne hp1 hne
      let ε : ℝ := min ((Q.measure U).toReal) (1 - (Q.measure U).toReal)
      have hε : 0 < ε := lt_min hpos (by linarith)
      rcases hclose ε hε with h | h
      · exact absurd h (not_lt.2 (min_le_left _ _))
      · have : ε ≤ 1 - (Q.measure U).toReal := min_le_right _ _
        linarith
    rw [← ENNReal.ofReal_toReal (measure_ne_top Q.measure U), hone, ENNReal.ofReal_one]

/-- An almost-sure nonzero period forces the environment to be almost surely one constant
field. -/
theorem environmentLaw_eq_const_of_period (Q : EnvironmentLaw d Λ₀ r₀) {p : Vec d}
    (hp : p ≠ 0) (hper : ∀ᵐ ω ∂Q.measure, translate p ω = ω) :
    ∃ c : FieldPair d, (∀ x, translate x c = c) ∧ ∀ᵐ ω ∂Q.measure, ω = c := by
  have : Nonempty (FieldPair d) := ⟨(ContinuousMap.const _ 0, ContinuousMap.const _ 0)⟩
  let : PolishSpace (FieldPair d) := fieldPair_polish d
  have : MeasurableSpace.CountablySeparated (FieldPair d) := inferInstance
  have : HasCountableSeparatingOn (FieldPair d) MeasurableSet Set.univ :=
    MeasurableSpace.CountablySeparated.countably_separated
  obtain ⟨c, hc⟩ := exists_eventuallyEq_const_of_forall_separating MeasurableSet
    (l := ae Q.measure) (f := id) fun U hU => by
      rcases environmentLaw_trivial_of_period Q hp hper hU with h0 | h1
      · right
        exact measure_eq_zero_iff_ae_notMem.1 h0
      · left
        rw [← prob_compl_eq_zero_iff hU] at h1
        exact mem_ae_iff.2 h1
  have hc' : ∀ᵐ ω ∂Q.measure, ω = c := hc
  refine ⟨c, fun x => ?_, hc'⟩
  have hmeas : MeasurableSet {ω : FieldPair d | ω = c} := measurableSet_singleton c
  have htr : ∀ᵐ ω ∂Q.measure, translate x ω = c := by
    have h := hc'
    rw [← Q.stationary x] at h
    exact ae_of_ae_map (Probability.measurable_translate x).aemeasurable h
  obtain ⟨ω, h1, h2⟩ := (hc'.and htr).exists
  rw [h1] at h2
  exact h2

/-- The event that some period lies in a given set. -/
def periodHit (K : Set (Vec d)) : Set (FieldPair d) := {ω | ∃ x ∈ K, translate x ω = ω}

theorem isClosed_periodHit {K : Set (Vec d)} (hK : IsCompact K) :
    IsClosed (periodHit (d := d) K) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : Set (K × FieldPair d) := {q | translate (q.1 : Vec d) q.2 = q.2}
  have hC : IsClosed C := isClosed_eq
    (Probability.continuous_translate.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) continuous_snd
  have himg : periodHit K = Prod.snd '' C := by
    ext ω
    constructor
    · rintro ⟨x, hx, hxω⟩
      exact ⟨(⟨x, hx⟩, ω), hxω, rfl⟩
    · rintro ⟨⟨x, ω'⟩, hq, rfl⟩
      exact ⟨x, x.2, hq⟩
  rw [himg]
  exact isClosedMap_snd_of_compactSpace C hC

/-- A translate has the same periods. -/
theorem translate_translate_eq_self_iff (x y : Vec d) (ω : FieldPair d) :
    translate x (translate y ω) = translate y ω ↔ translate x ω = ω := by
  constructor
  · intro h
    have h1 : translate (-y) (translate x (translate y ω)) = translate x ω := by
      rw [translate_add, translate_add, show -y + x + y = x by abel]
    have h2 : translate (-y) (translate y ω) = ω := by
      rw [translate_add, neg_add_cancel, translate_zero]
    rw [← h1, h, h2]
  · intro h
    rw [translate_add, add_comm, ← translate_add, h]

theorem translate_mem_periodHit_iff (K : Set (Vec d)) (y : Vec d) (ω : FieldPair d) :
    translate y ω ∈ periodHit K ↔ ω ∈ periodHit K := by
  simp only [periodHit, Set.mem_ofPred_eq, translate_translate_eq_self_iff]

/-- A rational closed ball around a point, inside a given open ball. -/
theorem exists_ratClosedBall (x : Vec d) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : (Fin d → ℚ) × ℚ, 0 < (b.2 : ℝ) ∧
      x ∈ Metric.closedBall (fun j => (b.1 j : ℝ)) (b.2 : ℝ) ∧
      Metric.closedBall (fun j => (b.1 j : ℝ)) (b.2 : ℝ) ⊆ Metric.ball x ε := by
  obtain ⟨r, hr0, hr⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 3 by positivity)
  have hq : ∀ j, ∃ q : ℚ, |x j - q| < r := by
    intro j
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x j - r < x j by linarith)
    exact ⟨q, by rw [abs_lt]; constructor <;> linarith⟩
  choose q hq using hq
  have hdist : dist x (fun j => (q j : ℝ)) < r := by
    rw [dist_pi_lt_iff (by exact_mod_cast hr0)]
    intro j
    simpa [Real.dist_eq] using hq j
  refine ⟨(q, r), by exact_mod_cast hr0, ?_, ?_⟩
  · exact Metric.mem_closedBall.2 (dist_comm x _ ▸ hdist.le)
  · intro y hy
    have hy' : dist y (fun j => (q j : ℝ)) ≤ r := Metric.mem_closedBall.1 hy
    apply Metric.mem_ball.2
    calc dist y x ≤ dist y (fun j => (q j : ℝ)) + dist (fun j => (q j : ℝ)) x :=
          dist_triangle _ _ _
      _ < r + r := by
          have := dist_comm x (fun j => (q j : ℝ)) ▸ hdist
          linarith
      _ < ε := by linarith

/-- Under an environment law, either almost every environment is aperiodic, or the law is
concentrated on one constant field. -/
theorem environmentLaw_period_dichotomy (Q : EnvironmentLaw d Λ₀ r₀) (hd : 2 ≤ d) :
    (∀ᵐ ω ∂Q.measure, ∀ x, translate x ω = ω → x = 0) ∨
      ∃ c : FieldPair d, (∀ x, translate x c = c) ∧ ∀ᵐ ω ∂Q.measure, ω = c := by
  let ball : (Fin d → ℚ) × ℚ → Set (Vec d) := fun b =>
    Metric.closedBall (fun j => (b.1 j : ℝ)) (b.2 : ℝ)
  let H : (Fin d → ℚ) × ℚ → Set (FieldPair d) := fun b => periodHit (ball b)
  have hHm : ∀ b, MeasurableSet (H b) := fun b =>
    (isClosed_periodHit (isCompact_closedBall _ _)).measurableSet
  have htriv : ∀ b, Q.measure (H b) = 0 ∨ Q.measure (H b) = 1 := fun b =>
    Localization.environmentLaw_translation_ergodic Q hd (H b) (hHm b) fun x =>
      ae_of_all _ fun ω => translate_mem_periodHit_iff _ x ω
  by_cases hall : ∀ b, 0 ∉ ball b → Q.measure (H b) = 0
  · left
    have hae : ∀ᵐ ω ∂Q.measure, ∀ b, 0 ∉ ball b → ω ∉ H b := by
      rw [ae_all_iff]
      intro b
      by_cases h0 : 0 ∈ ball b
      · exact ae_of_all _ fun _ h => absurd h0 h
      · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hall b h0)] with ω hω _ using hω
    filter_upwards [hae] with ω hω x hx
    by_contra hx0
    have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    obtain ⟨b, -, hxb, hsub⟩ := exists_ratClosedBall x hpos
    have h0 : 0 ∉ ball b := by
      intro h
      have := hsub h
      rw [Metric.mem_ball, dist_comm, dist_zero_right] at this
      exact lt_irrefl _ this
    exact hω b h0 ⟨x, hxb, hx⟩
  · right
    push Not at hall
    obtain ⟨b₀, hb₀, hHb₀⟩ := hall
    have hone : Q.measure (H b₀) = 1 := (htriv b₀).resolve_left hHb₀
    have hG : ∀ᵐ ω ∂Q.measure, ∀ b, (ω ∈ H b ↔ Q.measure (H b) = 1) := by
      rw [ae_all_iff]
      intro b
      rcases htriv b with h0 | h1
      · filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
        simp only [hω, false_iff, h0]
        exact zero_ne_one
      · have hc : Q.measure (H b)ᶜ = 0 := by
          rw [prob_compl_eq_zero_iff (hHm b)]
          exact h1
        filter_upwards [mem_ae_iff.2 hc] with ω hω
        simp only [h1, iff_true]
        exact hω
    obtain ⟨ω₁, hω₁G⟩ := hG.exists
    obtain ⟨p, hpb, hpω⟩ := (hω₁G b₀).2 hone
    have hp0 : p ≠ 0 := fun h => hb₀ (h ▸ hpb)
    refine environmentLaw_eq_const_of_period Q hp0 ?_
    filter_upwards [hG] with ω hω
    by_contra hne
    have hclosed : IsClosed {x : Vec d | translate x ω = ω} :=
      isClosed_eq (Probability.continuous_translate.comp
        (continuous_id.prodMk continuous_const)) continuous_const
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hclosed.isOpen_compl p hne
    obtain ⟨b, -, hpb', hsub⟩ := exists_ratClosedBall p hε
    have hω₁b : ω₁ ∈ H b := ⟨p, hpb', hpω⟩
    have hωb : ω ∈ H b := (hω b).2 ((hω₁G b).1 hω₁b)
    obtain ⟨x, hxb, hxω⟩ := hωb
    exact hball (hsub hxb) hxω

end EinsteinFull
