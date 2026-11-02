import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Localization.JointObservationSigma
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Stationarity and joint finite range in Assumption 1.1(S4)--(S5) imply
translation ergodicity for the actual physical compact-open field pair. The proof
uses bounded joint local observations and finite-range independence. -/

open MeasureTheory
open scoped Topology symmDiff

namespace EinsteinRelation.Localization

/-- The literal translation action is jointly Borel measurable, as required for
the continuous `ℝ^d` action in GMP Section 7. Its identity and composition laws
are `translate_zero` and `translate_add` on the physical field-pair carrier. -/
theorem physicalTranslation_jointlyMeasurable {d : ℕ} :
    Measurable (fun p : Vec d × FieldPair d => translate p.1 p.2) :=
  Probability.continuous_translate.measurable

private def observationWindow {d : ℕ} (n : ℕ) : Set (Vec d) :=
  Metric.ball 0 ((n : ℝ) + 1)

/-- Events observable in some bounded spatial window of the joint field. -/
private def boundedObservationEvents {d : ℕ} : Set (Set (FieldPair d)) :=
  {s | ∃ n : ℕ, MeasurableSet[localSigma (observationWindow n)] s}

private theorem observationWindow_mono {d : ℕ} {n m : ℕ} (hnm : n ≤ m) :
    observationWindow (d := d) n ⊆ observationWindow m := by
  intro x hx
  change dist x (0 : Vec d) < (n : ℝ) + 1 at hx
  change dist x (0 : Vec d) < (m : ℝ) + 1
  exact lt_of_lt_of_le hx (by exact_mod_cast Nat.add_le_add_right hnm 1)

private theorem boundedObservationEvents_isSetAlgebra {d : ℕ} :
    IsSetAlgebra (boundedObservationEvents (d := d)) := by
  constructor
  · exact ⟨0, @MeasurableSet.empty (FieldPair d) (localSigma (observationWindow 0))⟩
  · intro s hs
    rcases hs with ⟨n, hn⟩
    exact ⟨n, hn.compl⟩
  · intro s t hs ht
    rcases hs with ⟨n, hn⟩
    rcases ht with ⟨m, hm⟩
    refine ⟨max n m, ?_⟩
    apply MeasurableSet.union
    · exact (Probability.localSigma_mono (observationWindow_mono (Nat.le_max_left n m))) s hn
    · exact (Probability.localSigma_mono (observationWindow_mono (Nat.le_max_right n m))) t hm

private theorem boundedObservationEvents_generateFrom_eq {d : ℕ} :
    MeasurableSpace.generateFrom (boundedObservationEvents (d := d)) =
      (inferInstance : MeasurableSpace (FieldPair d)) := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    rcases hs with ⟨n, hn⟩
    exact Probability.localSigma_le_borel (observationWindow n) s hn
  · rw [← localSigma_univ_eq_borel]
    unfold localSigma
    apply iSup_le
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (dist x.1 (0 : Vec d))
    have hball :
        localSigma (observationWindow (d := d) n) ≤
          MeasurableSpace.generateFrom (boundedObservationEvents (d := d)) := by
      intro s hs
      exact MeasurableSpace.measurableSet_generateFrom ⟨n, hs⟩
    have hxwindow : x.1 ∈ observationWindow (d := d) n := by
      apply Metric.mem_ball.mpr
      exact lt_trans hn (by exact_mod_cast (Nat.lt_succ_self n))
    exact le_trans (le_iSup_of_le ⟨x.1, hxwindow⟩ le_rfl) hball

theorem environmentLaw_boundedObservationEvents_measureDense {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : Q.measure.MeasureDense
      (boundedObservationEvents (d := d)) := by
  apply Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite Q.measure
      boundedObservationEvents_isSetAlgebra
  exact boundedObservationEvents_generateFrom_eq.symm

theorem environmentLaw_exists_boundedObservation_approx {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (A : Set (FieldPair d))
    (hA : MeasurableSet A) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ B : Set (FieldPair d),
      MeasurableSet[localSigma (observationWindow n)] B ∧
      Q.measure (A ∆ B) < ENNReal.ofReal ε := by
  obtain ⟨B, hB, happrox⟩ :=
    (environmentLaw_boundedObservationEvents_measureDense Q).approx A hA (by finiteness) ε hε
  rcases hB with ⟨n, hn⟩
  exact ⟨n, B, hn, happrox⟩

private theorem coordinate_abs_le_euclideanNorm {d : ℕ} (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  have hsq : v i * v i ≤ ∑ j, v j * v j :=
    Finset.single_le_sum (f := fun j => v j * v j)
      (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact hsq

private theorem local_preimage_ball {d : ℕ} {R : ℝ} (x : Vec d)
    {B : Set (FieldPair d)}
    (hB : MeasurableSet[localSigma (Metric.ball (0 : Vec d) R)] B) :
    MeasurableSet[localSigma (Metric.ball x R)] (translate x ⁻¹' B) := by
  have himage : (fun y : Vec d => x + y) '' Metric.ball (0 : Vec d) R ⊆
      Metric.ball x R := by
    rintro z ⟨y, hy, rfl⟩
    apply Metric.mem_ball.mpr
    have hy' : dist y (0 : Vec d) < R := Metric.mem_ball.mp hy
    simpa [dist_eq_norm, add_comm, add_left_comm, add_assoc] using hy'
  have hlocal := Probability.measurable_translate_local x
      (Metric.ball (0 : Vec d) R)
  exact (Probability.localSigma_mono himage) _ (hlocal hB)

theorem environmentLaw_independent_window_translate {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (i : Fin d)
    (B : Set (FieldPair d))
    (hB : MeasurableSet[localSigma (Metric.ball (0 : Vec d) R)] B) :
    Q.measure (B ∩ translate ((r₀ + 2 * R + 1) • unitVector i) ⁻¹' B) =
      Q.measure B * Q.measure B := by
  let x : Vec d := (r₀ + 2 * R + 1) • unitVector i
  let U : Set (Vec d) := Metric.ball (0 : Vec d) R
  let W : Set (Vec d) := Metric.ball x R
  have hgap : ∃ s : ℝ, r₀ < s ∧ ∀ y ∈ U, ∀ z ∈ W,
      s ≤ euclideanNorm (y - z) := by
    refine ⟨r₀ + 1, by linarith [Q.range_parameter], ?_⟩
    intro y hy z hz
    have hyNorm : ‖y‖ < R := by simpa [U, dist_eq_norm] using Metric.mem_ball.mp hy
    have hzNorm : ‖z - x‖ < R := by simpa [W, dist_eq_norm] using Metric.mem_ball.mp hz
    have hyCoord : |y i| < R := by
      have := (norm_le_pi_norm y i).trans_lt hyNorm
      simpa only [Real.norm_eq_abs] using this
    have hzCoord : |z i - x i| < R := by
      have := (norm_le_pi_norm (z - x) i).trans_lt hzNorm
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using this
    have hxCoord : x i = r₀ + 2 * R + 1 := by simp [x, unitVector]
    have hdecomp : z i - y i = (r₀ + 2 * R + 1) + (z i - x i) - y i := by
      rw [← hxCoord]
      ring
    have hlower : r₀ + 1 ≤ z i - y i := by
      have hzlo : -(R) < z i - x i := (abs_lt.mp hzCoord).1
      have hyhi : y i < R := (abs_lt.mp hyCoord).2
      nlinarith
    calc
      r₀ + 1 ≤ |z i - y i| := le_trans hlower (le_abs_self _)
      _ = |(y - z) i| := by simp [Pi.sub_apply, abs_sub_comm]
      _ ≤ euclideanNorm (y - z) := coordinate_abs_le_euclideanNorm (y - z) i
  have hind := Q.finiteRange U W Metric.isOpen_ball.measurableSet
      Metric.isOpen_ball.measurableSet hgap
  have hlocal :
      MeasurableSet[localSigma W]
        (translate ((r₀ + 2 * R + 1) • unitVector i) ⁻¹' B) := by
    exact local_preimage_ball ((r₀ + 2 * R + 1) • unitVector i) hB
  have hfac := (ProbabilityTheory.Indep_iff (localSigma U) (localSigma W) Q.measure).1 hind
      B (translate ((r₀ + 2 * R + 1) • unitVector i) ⁻¹' B) hB hlocal
  have hBambient : MeasurableSet B := Probability.localSigma_le_borel U B hB
  have hmap := Probability.measurable_translate ((r₀ + 2 * R + 1) • unitVector i)
  have hpre : Q.measure
      (translate ((r₀ + 2 * R + 1) • unitVector i) ⁻¹' B) = Q.measure B := by
    rw [← Measure.map_apply hmap hBambient, Q.stationary]
  rw [hpre] at hfac
  exact hfac

private theorem symmDiff_inter_subset {α : Type*} (A B C D : Set α) :
    (A ∩ B) ∆ (C ∩ D) ⊆ (A ∆ C) ∪ (B ∆ D) := by
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union] at *
  tauto

/-- The actual physical translation action is ergodic under Assumption 1.1(S4)--(S5).
This is the zero-one event formulation for the continuous action `translate` on the
full compact-open Borel carrier, not an assumption added to the environment law. -/
theorem environmentLaw_translation_ergodic {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hd : 2 ≤ d) (A : Set (FieldPair d))
    (hA : MeasurableSet A)
    (hInv : ∀ x : Vec d, ∀ᵐ ω ∂Q.measure,
      (translate x ω ∈ A ↔ ω ∈ A)) :
    Q.measure A = 0 ∨ Q.measure A = 1 := by
  let p : ℝ := (Q.measure A).toReal
  have hsmall : ∀ ε : ℝ, 0 < ε → |p - p * p| ≤ 4 * ε := by
    intro ε hε
    obtain ⟨n, B, hB, happrox⟩ :=
      environmentLaw_exists_boundedObservation_approx Q A hA ε hε
    let R : ℝ := (n : ℝ) + 1
    let i : Fin d := ⟨0, by omega⟩
    let x : Vec d := (r₀ + 2 * R + 1) • unitVector i
    let T : FieldPair d → FieldPair d := translate x
    let E : Set (FieldPair d) := A ∆ B
    let D : Set (FieldPair d) := A ∩ (T ⁻¹' A)
    let C : Set (FieldPair d) := B ∩ T ⁻¹' B
    let e : ℝ := (Q.measure E).toReal
    let b : ℝ := (Q.measure B).toReal
    let q : ℝ := (Q.measure C).toReal
    have hBlocal : MeasurableSet[localSigma (Metric.ball (0 : Vec d) R)] B := by
      exact hB
    have hind := environmentLaw_independent_window_translate Q R i B hBlocal
    have hBambient : MeasurableSet B := Probability.localSigma_le_borel _ _ hB
    have hE : MeasurableSet E := hA.symmDiff hBambient
    have hT : Measurable T := by
      simpa [T] using Probability.measurable_translate x
    have hTB : MeasurableSet (T ⁻¹' B) := hT hBambient
    have hC : MeasurableSet C := hBambient.inter hTB
    have hpreE : Q.measure (T ⁻¹' E) = Q.measure E := by
      rw [← Measure.map_apply hT hE, Q.stationary x]
    have hApreAE : A =ᵐ[Q.measure] T ⁻¹' A := by
      filter_upwards [hInv x] with ω hω
      exact propext hω.symm
    have hApreNull : Q.measure (A ∆ (T ⁻¹' A)) = 0 :=
      measure_symmDiff_eq_zero_iff.mpr hApreAE
    have hADsubset : A ∆ D ⊆ A ∆ (T ⁻¹' A) := by
      intro ω hω
      change ω ∈ A ∆ (A ∩ (T ⁻¹' A)) at hω
      simp only [Set.mem_symmDiff, Set.mem_inter_iff] at *
      tauto
    have hADnull : Q.measure (A ∆ D) = 0 := by
      apply le_antisymm
      · exact (measure_mono hADsubset).trans_eq hApreNull
      · exact bot_le
    have hDCsubset : D ∆ C ⊆ E ∪ T ⁻¹' E := by
      change (A ∩ (T ⁻¹' A)) ∆ (B ∩ (T ⁻¹' B)) ⊆
        (A ∆ B) ∪ T ⁻¹' (A ∆ B)
      exact symmDiff_inter_subset A (T ⁻¹' A) B (T ⁻¹' B)
    have hsetMeasure : Q.measure (A ∆ C) ≤ Q.measure E + Q.measure (T ⁻¹' E) := by
      calc
        Q.measure (A ∆ C) ≤ Q.measure (A ∆ D) + Q.measure (D ∆ C) :=
          measure_symmDiff_le A D C
        _ = Q.measure (D ∆ C) := by rw [hADnull, zero_add]
        _ ≤ Q.measure E + Q.measure (T ⁻¹' E) :=
          (measure_mono hDCsubset).trans (measure_union_le E (T ⁻¹' E))
    have hpreEreal : (Q.measure (T ⁻¹' E)).toReal = e := by
      simp [e, hpreE]
    have hEreal : e < ε := by
      dsimp [e, E]
      exact ENNReal.toReal_lt_of_lt_ofReal happrox
    have hsetReal : (Q.measure (A ∆ C)).toReal ≤ 2 * e := by
      calc
        (Q.measure (A ∆ C)).toReal ≤ (Q.measure E + Q.measure (T ⁻¹' E)).toReal :=
          ENNReal.toReal_mono (by finiteness) hsetMeasure
        _ = e + e := by
          rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hpreEreal]
        _ = 2 * e := by ring
    have hAp : Q.measure A ≤ 1 := by
      calc
        Q.measure A ≤ Q.measure Set.univ := measure_mono (Set.subset_univ A)
        _ = 1 := measure_univ
    have hBp : Q.measure B ≤ 1 := by
      calc
        Q.measure B ≤ Q.measure Set.univ := measure_mono (Set.subset_univ B)
        _ = 1 := measure_univ
    have hp_nonneg : 0 ≤ p := ENNReal.toReal_nonneg
    have hp_le : p ≤ 1 := by
      dsimp [p]
      exact (ENNReal.toReal_mono (by simp) hAp).trans_eq (by norm_num)
    have hb_nonneg : 0 ≤ b := ENNReal.toReal_nonneg
    have hb_le : b ≤ 1 := by
      dsimp [b]
      exact (ENNReal.toReal_mono (by simp) hBp).trans_eq (by norm_num)
    have hpb : |p - b| ≤ e := by
      have h := (abs_measureReal_sub_le_measureReal_symmDiff
        (μ := Q.measure) hA.nullMeasurableSet hBambient.nullMeasurableSet)
      exact h
    have hqfac : q = b * b := by
      dsimp [q, b, C, T, x] at *
      rw [hind, ENNReal.toReal_mul]
    have hpc : |p - q| ≤ 2 * e := by
      have h := (abs_measureReal_sub_le_measureReal_symmDiff
        (μ := Q.measure) hA.nullMeasurableSet hC.nullMeasurableSet)
      exact h.trans hsetReal
    have hbdiff : |b - p| ≤ ε := by
      rw [abs_sub_comm]
      exact hpb.trans (le_of_lt hEreal)
    have hsum : |b + p| ≤ 2 := by
      rw [abs_of_nonneg (add_nonneg hb_nonneg hp_nonneg)]
      linarith
    have hsquares : |b * b - p * p| ≤ 2 * ε := by
      calc
        |b * b - p * p| = |(b - p) * (b + p)| := by congr 1; ring
        _ = |b - p| * |b + p| := abs_mul _ _
        _ ≤ ε * 2 := mul_le_mul hbdiff hsum (abs_nonneg _) hε.le
        _ = 2 * ε := by ring
    have hdelta : |p - p * p| ≤ 2 * e + |b * b - p * p| := by
      calc
        |p - p * p| = |(p - q) + (q - p * p)| := by congr 1; ring
        _ ≤ |p - q| + |q - p * p| := abs_add_le _ _
        _ ≤ 2 * e + |q - p * p| := add_le_add hpc le_rfl
        _ = 2 * e + |b * b - p * p| := by rw [hqfac]
    nlinarith [hEreal, hsquares, hdelta]
  have hzero : p - p * p = 0 := by
    by_contra hne
    have hpos : 0 < |p - p * p| := abs_pos.mpr hne
    have hcontr := hsmall (|p - p * p| / 5) (by positivity)
    nlinarith
  have hp_cases : p = 0 ∨ p = 1 := by
    have hprod : p * (1 - p) = 0 := by nlinarith [hzero]
    rcases mul_eq_zero.mp hprod with hp | hp
    · exact Or.inl hp
    · exact Or.inr (by linarith)
  rcases hp_cases with hp | hp
  · left
    have hz : (Q.measure A).toReal = 0 := by simpa [p] using hp
    rcases (ENNReal.toReal_eq_zero_iff (Q.measure A)).mp hz with h | h
    · exact h
    · exact False.elim ((measure_ne_top Q.measure A) h)
  · right
    exact (ENNReal.toReal_eq_one_iff (Q.measure A)).mp (by simpa [p] using hp)

end EinsteinRelation.Localization
