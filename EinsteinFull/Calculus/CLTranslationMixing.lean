import EinsteinFull.Calculus.S2ReducedErgodicitySupport

/-!
# Far translates of the environment law

Finite range of dependence makes a bounded-window event independent of its translates along a
coordinate axis by more than the range plus the window diameter. Hence an event that is null
on its intersections with translates by distances tending to infinity is itself null, and a
measurable translation eigenfunction with a nonzero frequency vanishes almost surely.
-/

open MeasureTheory Filter
open scoped Topology symmDiff

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

private theorem abs_coord_le_euclideanNorm (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  have hsq : v i * v i ≤ ∑ j, v j * v j :=
    Finset.single_le_sum (f := fun j => v j * v j)
      (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact hsq

private theorem localSigma_translate_preimage_ball (x : Vec d) {R : ℝ}
    {B : Set (FieldPair d)} (hB : MeasurableSet[localSigma (Metric.ball (0 : Vec d) R)] B) :
    MeasurableSet[localSigma (Metric.ball x R)] (translate x ⁻¹' B) := by
  have himage : (fun y : Vec d => x + y) '' Metric.ball (0 : Vec d) R ⊆ Metric.ball x R := by
    rintro z ⟨y, hy, rfl⟩
    apply Metric.mem_ball.mpr
    have hy' : dist y (0 : Vec d) < R := Metric.mem_ball.mp hy
    simpa [dist_eq_norm, add_comm, add_left_comm, add_assoc] using hy'
  have hlocal := Probability.measurable_translate_local x (Metric.ball (0 : Vec d) R)
  exact (Probability.localSigma_mono himage) _ (hlocal hB)

/-- A window event is independent of its translate along a coordinate axis by any distance at
least the range plus twice the window radius plus one. -/
theorem environmentLaw_indep_window_translate_far (Q : EnvironmentLaw d Λ₀ r₀) {R s : ℝ}
    (i : Fin d) (hs : r₀ + 2 * R + 1 ≤ s) (B : Set (FieldPair d))
    (hB : MeasurableSet[localSigma (Metric.ball (0 : Vec d) R)] B) :
    Q.measure (B ∩ translate (s • unitVector i) ⁻¹' B) = Q.measure B * Q.measure B := by
  let x : Vec d := s • unitVector i
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
    have hxCoord : x i = s := by simp [x, unitVector]
    have hlower : r₀ + 1 ≤ z i - y i := by
      have hzlo : -R < z i - x i := (abs_lt.mp hzCoord).1
      have hyhi : y i < R := (abs_lt.mp hyCoord).2
      rw [hxCoord] at hzlo
      linarith
    calc
      r₀ + 1 ≤ |z i - y i| := le_trans hlower (le_abs_self _)
      _ = |(y - z) i| := by simp [Pi.sub_apply, abs_sub_comm]
      _ ≤ euclideanNorm (y - z) := abs_coord_le_euclideanNorm (y - z) i
  have hind := Q.finiteRange U W Metric.isOpen_ball.measurableSet
    Metric.isOpen_ball.measurableSet hgap
  have hlocal : MeasurableSet[localSigma W] (translate x ⁻¹' B) :=
    localSigma_translate_preimage_ball x hB
  have hfac := (ProbabilityTheory.Indep_iff (localSigma U) (localSigma W) Q.measure).1 hind
    B (translate x ⁻¹' B) hB hlocal
  have hBambient : MeasurableSet B := Probability.localSigma_le_borel U B hB
  have hpre : Q.measure (translate x ⁻¹' B) = Q.measure B := by
    rw [← Measure.map_apply (Probability.measurable_translate x) hBambient, Q.stationary]
  rw [hpre] at hfac
  exact hfac

/-- An event whose intersections with its translates along a coordinate axis, by distances
tending to infinity, are null is itself null. -/
theorem environmentLaw_measure_eq_zero_of_far_translates (Q : EnvironmentLaw d Λ₀ r₀)
    {A : Set (FieldPair d)} (hA : MeasurableSet A) (i : Fin d) {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop)
    (hdisj : ∀ n, Q.measure (A ∩ translate (s n • unitVector i) ⁻¹' A) = 0) :
    Q.measure A = 0 := by
  let p : ℝ := (Q.measure A).toReal
  have hsmall : ∀ ε : ℝ, 0 < ε → p ^ 2 ≤ 4 * ε + 2 * ε ^ 2 := by
    intro ε hε
    obtain ⟨n, B, hB, happrox⟩ :=
      Localization.environmentLaw_exists_boundedObservation_approx Q A hA ε hε
    let R : ℝ := (n : ℝ) + 1
    have hBlocal : MeasurableSet[localSigma (Metric.ball (0 : Vec d) R)] B := hB
    obtain ⟨m, hm⟩ := (tendsto_atTop.1 hs (r₀ + 2 * R + 1)).exists
    let T : FieldPair d → FieldPair d := translate (s m • unitVector i)
    have hT : Measurable T := Probability.measurable_translate _
    have hBm : MeasurableSet B := Probability.localSigma_le_borel _ B hB
    let E : Set (FieldPair d) := A ∆ B
    have hE : MeasurableSet E := hA.symmDiff hBm
    have hind := environmentLaw_indep_window_translate_far Q i hm B hBlocal
    have hpreE : Q.measure (T ⁻¹' E) = Q.measure E := by
      rw [← Measure.map_apply hT hE, Q.stationary]
    have hsub : B ∩ T ⁻¹' B ⊆ (A ∩ T ⁻¹' A) ∪ (E ∪ T ⁻¹' E) := by
      intro ω hω
      simp only [E, Set.mem_inter_iff, Set.mem_union, Set.mem_preimage,
        Set.mem_symmDiff] at hω ⊢
      tauto
    have hBB : Q.measure B * Q.measure B ≤ 2 * Q.measure E := by
      rw [← hind]
      calc Q.measure (B ∩ T ⁻¹' B) ≤ Q.measure ((A ∩ T ⁻¹' A) ∪ (E ∪ T ⁻¹' E)) :=
            measure_mono hsub
        _ ≤ Q.measure (A ∩ T ⁻¹' A) + (Q.measure E + Q.measure (T ⁻¹' E)) :=
            (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
        _ = 2 * Q.measure E := by rw [hdisj m, hpreE, zero_add, two_mul]
    have hAB : Q.measure A ≤ Q.measure B + Q.measure E := by
      calc Q.measure A ≤ Q.measure (B ∪ E) := measure_mono fun ω hω => by
            by_cases hb : ω ∈ B
            · exact Or.inl hb
            · exact Or.inr (Or.inl ⟨hω, hb⟩)
        _ ≤ Q.measure B + Q.measure E := measure_union_le _ _
    let b : ℝ := (Q.measure B).toReal
    let e : ℝ := (Q.measure E).toReal
    have he : e < ε := ENNReal.toReal_lt_of_lt_ofReal happrox
    have he0 : 0 ≤ e := ENNReal.toReal_nonneg
    have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
    have hbb : b * b ≤ 2 * e := by
      have := ENNReal.toReal_mono (by finiteness) hBB
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using this
    have hpb : p ≤ b + e := by
      have := ENNReal.toReal_mono (by finiteness) hAB
      rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
    have h1 : p ^ 2 ≤ (b + e) ^ 2 := pow_le_pow_left₀ hp0 hpb 2
    have h2 : (b + e) ^ 2 ≤ 2 * (b * b) + 2 * e ^ 2 := by nlinarith [sq_nonneg (b - e)]
    have h3 : e ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ he0 he.le 2
    linarith
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp : p = 0 := by
    by_contra hne
    have hpos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hne)
    let ε : ℝ := min 1 (p ^ 2 / 12)
    have hε : 0 < ε := lt_min one_pos (by positivity)
    have h1 : ε ≤ 1 := min_le_left _ _
    have h2 : ε ≤ p ^ 2 / 12 := min_le_right _ _
    have := hsmall ε hε
    nlinarith
  exact (ENNReal.toReal_eq_zero_iff _).1 hp |>.resolve_right (measure_ne_top _ _)

/-- A real observable that changes sign under translations along a coordinate axis by
distances tending to infinity has a null positivity set. -/
theorem environmentLaw_measure_pos_eq_zero_of_far_antisymmetric (Q : EnvironmentLaw d Λ₀ r₀)
    {g : FieldPair d → ℝ} (hg : Measurable g) (i : Fin d) {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop)
    (hanti : ∀ n, ∀ᵐ ω ∂Q.measure, g (translate (s n • unitVector i) ω) = -g ω) :
    Q.measure {ω | 0 < g ω} = 0 := by
  apply environmentLaw_measure_eq_zero_of_far_translates Q
    (measurableSet_lt measurable_const hg) i hs
  intro n
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (hanti n))
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at hω ⊢
  intro h
  linarith [hω.1, hω.2]

private theorem dot_smul_unitVector (k : Vec d) (s : ℝ) (i : Fin d) :
    dot k (s • unitVector i) = s * k i := by
  simp [dot, unitVector, Pi.single_apply, mul_comm]

private theorem cexp_half_odd_mul_two_pi (m : ℤ) :
    Complex.exp (((2 * Real.pi * ((m : ℝ) + 1 / 2) : ℝ) : ℂ) * Complex.I) = -1 := by
  have h : (((2 * Real.pi * ((m : ℝ) + 1 / 2) : ℝ) : ℂ) * Complex.I) =
      (m : ℂ) * (2 * Real.pi * Complex.I) + Real.pi * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

/-- A measurable function of the physical environment that is a translation eigenfunction with a
nonzero frequency vanishes almost surely. -/
theorem environmentLaw_ae_eq_zero_of_translation_eigen (Q : EnvironmentLaw d Λ₀ r₀)
    {h : FieldPair d → ℂ} (hh : Measurable h) {k : Vec d} (hk : k ≠ 0)
    (heig : ∀ x : Vec d, ∀ᵐ ω ∂Q.measure,
      h (translate x ω) =
        Complex.exp (((2 * Real.pi * dot k x : ℝ) : ℂ) * Complex.I) * h ω) :
    ∀ᵐ ω ∂Q.measure, h ω = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hk (funext hcon)
  have hai : 0 < |k i| := abs_pos.2 hi
  let s : ℕ → ℝ := fun n => ((n : ℝ) + 1 / 2) / |k i|
  have hs : Tendsto s atTop atTop := by
    apply Tendsto.atTop_div_const hai
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hneg : ∀ n, ∀ᵐ ω ∂Q.measure, h (translate (s n • unitVector i) ω) = -h ω := by
    intro n
    filter_upwards [heig (s n • unitVector i)] with ω hω
    rw [hω, dot_smul_unitVector]
    have hphase : Complex.exp (((2 * Real.pi * (s n * k i) : ℝ) : ℂ) * Complex.I) = -1 := by
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · have hsk : s n * k i = ((-(n : ℤ) - 1 : ℤ) : ℝ) + 1 / 2 := by
          simp only [s, abs_of_neg hlt]
          field_simp
          push_cast
          ring
        rw [hsk]
        exact cexp_half_odd_mul_two_pi _
      · have hsk : s n * k i = ((n : ℤ) : ℝ) + 1 / 2 := by
          simp only [s, abs_of_pos hgt]
          field_simp
          push_cast
          ring
        rw [hsk]
        exact cexp_half_odd_mul_two_pi _
    rw [hphase, neg_one_mul]
  have hre := environmentLaw_measure_pos_eq_zero_of_far_antisymmetric Q
    (Complex.measurable_re.comp hh) i hs fun n => by
      filter_upwards [hneg n] with ω hω
      simp only [Function.comp, hω, Complex.neg_re]
  have hre' := environmentLaw_measure_pos_eq_zero_of_far_antisymmetric Q
    (Complex.measurable_re.comp hh).neg i hs fun n => by
      filter_upwards [hneg n] with ω hω
      simp only [Function.comp, Pi.neg_apply, hω, Complex.neg_re]
  have him := environmentLaw_measure_pos_eq_zero_of_far_antisymmetric Q
    (Complex.measurable_im.comp hh) i hs fun n => by
      filter_upwards [hneg n] with ω hω
      simp only [Function.comp, hω, Complex.neg_im]
  have him' := environmentLaw_measure_pos_eq_zero_of_far_antisymmetric Q
    (Complex.measurable_im.comp hh).neg i hs fun n => by
      filter_upwards [hneg n] with ω hω
      simp only [Function.comp, Pi.neg_apply, hω, Complex.neg_im]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hre, measure_eq_zero_iff_ae_notMem.1 hre',
    measure_eq_zero_iff_ae_notMem.1 him, measure_eq_zero_iff_ae_notMem.1 him'] with
    ω h1 h2 h3 h4
  simp only [Function.comp, Pi.neg_apply, not_lt, neg_nonpos] at h1 h2 h3 h4
  exact Complex.ext (le_antisymm h1 h2) (le_antisymm h3 h4)

/-- The same statement for the reduced law. -/
theorem reducedLaw_ae_eq_zero_of_translation_eigen (Q : EnvironmentLaw d Λ₀ r₀)
    {h : FieldPair d → ℂ} (hh : Measurable h) {k : Vec d} (hk : k ≠ 0)
    (heig : ∀ x : Vec d, ∀ᵐ ω ∂reducedLaw Q,
      h (translate x ω) =
        Complex.exp (((2 * Real.pi * dot k x : ℝ) : ℂ) * Complex.I) * h ω) :
    ∀ᵐ ω ∂reducedLaw Q, h ω = 0 := by
  have hm : Measurable (reduce : FieldPair d → FieldPair d) := Probability.measurable_reduce
  have h0 := environmentLaw_ae_eq_zero_of_translation_eigen Q (hh.comp hm) hk fun x => by
    filter_upwards [ae_of_ae_map hm.aemeasurable (heig x)] with ω hω
    simpa only [Function.comp, reduce_translate] using hω
  exact (ae_map_iff hm.aemeasurable (measurableSet_eq_fun hh measurable_const)).2 h0

end EinsteinFull
