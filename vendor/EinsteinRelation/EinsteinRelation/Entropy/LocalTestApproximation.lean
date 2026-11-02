import EinsteinRelation.Calculus.WeakChainRule
import EinsteinRelation.Entropy.HorizontalSmoothApproximation
import EinsteinRelation.Environment.LocalIntegralMeasurability
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # Local horizontal tests approximating a local function with a weak gradient

Source: `paper/main.tex` 545-566 and 662-666 ("by density"). A function `f` with weak horizontal
gradient `Df`, both in `L^q` and measurable for the local σ-algebra of the ball `B_r`, is the limit
of horizontal tests `F_n` that are measurable for the local σ-algebra of `B_{2r}`, and whose
horizontal derivatives converge to `Df` in `L^q`. The tests are `S_ε (T_M ∘ f)`: the soft
truncation `T_M` (bounded, with the weak chain rule), followed by the horizontal mollification
`S_ε` at a scale `ε ≤ min r 1`.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace EinsteinRelation.Entropy

variable {d : ℕ}

/-! ## The soft truncation -/

theorem abs_softTruncation_le_level {M : ℝ} (hM : 0 < M) (x : ℝ) :
    |softTruncation M x| ≤ M := by
  have hpos : 0 < 1 + x / M * (x / M) := one_add_mul_self_pos (x / M)
  unfold softTruncation
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have ht : |x / M| ≤ 1 + x / M * (x / M) := by
    rcases le_or_gt |x / M| 1 with h | h
    · nlinarith [mul_self_nonneg (x / M)]
    · have h2 : |x / M| ≤ |x / M| * |x / M| := le_mul_of_one_le_right (abs_nonneg _) h.le
      rw [abs_mul_abs_self] at h2
      linarith
  have hx : |x| = M * |x / M| := by
    rw [abs_div, abs_of_pos hM]
    field_simp
  rw [hx]
  exact mul_le_mul_of_nonneg_left ht hM.le

theorem deriv_softTruncation (M : ℝ) : deriv (softTruncation M) = softTruncationDeriv M :=
  funext fun x => (hasDerivAt_softTruncation M x).deriv

theorem contDiff_softTruncation (M : ℝ) : ContDiff ℝ 1 (softTruncation M) := by
  rw [contDiff_one_iff_deriv, deriv_softTruncation]
  exact ⟨fun x => (hasDerivAt_softTruncation M x).differentiableAt,
    continuous_softTruncationDeriv M⟩

/-- The weak chain rule for the soft truncation. -/
theorem hasWeakHorizontalGradient_softTruncation {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (M : ℝ) {f : FieldPair d → ℝ}
    {Df : FieldPair d → Vec d} (hf : HasWeakHorizontalGradient Q hQ f Df) :
    HasWeakHorizontalGradient Q hQ (fun w => softTruncation M (f w))
      (fun w i => softTruncationDeriv M (f w) * Df w i) := by
  have h := Calculus.hasWeakChainRule_of_contDiff Q hQ (contDiff_softTruncation M) (L := 1)
    (fun x => by rw [deriv_softTruncation]; exact abs_softTruncationDeriv_le_one M x) f Df hf
  rw [deriv_softTruncation] at h
  exact h

/-! ## The rescaled mollifier -/

theorem continuous_euclideanNorm' : Continuous (fun v : Vec d => euclideanNorm v) := by
  have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) := by
    apply continuous_finset_sum
    intro j _
    exact (continuous_apply j).mul (continuous_apply j)
  unfold euclideanNorm euclideanSq dot
  exact Real.continuous_sqrt.comp hsum

theorem contDiff_unitMassScaledMollifier (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Calculus.unitMassScaledMollifier d ε) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ε⁻¹ • x) := contDiff_id.const_smul (ε⁻¹ : ℝ)
  unfold Calculus.unitMassScaledMollifier
  exact contDiff_const.mul ((contDiff_mollifier d).comp hs)

theorem euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero {ε : ℝ} (hε : 0 < ε) {z : Vec d}
    (hz : Calculus.unitMassScaledMollifier d ε z ≠ 0) : euclideanNorm z < ε := by
  unfold Calculus.unitMassScaledMollifier at hz
  have hm : mollifier d (ε⁻¹ • z) ≠ 0 := right_ne_zero_of_mul hz
  have hts : ε⁻¹ • z ∈ tsupport (mollifier d) :=
    subset_tsupport _ (Function.mem_support.mpr hm)
  have h1 : euclideanNorm (ε⁻¹ • z) < 1 := tsupport_mollifier_subset d hts
  rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hε)] at h1
  have h2 := (inv_mul_lt_iff₀ hε).mp h1
  rwa [mul_one] at h2

theorem hasCompactSupport_unitMassScaledMollifier {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (Calculus.unitMassScaledMollifier d ε) := by
  have h := ((hasCompactSupport_mollifier d).comp_smul (inv_ne_zero hε.ne')).mul_left
    (f := fun _ : Vec d => (ε ^ d)⁻¹)
  exact h

/-- Mollification at scale `ε` of a field that is local in `B_r` is local in `B_{r+ε}`. -/
theorem measurable_localSigma_horizontalMollify {r ε : ℝ} (hε : 0 < ε) {u : FieldPair d → ℝ}
    (hu : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] u) :
    Measurable[localSigma {y : Vec d | euclideanNorm y < r + ε}]
      (horizontalMollify (Calculus.unitMassScaledMollifier d ε) u) := by
  set S : Set (Vec d) := {z | euclideanNorm z < ε} with hSdef
  have hS : MeasurableSet S := measurableSet_lt continuous_euclideanNorm'.measurable measurable_const
  have heq : horizontalMollify (Calculus.unitMassScaledMollifier d ε) u =
      fun w => ∫ z in S, Calculus.unitMassScaledMollifier d ε z * u (translate z w) := by
    funext w
    unfold horizontalMollify
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
    by_contra hne
    exact hz (euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero hε (left_ne_zero_of_mul hne))
  rw [heq]
  refine measurable_localSigma_setIntegral_translate hS (fun x hx y hy => ?_) _
    (contDiff_unitMassScaledMollifier ε).continuous.measurable u hu
  have h := TimeChange.euclideanNorm_add_le x y
  simp only [hSdef, Set.mem_setOf_eq] at hx hy ⊢
  linarith

/-! ## The approximation -/

/-- The error of one truncation-mollification step, split into its two parts. -/
theorem eLpNorm_sub_le_of_split {Q : Measure (FieldPair d)} {q : ℝ≥0∞} (hq : 1 ≤ q)
    {a b c : FieldPair d → ℝ} (ha : AEStronglyMeasurable a Q) (hb : AEStronglyMeasurable b Q)
    (hc : AEStronglyMeasurable c Q) :
    eLpNorm (fun w => a w - c w) q Q ≤
      eLpNorm (fun w => a w - b w) q Q + eLpNorm (fun w => b w - c w) q Q := by
  have e : (fun w => a w - c w) = fun w => (a w - b w) + (b w - c w) := funext fun w => by ring
  rw [e]
  exact eLpNorm_add_le hq

theorem tendsto_of_le_two_mul_inv {u : ℕ → ℝ≥0∞} (hu : ∀ n, u n ≤ 2 * ((n : ℝ≥0∞) + 1)⁻¹) :
    Tendsto u atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ≥0∞))⁻¹) atTop (𝓝 0) := ENNReal.tendsto_inv_nat_nhds_zero
  have h2 : Tendsto (fun n : ℕ => 2 * ((n : ℝ≥0∞))⁻¹) atTop (𝓝 0) := by
    have h3 : Tendsto (fun n : ℕ => 2 * ((n : ℝ≥0∞))⁻¹) atTop (𝓝 (2 * 0)) :=
      ENNReal.Tendsto.const_mul h1 (Or.inr (by simp))
    rwa [mul_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun n => zero_le)
    fun n => (hu n).trans ?_
  gcongr
  exact le_self_add

/-- **Approximation by local horizontal tests** (`paper/main.tex` 545-566, 662-666). -/
theorem exists_local_test_approximation {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {r : ℝ} (hr : 0 < r) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ∞)
    {f : FieldPair d → ℝ} {Df : FieldPair d → Vec d} (hf : HasWeakHorizontalGradient Q hQ f Df)
    (hfq : MemLp f q Q) (hDfq : ∀ i, MemLp (fun w => Df w i) q Q)
    (hfl : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] f)
    (hDfl : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] Df) :
    ∃ (F : ℕ → FieldPair d → ℝ) (G : ℕ → FieldPair d → Vec d),
      (∀ n, IsHorizontalTest (F n)) ∧
      (∀ n, Measurable[localSigma {y : Vec d | euclideanNorm y < 2 * r}] (F n)) ∧
      (∀ n, Measurable[localSigma {y : Vec d | euclideanNorm y < 2 * r}] (G n)) ∧
      (∀ n, ∀ᵐ w ∂Q, ∀ i, horizontalDerivative i (F n) w = G n w i) ∧
      (∀ n, MemLp (fun w => F n w - f w) q Q) ∧
      Tendsto (fun n => eLpNorm (fun w => F n w - f w) q Q) atTop (𝓝 0) ∧
      (∀ n i, MemLp (fun w => G n w i - Df w i) q Q) ∧
      ∀ i, Tendsto (fun n => eLpNorm (fun w => G n w i - Df w i) q Q) atTop (𝓝 0) := by
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  set U : Set (Vec d) := {y : Vec d | euclideanNorm y < r} with hUdef
  have hfm : Measurable f := hfl.mono (Probability.localSigma_le_borel U) le_rfl
  have hDfm : Measurable Df := hDfl.mono (Probability.localSigma_le_borel U) le_rfl
  have hDim : ∀ i, Measurable fun w => Df w i := fun i => (measurable_pi_apply i).comp hDfm
  set δ : ℕ → ℝ≥0∞ := fun n => ((n : ℝ≥0∞) + 1)⁻¹ with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => ENNReal.inv_pos.mpr (by simp)
  have hδtop : ∀ n, δ n < ⊤ := fun n => by
    simp only [hδdef, ENNReal.inv_lt_top]
    exact lt_of_lt_of_le zero_lt_one le_add_self
  -- The truncated functions and their weak gradients.
  set u : ℕ → FieldPair d → ℝ := fun m w => softTruncation (m : ℝ) (f w) with hudef
  set v : ℕ → Fin d → FieldPair d → ℝ := fun m i w => softTruncationDeriv (m : ℝ) (f w) * Df w i
    with hvdef
  have hum : ∀ m, Measurable (u m) := fun m => (measurable_softTruncation _).comp hfm
  have hvm : ∀ m i, Measurable (v m i) := fun m i =>
    ((measurable_softTruncationDeriv _).comp hfm).mul (hDim i)
  have hul : ∀ m, Measurable[localSigma U] (u m) := fun m =>
    (measurable_softTruncation _).comp hfl
  have hvl : ∀ m i, Measurable[localSigma U] (v m i) := fun m i =>
    ((measurable_softTruncationDeriv _).comp hfl).mul ((measurable_pi_apply i).comp hDfl)
  have hvq : ∀ m i, MemLp (v m i) q Q := fun m i =>
    (hDfq i).of_le (hvm m i).aestronglyMeasurable (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_softTruncationDeriv_le_one _ _))
  have huq : ∀ m : ℕ, 0 < m → MemLp (u m) q Q := fun m hm =>
    MemLp.of_bound (hum m).aestronglyMeasurable (m : ℝ) (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs]; exact abs_softTruncation_le_level (by exact_mod_cast hm) _)
  -- Step 1: the truncation level.
  have hT : ∀ n, ∃ m : ℕ, 0 < m ∧
      eLpNorm (fun w => u m w - f w) q Q ≤ δ n ∧
      ∀ i, eLpNorm (fun w => v m i w - Df w i) q Q ≤ δ n := by
    intro n
    have h1 := tendsto_eLpNorm_softTruncation_sub hq0 hq hfq hfm
    have h2 : ∀ i, Tendsto (fun m : ℕ => eLpNorm (fun w => v m i w - Df w i) q Q) atTop (𝓝 0) := by
      intro i
      refine (tendsto_eLpNorm_softTruncationDeriv_error hq0 hq (hDfq i) hfm (hDim i)).congr
        fun m => ?_
      rw [← eLpNorm_neg]
      congr 1
      funext w
      simp only [hvdef, Pi.neg_apply]
      ring
    have e1 := (ENNReal.tendsto_nhds_zero.mp h1) (δ n) (hδpos n)
    have e2 : ∀ᶠ m in atTop, ∀ i, eLpNorm (fun w => v m i w - Df w i) q Q ≤ δ n :=
      Filter.eventually_all.mpr fun i => (ENNReal.tendsto_nhds_zero.mp (h2 i)) (δ n) (hδpos n)
    obtain ⟨m, hm0, hm1, hm2⟩ := ((eventually_gt_atTop 0).and (e1.and e2)).exists
    exact ⟨m, hm0, hm1, hm2⟩
  choose m hm0 hmu hmv using hT
  -- Step 2: the mollification scale.
  have hE : ∀ n, ∃ ε : ℝ, 0 < ε ∧ ε ≤ min r 1 ∧
      eLpNorm (fun w => horizontalMollify (Calculus.unitMassScaledMollifier d ε) (u (m n)) w -
        u (m n) w) q Q ≤ δ n ∧
      ∀ i, eLpNorm (fun w => horizontalMollify (Calculus.unitMassScaledMollifier d ε)
        (v (m n) i) w - v (m n) i w) q Q ≤ δ n := by
    intro n
    have h1 := Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier Q hQ q hq
      (hum (m n)) (huq (m n) (hm0 n))
    have h2 := fun i => Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier Q hQ q hq
      (hvm (m n) i) (hvq (m n) i)
    have e1 := (ENNReal.tendsto_nhds_zero.mp h1) (δ n) (hδpos n)
    have e2 := Filter.eventually_all.mpr fun i => (ENNReal.tendsto_nhds_zero.mp (h2 i)) (δ n)
      (hδpos n)
    have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo 0 (min r 1) :=
      Ioo_mem_nhdsGT (lt_min hr one_pos)
    obtain ⟨ε, hε, h1', h2'⟩ := (e3.and (e1.and e2)).exists
    exact ⟨ε, hε.1, hε.2.le, h1', h2'⟩
  choose ε hε0 hεr hεu hεv using hE
  have hε1 : ∀ n, ε n ≤ 1 := fun n => (hεr n).trans (min_le_right _ _)
  have hεr' : ∀ n, ε n ≤ r := fun n => (hεr n).trans (min_le_left _ _)
  set κ : ℕ → Vec d → ℝ := fun n => Calculus.unitMassScaledMollifier d (ε n) with hκdef
  have hκm : ∀ n, Measurable (κ n) := fun n =>
    (contDiff_unitMassScaledMollifier (ε n)).continuous.measurable
  have hSum : ∀ n, Measurable (horizontalMollify (κ n) (u (m n))) := fun n =>
    measurable_horizontalMollify (κ n) (hκm n) (hum (m n))
  have hSvm : ∀ n i, Measurable (horizontalMollify (κ n) (v (m n) i)) := fun n i =>
    measurable_horizontalMollify (κ n) (hκm n) (hvm (m n) i)
  have hSu : ∀ n, MemLp (fun w => horizontalMollify (κ n) (u (m n)) w - u (m n) w) q Q :=
    fun n => (hεu n).trans_lt (hδtop n)
  have hSv : ∀ n i, MemLp (fun w => horizontalMollify (κ n) (v (m n) i) w - v (m n) i w) q Q :=
    fun n i => (hεv n i).trans_lt (hδtop n)
  refine ⟨fun n => horizontalMollify (κ n) (u (m n)),
    fun n w i => horizontalMollify (κ n) (v (m n) i) w, fun n => ?_, fun n => ?_, fun n => ?_,
    fun n => ?_, fun n => ?_, ?_, fun n i => ?_, fun i => ?_⟩
  · exact Correctors.isHorizontalTest_horizontalMollify (κ n)
      (contDiff_unitMassScaledMollifier (ε n)) (hasCompactSupport_unitMassScaledMollifier (hε0 n))
      (u (m n)) (hum (m n)) ⟨(m n : ℝ), fun w =>
        abs_softTruncation_le_level (by exact_mod_cast hm0 n) _⟩
  · have hsub : {y : Vec d | euclideanNorm y < r + ε n} ⊆ {y : Vec d | euclideanNorm y < 2 * r} :=
      fun y hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        linarith [hεr' n]
    exact (measurable_localSigma_horizontalMollify (hε0 n) (hul (m n))).mono
      (Probability.localSigma_mono hsub) le_rfl
  · have hsub : {y : Vec d | euclideanNorm y < r + ε n} ⊆ {y : Vec d | euclideanNorm y < 2 * r} :=
      fun y hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        linarith [hεr' n]
    letI : MeasurableSpace (FieldPair d) := localSigma {y : Vec d | euclideanNorm y < 2 * r}
    exact Measurable.of_eval fun i =>
      (measurable_localSigma_horizontalMollify (hε0 n) (hvl (m n) i)).mono
        (Probability.localSigma_mono hsub) le_rfl
  · have hchain := hasWeakHorizontalGradient_softTruncation hQ (m n : ℝ) hf
    rw [ae_all_iff]
    intro i
    have hfi : Integrable f Q := hf.1
    have hui : Integrable (u (m n)) Q := (huq (m n) (hm0 n)).integrable hq1
    have hvi : Integrable (v (m n) i) Q := (hvq (m n) i).integrable hq1
    exact Calculus.ae_orbit_derivative_mollify_eq hQ (hε0 n) (hε1 n) (hum (m n)) hui
      (hvm (m n) i) hvi i fun K hK => Calculus.weakPairing_core hchain i hK
  · have e : (fun w => horizontalMollify (κ n) (u (m n)) w - f w) =
        fun w => (horizontalMollify (κ n) (u (m n)) w - u (m n) w) + (u (m n) w - f w) :=
      funext fun w => by ring
    rw [e]
    exact (hSu n).add ((huq (m n) (hm0 n)).sub hfq)
  · refine tendsto_of_le_two_mul_inv fun n => ?_
    refine (eLpNorm_sub_le_of_split hq1 (hSum n).aestronglyMeasurable
      (hum (m n)).aestronglyMeasurable hfm.aestronglyMeasurable).trans ?_
    rw [two_mul]
    exact add_le_add (hεu n) (hmu n)
  · have e : (fun w => horizontalMollify (κ n) (v (m n) i) w - Df w i) =
        fun w => (horizontalMollify (κ n) (v (m n) i) w - v (m n) i w) + (v (m n) i w - Df w i) :=
      funext fun w => by ring
    rw [e]
    exact (hSv n i).add ((hvq (m n) i).sub (hDfq i))
  · refine tendsto_of_le_two_mul_inv fun n => ?_
    refine (eLpNorm_sub_le_of_split hq1 (hSvm n i).aestronglyMeasurable
      (hvm (m n) i).aestronglyMeasurable (hDim i).aestronglyMeasurable).trans ?_
    rw [two_mul]
    exact add_le_add (hεv n i) (hmv n i)

end EinsteinRelation.Entropy
