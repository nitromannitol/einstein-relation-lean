import EinsteinRelation.Correctors.ScalarGlobalAssembly
import EinsteinRelation.Correctors.ScalarDecompositionSums
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # Global moment bounds for the scalar decomposition

Source: `paper/main.tex:1070–1084`. The actual sums of scalar and vector
bands satisfy the four required bounds once their one-scale estimates and
the small-scale flux estimate have been established.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}

/-- The Euclidean norm is subadditive over finite vector sums
(`paper/main.tex:1070–1078`). -/
theorem euclideanNorm_finset_sum_le {ι : Type*} (s : Finset ι) (v : ι → Vec d) :
    euclideanNorm (∑ k ∈ s, v k) ≤ ∑ k ∈ s, euclideanNorm (v k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [euclideanNorm, euclideanSq, dot]
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (TimeChange.euclideanNorm_add_le _ _).trans (add_le_add le_rfl ih)

/-- Triangle inequality for the actual Euclidean norms of vector fields
(`paper/main.tex:1070–1078`). -/
theorem eLpNorm_euclidean_finset_sum_le {ι : Type*} (s : Finset ι)
    (V : ι → Ω → Vec d) (hV : ∀ k ∈ s, Measurable (V k))
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun ω => euclideanNorm (∑ k ∈ s, V k ω)) p μ ≤
      ∑ k ∈ s, eLpNorm (fun ω => euclideanNorm (V k ω)) p μ := by
  calc
    _ ≤ eLpNorm (fun ω => ∑ k ∈ s, euclideanNorm (V k ω)) p μ :=
      eLpNorm_mono_real (fun ω => by
        rw [Real.norm_of_nonneg (show 0 ≤ euclideanNorm _ from Real.sqrt_nonneg _)]
        exact euclideanNorm_finset_sum_le s (fun k => V k ω))
    _ ≤ _ := eLpNorm_finset_sum_le s _ (fun k hk =>
      (Entropy.continuous_euclideanNorm'.measurable.comp (hV k hk)).aestronglyMeasurable) hp

/-- Summing prescribed real bounds on the moments of scalar fields
(`paper/main.tex:1070–1078`). -/
theorem eLpNorm_finset_sum_le_of_bound {ι : Type*} (s : Finset ι)
    (X : ι → Ω → ℝ) (hX : ∀ k ∈ s, AEStronglyMeasurable (X k) μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (B : ι → ℝ) (hB : ∀ k ∈ s, 0 ≤ B k)
    (hbound : ∀ k ∈ s, eLpNorm (X k) p μ ≤ ENNReal.ofReal (B k)) :
    eLpNorm (fun ω => ∑ k ∈ s, X k ω) p μ ≤ ENNReal.ofReal (∑ k ∈ s, B k) := by
  exact (eLpNorm_finset_sum_le s X hX hp).trans
    ((Finset.sum_le_sum hbound).trans_eq (ENNReal.ofReal_sum_of_nonneg hB).symm)

/-- Summing prescribed real bounds on Euclidean vector moments
(`paper/main.tex:1070–1078`). -/
theorem eLpNorm_euclidean_finset_sum_le_of_bound {ι : Type*} (s : Finset ι)
    (V : ι → Ω → Vec d) (hV : ∀ k ∈ s, Measurable (V k))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (B : ι → ℝ) (hB : ∀ k ∈ s, 0 ≤ B k)
    (hbound : ∀ k ∈ s,
      eLpNorm (fun ω => euclideanNorm (V k ω)) p μ ≤ ENNReal.ofReal (B k)) :
    eLpNorm (fun ω => euclideanNorm (∑ k ∈ s, V k ω)) p μ ≤
      ENNReal.ofReal (∑ k ∈ s, B k) := by
  exact (eLpNorm_euclidean_finset_sum_le s V hV hp).trans
    ((Finset.sum_le_sum hbound).trans_eq (ENNReal.ofReal_sum_of_nonneg hB).symm)

/-- The dyadic scale weights give a bound linear in the largest scale
(`paper/main.tex:1074–1076`). -/
theorem sum_dyadic_scale_bound {A : ℝ} (hA : 0 ≤ A) (K : ℕ) :
    ∑ k ∈ Finset.range K,
      A * ((2 : ℝ) ^ k + Real.sqrt (Real.log (2 + (2 : ℝ) ^ k))) ≤
        4 * A * (2 : ℝ) ^ K := by
  rw [← Finset.mul_sum]
  simpa only [mul_assoc, mul_comm 4 A] using
    mul_le_mul_of_nonneg_left (dyadic_sum_scale_le K) hA

/-- The dyadic error weights are summable independently of the largest
scale (`paper/main.tex:1071–1073`). -/
theorem sum_dyadic_error_bound {A : ℝ} (hA : 0 ≤ A) (K : ℕ) :
    ∑ k ∈ Finset.range K,
      A * (Real.sqrt (Real.log (2 + (2 : ℝ) ^ k)) / (2 : ℝ) ^ k) ≤ 12 * A := by
  rw [← Finset.mul_sum]
  simpa only [mul_comm A 12] using
    mul_le_mul_of_nonneg_left (dyadic_sum_sqrtLog_div_le_twelve K) hA

/-- A bounded contribution from each band gives logarithmic growth
(`paper/main.tex:1077–1078`). -/
theorem sum_dyadic_constant_bound {A : ℝ} (hA : 0 ≤ A) (K : ℕ) :
    ∑ _k ∈ Finset.range K, A ≤ 2 * A * Real.log (2 + (2 : ℝ) ^ K) := by
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left (dyadic_count_le_log K) hA]

/-- Euclidean vector subtraction obeys the moment triangle inequality
(`paper/main.tex:1071–1073`). -/
theorem eLpNorm_euclidean_sub_le {U V : Ω → Vec d}
    (hU : Measurable U) (hV : Measurable V) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun ω => euclideanNorm (U ω - V ω)) p μ ≤
      eLpNorm (fun ω => euclideanNorm (U ω)) p μ +
        eLpNorm (fun ω => euclideanNorm (V ω)) p μ := by
  have hneg (v : Vec d) : euclideanNorm (-v) = euclideanNorm v := by
    simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
      TimeChange.euclideanNorm_smul (-1) v
  calc
    _ ≤ eLpNorm (fun ω => euclideanNorm (U ω) + euclideanNorm (V ω)) p μ :=
      eLpNorm_mono_real (fun ω => by
        rw [Real.norm_of_nonneg (show 0 ≤ euclideanNorm _ from Real.sqrt_nonneg _)]
        simpa only [sub_eq_add_neg, hneg] using
          TimeChange.euclideanNorm_add_le (U ω) (-V ω))
    _ ≤ _ := eLpNorm_add_le
      (Entropy.continuous_euclideanNorm'.measurable.comp hU).aestronglyMeasurable
      (Entropy.continuous_euclideanNorm'.measurable.comp hV).aestronglyMeasurable hp

/-- The literal band sums satisfy all four global moment bounds with
one constant (`paper/main.tex:1070–1078`). The one-scale estimates and
the small-scale flux bound are explicit internal premises. -/
theorem scalarGlobal_moment_bounds {q : ℝ≥0∞} (hq : 1 ≤ q)
    {A B D F : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (K : ℕ) (X H : ℕ → Ω → ℝ) (V W P : ℕ → Ω → Vec d)
    (E₀ : Ω → Vec d) (e : Ω → ℝ)
    (hX : ∀ k ∈ Finset.range K, Measurable (X k))
    (hH : ∀ k ∈ Finset.range K, Measurable (H k))
    (hV : ∀ k ∈ Finset.range K, Measurable (V k))
    (hW : ∀ k ∈ Finset.range K, Measurable (W k))
    (hP : ∀ k ∈ Finset.range K, Measurable (P k)) (hE₀ : Measurable E₀)
    (hXb : ∀ k ∈ Finset.range K, eLpNorm (X k) q μ ≤
      ENNReal.ofReal (A * ((2 : ℝ) ^ k + Real.sqrt (Real.log (2 + (2 : ℝ) ^ k)))))
    (hPb : ∀ k ∈ Finset.range K, eLpNorm (fun ω => euclideanNorm (P k ω)) q μ ≤
      ENNReal.ofReal (A * ((2 : ℝ) ^ k + Real.sqrt (Real.log (2 + (2 : ℝ) ^ k)))))
    (hVb : ∀ k ∈ Finset.range K,
      eLpNorm (fun ω => euclideanNorm (V k ω)) q μ ≤ ENNReal.ofReal A)
    (hWb : ∀ k ∈ Finset.range K, eLpNorm (fun ω => euclideanNorm (W k ω)) q μ ≤
      ENNReal.ofReal (B * (Real.sqrt (Real.log (2 + (2 : ℝ) ^ k)) / (2 : ℝ) ^ k)))
    (hHb : ∀ k ∈ Finset.range K, eLpNorm (H k) q μ ≤
      ENNReal.ofReal (B * (Real.sqrt (Real.log (2 + (2 : ℝ) ^ k)) / (2 : ℝ) ^ k)))
    (hE₀b : eLpNorm (fun ω => euclideanNorm (E₀ ω)) q μ ≤ ENNReal.ofReal D)
    (heb : eLpNorm e q μ ≤ ENNReal.ofReal (F * ((2 : ℝ) ^ K)⁻¹)) :
    let C := 8 * A + 24 * B + D + F
    0 ≤ C ∧
    eLpNorm (fun ω => ∑ k ∈ Finset.range K, X k ω) q μ +
        eLpNorm (fun ω => euclideanNorm (∑ k ∈ Finset.range K, P k ω)) q μ ≤
      ENNReal.ofReal (C * (2 : ℝ) ^ K) ∧
    eLpNorm (fun ω => euclideanNorm (∑ k ∈ Finset.range K, V k ω)) q μ ≤
      ENNReal.ofReal (C * Real.log (2 + (2 : ℝ) ^ K)) ∧
    eLpNorm (fun ω => euclideanNorm (E₀ ω - ∑ k ∈ Finset.range K, W k ω)) q μ +
        eLpNorm (fun ω => ∑ k ∈ Finset.range K, H k ω) q μ ≤ ENNReal.ofReal C ∧
    eLpNorm e q μ ≤ ENNReal.ofReal (C * ((2 : ℝ) ^ K)⁻¹) := by
  dsimp only
  let s := Finset.range K
  let a : ℕ → ℝ := fun k =>
    A * ((2 : ℝ) ^ k + Real.sqrt (Real.log (2 + (2 : ℝ) ^ k)))
  let b : ℕ → ℝ := fun k =>
    B * (Real.sqrt (Real.log (2 + (2 : ℝ) ^ k)) / (2 : ℝ) ^ k)
  have ha (k : ℕ) : 0 ≤ a k := by dsimp only [a]; positivity
  have hb (k : ℕ) : 0 ≤ b k := by dsimp only [b]; positivity
  have hXs : eLpNorm (fun ω => ∑ k ∈ s, X k ω) q μ ≤
      ENNReal.ofReal (4 * A * (2 : ℝ) ^ K) :=
    (eLpNorm_finset_sum_le_of_bound s X (fun k hk => (hX k hk).aestronglyMeasurable)
      hq a (fun k _ => ha k) hXb).trans
        (ENNReal.ofReal_le_ofReal (sum_dyadic_scale_bound hA K))
  have hPs : eLpNorm (fun ω => euclideanNorm (∑ k ∈ s, P k ω)) q μ ≤
      ENNReal.ofReal (4 * A * (2 : ℝ) ^ K) :=
    (eLpNorm_euclidean_finset_sum_le_of_bound s P hP hq a (fun k _ => ha k) hPb).trans
      (ENNReal.ofReal_le_ofReal (sum_dyadic_scale_bound hA K))
  have hVs : eLpNorm (fun ω => euclideanNorm (∑ k ∈ s, V k ω)) q μ ≤
      ENNReal.ofReal (2 * A * Real.log (2 + (2 : ℝ) ^ K)) :=
    (eLpNorm_euclidean_finset_sum_le_of_bound s V hV hq (fun _ => A) (fun _ _ => hA) hVb).trans
      (ENNReal.ofReal_le_ofReal (sum_dyadic_constant_bound hA K))
  have hWs : eLpNorm (fun ω => euclideanNorm (∑ k ∈ s, W k ω)) q μ ≤
      ENNReal.ofReal (12 * B) :=
    (eLpNorm_euclidean_finset_sum_le_of_bound s W hW hq b (fun k _ => hb k) hWb).trans
      (ENNReal.ofReal_le_ofReal (sum_dyadic_error_bound hB K))
  have hHs : eLpNorm (fun ω => ∑ k ∈ s, H k ω) q μ ≤ ENNReal.ofReal (12 * B) :=
    (eLpNorm_finset_sum_le_of_bound s H (fun k hk => (hH k hk).aestronglyMeasurable)
      hq b (fun k _ => hb k) hHb).trans
        (ENNReal.ofReal_le_ofReal (sum_dyadic_error_bound hB K))
  have hEs := (eLpNorm_euclidean_sub_le hE₀ (Finset.measurable_sum s hW) hq).trans
    (add_le_add hE₀b hWs)
  have hlog : 0 ≤ Real.log (2 + (2 : ℝ) ^ K) :=
    Real.log_nonneg (by have := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := K); linarith)
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩
  · refine (add_le_add hXs hPs).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) K])
  · refine hVs.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (by linarith) hlog
  · refine (add_le_add hEs hHs).trans ?_
    rw [← ENNReal.ofReal_add hD (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · refine heb.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end EinsteinRelation.Correctors
