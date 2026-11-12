import EinsteinRelation.Correctors.ScalarDecompositionSums
import EinsteinRelation.Correctors.ScalarCorrectedFunction
import EinsteinRelation.Correctors.ScalarGlobalMomentBounds

/-! # Coordinate moments of the corrected drift flux

Source: `paper/main.tex:1062–1081`.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- One-scale drift flux bound (`paper/main.tex:1062–1081`). -/
theorem scalarCorrected_drift_coordinate_bounds (d : ℕ) (L A B : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p r a : ℝ} (hp : 1 ≤ p) (hr : 1 ≤ r) (ha : 1 ≤ a)
    (abar : Mat d) (habar : ∀ i j, |abar i j| ≤ L)
    (u : Ω → ℝ) (Du : Ω → Vec d) (Sig : Fin d → Ω → Mat d)
    (hu : Measurable u) (hDu : Measurable Du) (hSig : ∀ j, Measurable (Sig j))
    (hub : eLpNorm u (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (B * r))
    (hDub : ∀ i, eLpNorm (fun ω => Du ω i) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal B)
    (hSigb : ∀ j i k, eLpNorm (fun ω => Sig j ω i k) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (A * a)),
      ∀ i k, eLpNorm (fun ω => (u ω • (abar.mulVec (unitVector i)) +
        ∑ j, Du ω j • (fun k => Sig j ω i k)) k) (ENNReal.ofReal (2 * p)) μ ≤
        ENNReal.ofReal (C * (r + a)) := by
  let C := B * (L + (d : ℝ) * A)
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ p r a hp hr ha abar habar u Du Sig hu hDu hSig hub hDub hSigb i k
  have hp2_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) := by
    rw [ENNReal.one_le_ofReal]
    linarith
  have hp4_pos : 0 < 4 * p := by linarith
  have hp4_ne_zero : ENNReal.ofReal (4 * p) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact hp4_pos
  have hμ_ne_zero : μ ≠ 0 := IsProbabilityMeasure.ne_zero μ
  have h_expr : (fun ω => (u ω • (abar.mulVec (unitVector i)) +
      ∑ j, Du ω j • (fun k => Sig j ω i k)) k) =
      (fun ω => u ω * (abar k i) + ∑ j : Fin d, Du ω j * Sig j ω i k) := by
    ext ω
    calc
      (u ω • (abar.mulVec (unitVector i)) + ∑ j, Du ω j • (fun k => Sig j ω i k)) k
          = (u ω • (abar.mulVec (unitVector i))) k + (∑ j, Du ω j • (fun k => Sig j ω i k)) k := rfl
      _ = u ω * ((abar.mulVec (unitVector i)) k) + ∑ j, (Du ω j • (fun k => Sig j ω i k)) k := by
        simp [Pi.smul_apply, smul_eq_mul]
      _ = u ω * (∑ x, abar k x * (unitVector i) x) + ∑ j, Du ω j * Sig j ω i k := by
        simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      _ = u ω * (abar k i) + ∑ j : Fin d, Du ω j * Sig j ω i k := by
        simp [unitVector, Pi.single_apply]
  rw [h_expr]
  have hu_aest : AEStronglyMeasurable u μ := hu.aestronglyMeasurable
  have hDu_aest (i' : Fin d) : AEStronglyMeasurable (fun ω => Du ω i') μ :=
    (continuous_apply i').comp_aestronglyMeasurable hDu.aestronglyMeasurable
  have hSig_aest (j i' k' : Fin d) : AEStronglyMeasurable (fun ω => Sig j ω i' k') μ := by
    have h_cont : Continuous (fun (M : Mat d) => M i' k') :=
      (continuous_apply k').comp (continuous_apply i')
    have h_meas : Measurable (fun ω => Sig j ω i' k') :=
      (h_cont.measurable).comp (hSig j)
    exact h_meas.aestronglyMeasurable
  have hconst_aest : AEStronglyMeasurable (fun _ : Ω => (abar k i : ℝ)) μ :=
    aestronglyMeasurable_const
  have h_const_norm (c : ℝ) : eLpNorm (fun _ : Ω => c) (ENNReal.ofReal (4 * p)) μ =
      ENNReal.ofReal |c| := by
    rw [eLpNorm_const c hp4_ne_zero hμ_ne_zero, measure_univ]
    have h_enorm : ‖c‖ₑ = ENNReal.ofReal |c| := by
      rw [← Real.enorm_eq_ofReal (abs_nonneg c)]
      simp
    simp [h_enorm]
  have h_first : eLpNorm (fun ω => u ω * (abar k i)) (ENNReal.ofReal (2 * p)) μ ≤
      ENNReal.ofReal (L * B * r) := by
    calc
      eLpNorm (fun ω => u ω * (abar k i)) (ENNReal.ofReal (2 * p)) μ ≤
          eLpNorm u (ENNReal.ofReal (4 * p)) μ *
          eLpNorm (fun _ : Ω => (abar k i : ℝ)) (ENNReal.ofReal (4 * p)) μ :=
        eLpNorm_mul_le_holder_four hp hu_aest hconst_aest
      _ ≤ ENNReal.ofReal (B * r) *
          eLpNorm (fun _ : Ω => (abar k i : ℝ)) (ENNReal.ofReal (4 * p)) μ :=
        mul_le_mul_of_nonneg_right hub (by positivity)
      _ = ENNReal.ofReal (B * r) * ENNReal.ofReal |abar k i| := by rw [h_const_norm (abar k i)]
      _ ≤ ENNReal.ofReal (B * r) * ENNReal.ofReal L :=
        mul_le_mul_of_nonneg_left
          (ENNReal.ofReal_le_ofReal (habar k i)) (by positivity)
      _ = ENNReal.ofReal (B * r * L) := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ B * r)]
      _ = ENNReal.ofReal (L * B * r) := by ring
  have h_prod (j : Fin d) : eLpNorm (fun ω => Du ω j * Sig j ω i k) (ENNReal.ofReal (2 * p)) μ ≤
      ENNReal.ofReal (B * (A * a)) := by
    calc
      eLpNorm (fun ω => Du ω j * Sig j ω i k) (ENNReal.ofReal (2 * p)) μ ≤
          eLpNorm (fun ω => Du ω j) (ENNReal.ofReal (4 * p)) μ *
          eLpNorm (fun ω => Sig j ω i k) (ENNReal.ofReal (4 * p)) μ :=
        eLpNorm_mul_le_holder_four hp (hDu_aest j) (hSig_aest j i k)
      _ ≤ ENNReal.ofReal B *
          eLpNorm (fun ω => Sig j ω i k) (ENNReal.ofReal (4 * p)) μ :=
        mul_le_mul_of_nonneg_right (hDub j) (by positivity)
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal (A * a) :=
        mul_le_mul_of_nonneg_left (hSigb j i k) (by positivity)
      _ = ENNReal.ofReal (B * (A * a)) := by
        rw [ENNReal.ofReal_mul hB]
  have h_sum : eLpNorm (fun ω => ∑ j : Fin d, Du ω j * Sig j ω i k)
      (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal ((d : ℝ) * B * (A * a)) := by
    calc
      eLpNorm (fun ω => ∑ j : Fin d, Du ω j * Sig j ω i k) (ENNReal.ofReal (2 * p)) μ ≤
          ∑ j : Fin d, eLpNorm (fun ω => Du ω j * Sig j ω i k) (ENNReal.ofReal (2 * p)) μ :=
        eLpNorm_finset_sum_le (Finset.univ : Finset (Fin d))
          (fun j ω => Du ω j * Sig j ω i k)
          (fun j hj => (hDu_aest j).mul (hSig_aest j i k))
          hp2_one
      _ ≤ ∑ _j : Fin d, ENNReal.ofReal (B * (A * a)) :=
        Finset.sum_le_sum (fun j _ => h_prod j)
      _ = (d : ℝ≥0∞) * ENNReal.ofReal (B * (A * a)) := by simp
      _ = ENNReal.ofReal (B * (A * a)) * (d : ℝ≥0∞) := mul_comm _ _
      _ = ENNReal.ofReal (B * (A * a)) * ENNReal.ofReal (d : ℝ) := by simp
      _ = ENNReal.ofReal ((B * (A * a)) * (d : ℝ)) := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ B * (A * a))]
      _ = ENNReal.ofReal ((d : ℝ) * B * (A * a)) := by ring
  have h_sum_aest : AEStronglyMeasurable
      (fun ω => ∑ j : Fin d, Du ω j * Sig j ω i k) μ := by
    simpa [Finset.sum_fn] using Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin d))
      (fun j _ => (hDu_aest j).mul (hSig_aest j i k))
  have h_first_aest : AEStronglyMeasurable (fun ω => u ω * (abar k i)) μ :=
    hu_aest.mul hconst_aest
  have h_total : eLpNorm (fun ω => u ω * (abar k i) + ∑ j : Fin d, Du ω j * Sig j ω i k)
      (ENNReal.ofReal (2 * p)) μ ≤
      ENNReal.ofReal (L * B * r) + ENNReal.ofReal ((d : ℝ) * B * (A * a)) := by
    calc
      eLpNorm (fun ω => u ω * (abar k i) + ∑ j : Fin d, Du ω j * Sig j ω i k)
          (ENNReal.ofReal (2 * p)) μ ≤
          eLpNorm (fun ω => u ω * (abar k i)) (ENNReal.ofReal (2 * p)) μ +
          eLpNorm (fun ω => ∑ j : Fin d, Du ω j * Sig j ω i k) (ENNReal.ofReal (2 * p)) μ :=
        eLpNorm_add_le h_first_aest h_sum_aest hp2_one
      _ ≤ ENNReal.ofReal (L * B * r) +
          eLpNorm (fun ω => ∑ j : Fin d, Du ω j * Sig j ω i k) (ENNReal.ofReal (2 * p)) μ := by
        gcongr
      _ ≤ ENNReal.ofReal (L * B * r) + ENNReal.ofReal ((d : ℝ) * B * (A * a)) := by
        gcongr
  have h_final : ENNReal.ofReal (L * B * r) + ENNReal.ofReal ((d : ℝ) * B * (A * a)) ≤
      ENNReal.ofReal (C * (r + a)) := by
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ L * B * r)
      (by positivity : 0 ≤ (d : ℝ) * B * (A * a))]
    refine ENNReal.ofReal_le_ofReal ?_
    dsimp [C]
    have hr_nonneg : 0 ≤ r := by linarith
    have ha_nonneg : 0 ≤ a := by linarith
    have ha0 : 0 ≤ a := by linarith
    have hr0 : 0 ≤ r := by linarith
    have hposd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    have h1 : 0 ≤ B * L * a := by positivity
    have h2 : 0 ≤ B * (d : ℝ) * A * r := by positivity
    have hineq : L * B * r + (d : ℝ) * B * (A * a) ≤ B * (L + (d : ℝ) * A) * (r + a) := by
      nlinarith
    exact hineq
  exact h_total.trans h_final

end EinsteinRelation.Correctors
