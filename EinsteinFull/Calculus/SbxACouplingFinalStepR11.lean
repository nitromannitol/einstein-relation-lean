import EinsteinFull.Calculus.SbxACouplingInteriorChainR09
import EinsteinRelation.Regeneration.RenewalCarriers

/-! The last spatial and temporal steps of the coupling chain. -/

open EinsteinRelation EinsteinRelation.Regeneration
open EinsteinFull.External.Source.GMP
open scoped NNReal

namespace EinsteinFull.Calculus

/-- The final native ball is inside the coupling region and its inner half
contains both the entire endpoint ball and the penultimate integration ball. -/
theorem a_coupling_final_step_geometry {d : ℕ} (i : Fin d) (R : ℝ) (x : Vec d)
    (hR : 0 < R) (n : ℕ) (hn : 80 ≤ n) :
    let e := x + (9 * R) • unitVector i
    sourceBall e (2 * R) ⊆ couplingRegion i R x ∧
    endpointBall i R x = sourceBall e R ∧
    sourceBall (b_tube_segment_center x e n (n - 1)) (R / 16) ⊆ sourceBall e R := by
  dsimp only
  let e := x + (9 * R) • unitVector i
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hunit : euclideanNorm (unitVector i) = 1 := by
    change Real.sqrt (dotProduct (Pi.single i (1 : ℝ)) (Pi.single i 1)) = 1
    rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]
  have he : euclideanNorm (e - x) = 9 * R := by
    have hv : e - x = (9 * R) • unitVector i := by dsimp [e]; abel
    rw [hv, TimeChange.euclideanNorm_smul, hunit, mul_one,
      abs_of_nonneg (by positivity : 0 ≤ 9 * R)]
  have hgap : euclideanNorm (b_tube_segment_center x e n (n - 1) - e) ≤ R / 8 := by
    have hid : b_tube_segment_center x e n (n - 1) - e =
        -(e - b_tube_segment_center x e n (n - 1)) := by abel
    rw [hid, ← neg_one_smul ℝ, TimeChange.euclideanNorm_smul,
      abs_neg, abs_one, one_mul]
    have hdist := b_tube_segment_distance x e (((n - 1 : ℕ) : ℝ) / (n : ℝ)) 1
    simp only [sub_self, zero_smul, one_smul, zero_add] at hdist
    change euclideanNorm (e - ((1 - ((n - 1 : ℕ) : ℝ) / (n : ℝ)) • x +
      (((n - 1 : ℕ) : ℝ) / (n : ℝ)) • e)) ≤ R / 8
    rw [hdist, he, hnsub]
    have hparam : 1 - ((n : ℝ) - 1) / (n : ℝ) = (n : ℝ)⁻¹ := by
      field_simp; ring
    rw [hparam, abs_of_nonneg (inv_nonneg.mpr hn0.le), inv_mul_eq_div]
    apply (div_le_iff₀ hn0).2
    have hn' : (80 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  refine ⟨?_, rfl, ?_⟩
  · intro z hz
    change euclideanNorm (z - e) < 2 * R at hz
    change euclideanNorm (z - (x + (5 * R) • unitVector i)) < 6 * R
    have hv : e - (x + (5 * R) • unitVector i) = (4 * R) • unitVector i := by
      dsimp [e]; ext j; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have ht := TimeChange.euclideanNorm_add_le (z - e) (e - (x + (5 * R) • unitVector i))
    have hz' : z - e + (e - (x + (5 * R) • unitVector i)) =
        z - (x + (5 * R) • unitVector i) := by abel
    rw [hz', hv, TimeChange.euclideanNorm_smul, hunit, mul_one,
      abs_of_nonneg (by positivity : 0 ≤ 4 * R)] at ht
    linarith
  · intro z hz
    change euclideanNorm (z - b_tube_segment_center x e n (n - 1)) < R / 16 at hz
    change euclideanNorm (z - e) < R
    have ht := TimeChange.euclideanNorm_add_le
      (z - b_tube_segment_center x e n (n - 1))
      (b_tube_segment_center x e n (n - 1) - e)
    have hz' : z - b_tube_segment_center x e n (n - 1) +
        (b_tube_segment_center x e n (n - 1) - e) = z - e := by abel
    rw [hz'] at ht
    linarith

/-- Equal positive substeps sum to the actual regeneration grid spacing. -/
theorem a_regen_delta_subdivision (mu : ℝ) (hmu : 0 < mu) (N : ℕ) (hN : 80 ≤ N) :
    let τ : ℝ≥0 := Renewal.regenDelta mu / (N : ℝ≥0)
    (N : ℝ≥0) * τ = Renewal.regenDelta mu ∧ 0 < τ := by
  dsimp only
  have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hΔ : 0 < Renewal.regenDelta mu :=
    Real.toNNReal_pos.2 (inv_pos.2 (pow_pos hmu 2))
  exact ⟨mul_div_cancel₀ _ hN0, div_pos hΔ (pos_iff_ne_zero.mpr hN0)⟩

end EinsteinFull.Calculus

