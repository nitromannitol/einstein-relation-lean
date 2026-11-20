import EinsteinFull.Homogenization.OriginCubeAffineMean

/-!
# Linear functions on centered cubes

A linear function has a normalized `L²` norm bounded by its slope and the
side length of the centered triadic cube. This bound is useful for comparing
slopes in the optimizer flatness estimate of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Lemma 2.15.
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

/-- The normalized `L²` norm of a linear function is bounded by the cube
side length times its Euclidean slope, with a dimension factor. -/
theorem cubeLpNorm_vecDot_originCube_le {d : ℕ} (N : ℕ) (b : Vec d) :
    cubeLpNorm (originCube d (N : ℤ)) (2 : ℝ≥0∞) (fun x => vecDot b x) ≤
      (d : ℝ) * (3 : ℝ) ^ N * Real.sqrt (vecNormSq b) := by
  let Q := originCube d (N : ℤ)
  let L : ℝ := (d : ℝ) * (3 : ℝ) ^ N * Real.sqrt (vecNormSq b)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hm : MemLp (fun x => vecDot b x) 2 (normalizedCubeMeasure Q) := by
    simpa only [affineH1_toFun] using (affineH1 (N : ℤ) b).memL2_normalizedCubeMeasure
  have hc : ∀ᵐ x ∂normalizedCubeMeasure Q, x ∈ cubeSet Q := by
    change ∀ᵐ x ∂ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (cubeSet Q), x ∈ cubeSet Q
    exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_cubeSet Q)) _
  have hcoord (i : Fin d) : |b i| ≤ Real.sqrt (vecNormSq b) := by
    have h := Real.sqrt_le_sqrt (sq_apply_le_vecNormSq b i)
    simpa only [Real.sqrt_sq_eq_abs] using h
  have hpoint (x : Vec d) (hx : x ∈ cubeSet Q) : |vecDot b x| ≤ L := by
    have hxcoord (i : Fin d) : |x i| ≤ (3 : ℝ) ^ N := by
      have hi := (mem_cubeSet_originCube_iff.mp hx) i
      simp only [zpow_natCast] at hi
      have hpow : 0 ≤ (3 : ℝ) ^ N := by positivity
      rw [abs_le]
      constructor <;> linarith [hi.1, hi.2]
    unfold vecDot
    calc
      |∑ i : Fin d, b i * x i| ≤ ∑ i : Fin d, |b i * x i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, Real.sqrt (vecNormSq b) * (3 : ℝ) ^ N := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (hcoord i) (hxcoord i) (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = L := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, L]; ring
  calc
    _ ≤ cubeLpNorm Q 2 (fun _ => L) := by
      unfold cubeLpNorm
      apply ENNReal.toReal_mono (memLp_const L (μ := normalizedCubeMeasure Q) (p := (2 : ℝ≥0∞))).eLpNorm_ne_top
      apply eLpNorm_mono_ae hm.aestronglyMeasurable
      filter_upwards [hc] with x hx
      simpa only [Real.norm_eq_abs, abs_of_nonneg hL] using hpoint x hx
    _ = L := by rw [cubeLpNorm_const Q 2 L (by norm_num), Real.norm_eq_abs, abs_of_nonneg hL]

end EinsteinFull.Homogenization
