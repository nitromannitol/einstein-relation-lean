import EinsteinFull.Homogenization.SourceOptimizerAnnealedSlope
import EinsteinFull.Homogenization.SquareIntegrableMajorant

/-!
# Optimizer flatness moments

The multiscale majorant controls the second moment of the normalized optimizer
remainder whenever that remainder is almost everywhere measurable. This is a
conditional qualitative counterpart of the flatness estimate in Lemma 2.15 of Armstrong, Kuusi
and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*.
-/

open scoped ENNReal
open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- If the normalized optimizer remainder is almost everywhere measurable, its
second moment has a common vanishing bound over unit loadings. -/
theorem exists_tendsto_zero_sourceOptimizer_annealedSlope_moment_of_aemeasurable
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) :
    ∃ B : ℕ → ℝ, Tendsto B atTop (𝓝 0) ∧
      ∀ (n : ℕ) (p q : Vec d), vecNormSq p < 1 → vecNormSq q < 1 →
      let Q := originCube d ((n + 1 : ℕ) : ℤ)
      let b := matVecMul (annealedDualMatrix P n k hk) q - p
      let f := fun a : Coefficient d K => ((3 : ℝ) ^ (n + 1))⁻¹ *
        (let U := Book.Ch02.cubeDomain Q
         let A := sourceCoeffOn a U k hk
         let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).toSolution
         cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v.toH1 x - vecDot b x))
      AEMeasurable f P → MemLp f 2 P ∧ Integrable (fun a => (f a) ^ 2) P ∧
        (∫ a, (f a) ^ 2 ∂P) ≤ B n := by
  obtain ⟨C, hC, B, hB, hmajor⟩ :=
    exists_tendsto_zero_sourceOptimizer_annealedSlope_majorant hK P hP hstat k hk
  let T : ℕ → ℝ := fun n => C ^ 2 * B n
  have hT : Tendsto T atTop (𝓝 0) := by
    have h := hB.const_mul (C ^ 2)
    simpa only [mul_zero] using h
  refine ⟨T, hT, ?_⟩
  intro n p q hp hq Q b f hmeas
  obtain ⟨hF, H, hmem, hH, hbound, hint, hsecond⟩ := hmajor n p q hp hq
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (n + 1) := by positivity
  have hf (a : Coefficient d K) : 0 ≤ f a := by
    dsimp only [f]
    exact mul_nonneg (inv_nonneg.mpr hpow.le) (cubeLpNorm_nonneg _ _ _)
  have hbound' (a : Coefficient d K) : f a ≤ C * H a := by
    have h := hbound a
    change _ ≤ C * (3 : ℝ) ^ (n + 1) * H a at h
    calc
      f a ≤ ((3 : ℝ) ^ (n + 1))⁻¹ * (C * (3 : ℝ) ^ (n + 1) * H a) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hpow.le)
      _ = C * H a := by field_simp
  exact memLp_and_integral_sq_le_of_majorant P f H C (B n)
    hC hf hH hbound' hmeas hmem hsecond

end EinsteinFull.Homogenization
