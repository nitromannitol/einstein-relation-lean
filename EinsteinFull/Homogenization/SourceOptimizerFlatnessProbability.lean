import EinsteinFull.Homogenization.MajorantProbability

/-!
# Probability decay of optimizer flatness

Square-integrable multiscale majorants give uniform convergence in probability
of the rescaled optimizer remainders. The argument is related to Lemma 2.15
of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*.
-/

open scoped ENNReal
open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Under stationarity and finite-range dependence, the probabilities that
rescaled optimizer remainders exceed a positive threshold have a common
bound tending to zero, uniformly over unit loadings. -/
theorem exists_tendsto_zero_sourceOptimizer_flatness_probability
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ → ℝ, Tendsto T atTop (𝓝 0) ∧
      ∀ (N : ℕ) (p q : Vec d), vecNormSq p < 1 → vecNormSq q < 1 →
      let Q := originCube d (N : ℤ)
      let F := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain Q)
            (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk)) p q).toSolution
      let b := fun i => ∫ a, F a i ∂P
      (∀ i, Integrable (fun a => F a i) P) ∧
      P.real {a | ε ≤ ((3 : ℝ) ^ N)⁻¹ *
        (let U := Book.Ch02.cubeDomain Q
         let A := sourceCoeffOn a U k hk
         let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).toSolution
         cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v.toH1 x - vecDot b x))} ≤ T N := by
  obtain ⟨C, hC, B, hB, hmajor⟩ :=
    exists_tendsto_zero_sourceOptimizer_flatness_majorant hK P hP hstat k hk
  let T : ℕ → ℝ := fun N => (C ^ 2 / ε ^ 2) * B N
  have hT : Tendsto T atTop (𝓝 0) := by
    have h := hB.const_mul (C ^ 2 / ε ^ 2)
    simpa only [mul_zero] using h
  refine ⟨T, hT, ?_⟩
  intro N p q hp hq Q F b
  obtain ⟨hF, H, hmem, hH, hbound, hint, hsecond⟩ := hmajor N p q hp hq
  change (∀ i, Integrable (fun a => F a i) P) at hF
  let f := fun a : Coefficient d K => ((3 : ℝ) ^ N)⁻¹ *
    (let U := Book.Ch02.cubeDomain Q
     let A := sourceCoeffOn a U k hk
     let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U A) p q).toSolution
     cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v.toH1 x - vecDot b x))
  have hpow : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have hf (a : Coefficient d K) : f a ≤ C * H a := by
    have hb := hbound a
    change _ ≤ C * (3 : ℝ) ^ N * H a at hb
    calc
      f a ≤ ((3 : ℝ) ^ N)⁻¹ * (C * (3 : ℝ) ^ N * H a) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hpow.le)
      _ = C * H a := by field_simp
  have h := measureReal_ge_le_of_squareIntegrable_majorant P f H C ε (B N)
    hC hε hH hf hmem hsecond
  refine ⟨hF, ?_⟩
  change P.real {a | ε ≤ f a} ≤ T N
  convert h using 1; dsimp [T]; ring

end EinsteinFull.Homogenization
