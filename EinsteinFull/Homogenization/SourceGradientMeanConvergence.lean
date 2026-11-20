import EinsteinFull.Homogenization.SourceGradientDescendantMean
import EinsteinFull.Homogenization.SourceResponseAnnealed

/-!
# Convergence of mean optimizer gradients

The response decrement controls the mean optimizer gradient as in Armstrong,
Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, equation (2.44).
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The expected response decrement controls each coordinate of the change in
mean optimizer gradients, for arbitrary loadings. -/
theorem sq_integral_sourceGradient_sub_le_response_decrement
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (m n k : ℕ) (hmn : m ≤ n) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    let F := fun (r : ℕ) (a : Coefficient d K) => Book.Ch02.averageGradient
      (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk)) p q).toSolution i
    let J := fun (r : ℕ) (a : Coefficient d K) => Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk) p q
    (∀ r, Integrable (F r) P ∧ Integrable (J r) P) ∧
    ((∫ a, F n a ∂P) - (∫ a, F m a ∂P)) ^ 2 ≤
      (4 * d) * ((∫ a, J m a ∂P) - (∫ a, J n a ∂P)) := by
  classical
  intro F J
  refine ⟨fun r => ⟨(memLp_sourceResponseAverageGradient_cube P
    (originCube d (r : ℤ)) k hk p q i 2).integrable (by norm_num),
    integrable_sourceResponseJ hK P r k hk p q⟩, ?_⟩
  let Q := originCube d (n : ℤ)
  let j := n - m
  have hscale : Q.scale = (m : ℤ) + j := by
    dsimp [Q, j]
    simp only [originCube, Nat.cast_sub hmn]
    ring
  let X := fun a : Coefficient d K => Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
    (regularCoefficient a).toFun i
  let Y := fun a : Coefficient d K => descendantsAverage Q j (fun R =>
    Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
      (regularCoefficient a).toFun i)
  have hX : Integrable X P := by
    simpa only [X, sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)] using
      (memLp_sourceResponseAverageGradient_cube P Q k hk p q i 2).integrable (by norm_num)
  have hY : Integrable Y P := by
    have hs := memLp_finsetSum' (descendantsAtDepth Q j) (fun R _ =>
      memLp_sourceResponseAverageGradient_cube P R k hk p q i 2)
    have hc := (hs.const_mul (((descendantsAtDepth Q j).card : ℝ)⁻¹)).integrable (by norm_num)
    simpa only [Y, descendantsAverage, Finset.sum_apply,
      sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)] using hc
  have h := (sq_integral_sourceGradientMismatch_le hK P hstat Q j m hscale k hk p q i).2.2.2
  change (∫ a, (X a - Y a) ∂P) ^ 2 ≤ _ at h
  rw [integral_sub hX hY, integral_descendantsAverage_sourceGradient_eq_origin P hstat Q j m
    hscale k hk p q i] at h
  simpa only [X, Q, F, J, sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)] using h

/-- Every coordinate of the mean response-optimizer gradient has a limit. -/
theorem exists_tendsto_integral_sourceGradient
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    let F := fun (r : ℕ) (a : Coefficient d K) => Book.Ch02.averageGradient
      (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk)) p q).toSolution i
    (∀ r, Integrable (F r) P) ∧
    ∃ L : ℝ, Tendsto (fun r => ∫ a, F r a ∂P) atTop (𝓝 L) := by
  intro F
  refine ⟨fun r => (memLp_sourceResponseAverageGradient_cube P
    (originCube d (r : ℤ)) k hk p q i 2).integrable (by norm_num), ?_⟩
  let G : ℕ → ℝ := fun r => ∫ a, F r a ∂P
  let R : ℕ → ℝ := fun r => ∫ a, Book.Ch02.responseJ
    (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
    (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk) p q ∂P
  have hR : CauchySeq R := (tendsto_expected_sourceResponseJ hK P hstat k hk p q).cauchySeq
  have hG : CauchySeq G := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hc : 0 < (4 * (d : ℝ) + 1) := by positivity
    have hδ : 0 < ε ^ 2 / (4 * (d : ℝ) + 1) := div_pos (sq_pos_of_pos hε) hc
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hR) _ hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    have hd := hN m hm n hn
    rw [Real.dist_eq] at hd ⊢
    have hb (a b : ℕ) (hab : a ≤ b) : (G b - G a) ^ 2 ≤
        (4 * (d : ℝ)) * (R a - R b) := by
      simpa only [G, R, F] using
        (sq_integral_sourceGradient_sub_le_response_decrement hK P hstat a b k hab hk p q i).2
    have hbound : (G m - G n) ^ 2 ≤ (4 * (d : ℝ)) * |R m - R n| := by
      rcases le_total m n with hmn | hnm
      · have h := hb m n hmn
        have ha := le_abs_self (R m - R n)
        have hc' : 0 ≤ (4 * (d : ℝ)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left ha hc']
      · have h := hb n m hnm
        have ha := neg_le_abs (R m - R n)
        have hc' : 0 ≤ (4 * (d : ℝ)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left ha hc']
    have hden : (4 * (d : ℝ)) * |R m - R n| < ε ^ 2 := by
      have hmul := (lt_div_iff₀ hc).mp hd
      have ha := abs_nonneg (R m - R n)
      nlinarith
    have habs := abs_nonneg (G m - G n)
    have habssq : |G m - G n| ^ 2 = (G m - G n) ^ 2 := sq_abs _
    nlinarith
  exact cauchySeq_tendsto_of_complete hG

end EinsteinFull.Homogenization
