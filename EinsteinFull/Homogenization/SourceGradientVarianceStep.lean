import EinsteinFull.Homogenization.SourceGradientMismatchVariance
import EinsteinFull.Homogenization.SourceChildGradientContraction

/-!
# One-step optimizer gradient variance estimate

The variance contraction and response defect estimates combine as in the
proof of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization
and Large-Scale Regularity*, Lemma 2.13.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The parent gradient variance is bounded by a contracted child variance and
an adjustable multiple of the expected response decrement. -/
theorem variance_sourceGradient_le_child_variance_add_response_decrement
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (n k : ℕ) (hscale : Q.scale = (n : ℤ) + 2)
    (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) (δ : ℝ) (hδ : 0 < δ) :
    let X := fun a => Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
      (regularCoefficient a).toFun i
    let V := ProbabilityTheory.variance (fun a => Book.Ch02.averageGradient
      (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory
          (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk))
        p q).toSolution i) P
    ProbabilityTheory.variance X P ≤
      (1 + δ) * (1 - (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2) * V +
      (1 + δ⁻¹) * ((4 * d) *
        ((∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk) p q ∂P) -
         (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
          (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P))) := by
  classical
  intro X V
  let Y := fun a : Coefficient d K => descendantsAverage Q 1 (fun R =>
    Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
      (regularCoefficient a).toFun i)
  let Z := X - Y
  have hX : MemLp X 2 P := by
    simpa only [X, sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)] using
      memLp_sourceResponseAverageGradient_cube P Q k hk p q i 2
  have hY : MemLp Y 2 P := by
    have hs := memLp_finsetSum' (descendantsAtDepth Q 1) (fun R _ =>
      memLp_sourceResponseAverageGradient_cube P R k hk p q i 2)
    have hc := hs.const_mul (((descendantsAtDepth Q 1).card : ℝ)⁻¹)
    simpa only [Y, descendantsAverage, Finset.sum_apply, sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)]
      using hc
  have hZ : MemLp Z 2 P := hX.sub hY
  have hdecomp : X = Y + Z := by
    funext a
    simp [Z]
  have hchild := variance_average_childResponseGradient_le P hP hstat Q n k hscale hk p q i
  dsimp only at hchild
  have hYeq : Y = (((3 ^ d : ℕ) : ℝ)⁻¹ •
      ∑ R : {R // R ∈ descendantsAtDepth Q 1}, fun a =>
        Book.Ch02.averageGradient (Book.Ch02.cubeDomain R.1)
          (sourceCoeffOn a (Book.Ch02.cubeDomain R.1) k hk)
          (Book.Ch02.canonicalMaximizer
            (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain R.1)
              (sourceCoeffOn a (Book.Ch02.cubeDomain R.1) k hk)) p q).toSolution i) := by
    funext a
    simp only [Y, descendantsAverage, sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk),
      Pi.smul_apply, smul_eq_mul, Finset.sum_apply, descendantsAtDepth_card, pow_one]
    rw [← Finset.sum_coe_sort (descendantsAtDepth Q 1)]
  rw [← hYeq] at hchild
  change ProbabilityTheory.variance Y P ≤ _ * V at hchild
  have hscale' : Q.scale = ((n + 1 : ℕ) : ℤ) + (1 : ℕ) := by
    rw [hscale]
    push_cast
    ring
  have hz := (integrable_sq_and_variance_sourceGradientMismatch_le hK P hstat Q 1 (n + 1)
    hscale' k hk p q i).2
  change ProbabilityTheory.variance Z P ≤ _ at hz
  have ht := variance_add_le_weighted P hY hZ δ hδ
  rw [← hdecomp] at ht
  calc
    _ ≤ (1 + δ) * ProbabilityTheory.variance Y P +
        (1 + δ⁻¹) * ProbabilityTheory.variance Z P := ht
    _ ≤ _ := by
      simpa only [mul_assoc] using add_le_add
        (mul_le_mul_of_nonneg_left hchild (by linarith : 0 ≤ 1 + δ))
        (mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 1 + δ⁻¹))

end EinsteinFull.Homogenization
