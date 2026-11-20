import EinsteinFull.Homogenization.SourceGradientMismatchVariance
import EinsteinFull.Homogenization.SourceOptimizerGradientMoments
import EinsteinFull.Homogenization.SourceGradientMeanStationarity

/-!
# Mean optimizer gradient mismatch

The response decrement controls the mean optimizer gradient mismatch, as in
Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, equation (2.44).
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The square of the expected parent-to-descendant gradient mismatch is
controlled by the expected response decrement. -/
theorem sq_integral_sourceGradientMismatch_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    Integrable (fun a => Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
      (regularCoefficient a).toFun i - descendantsAverage Q j (fun R =>
      Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
        (regularCoefficient a).toFun i)) P ∧
    Integrable (fun a => Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d n)) k hk) p q) P ∧
    Integrable (fun a => Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q) P ∧
    (∫ a, (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
        (regularCoefficient a).toFun i -
      descendantsAverage Q j (fun R =>
        Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
          (regularCoefficient a).toFun i)) ∂P) ^ 2 ≤ (4 * d) *
      ((∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P) -
      (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P)) := by
  classical
  let X := fun a : Coefficient d K => Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
    (regularCoefficient a).toFun i
  let Y := fun a : Coefficient d K => descendantsAverage Q j (fun R =>
    Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
      (regularCoefficient a).toFun i)
  let Z := X - Y
  have hX : MemLp X 2 P := by
    simpa only [X, sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)] using
      memLp_sourceResponseAverageGradient_cube P Q k hk p q i 2
  have hY : MemLp Y 2 P := by
    have hs := memLp_finsetSum' (descendantsAtDepth Q j) (fun R _ =>
      memLp_sourceResponseAverageGradient_cube P R k hk p q i 2)
    have hc := hs.const_mul (((descendantsAtDepth Q j).card : ℝ)⁻¹)
    simpa only [Y, descendantsAverage, Finset.sum_apply,
      sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)] using hc
  have hZ : MemLp Z 2 P := hX.sub hY
  refine ⟨(hX.sub hY).integrable (by norm_num), integrable_sourceResponseJ hK P n k hk p q,
    integrable_sourceResponseJ_cube hK P Q k hk p q, ?_⟩
  let G := fun a : Coefficient d K => descendantsAverage Q j (fun R =>
    vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
        (regularCoefficient a).toFun -
      Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
        (regularCoefficient a).toFun))
  have hG := integrable_and_integral_sourceGradientMismatch_le hK P hstat Q j n hscale k hk p q
  change Integrable G P ∧ _ at hG
  have hZsq : Integrable (fun a => (Z a) ^ 2) P :=
    (integrable_sq_and_variance_sourceGradientMismatch_le hK P hstat Q j n hscale k hk p q i).1
  have hmean : (∫ a, Z a ∂P) ^ 2 ≤ ∫ a, (Z a) ^ 2 ∂P := by
    have hv := ProbabilityTheory.variance_nonneg Z P
    rw [ProbabilityTheory.variance_eq_sub hZ] at hv
    exact sub_nonneg.mp hv
  change (∫ a, Z a ∂P) ^ 2 ≤ _
  calc
    _ ≤ ∫ a, (Z a) ^ 2 ∂P := hmean
    _ ≤ ∫ a, G a ∂P := integral_mono hZsq hG.1 (fun a =>
      sq_sourceGradientAverage_sub_descendantsAverage_le_meanMismatch a Q j p q i)
    _ ≤ _ := hG.2

end EinsteinFull.Homogenization
