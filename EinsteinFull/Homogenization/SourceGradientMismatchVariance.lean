import EinsteinFull.Homogenization.SourceGradientMismatchAverage
import Mathlib.Probability.Moments.Variance

/-!
# Variance of the optimizer gradient mismatch

The response decrement bounds the variance of the difference between a parent
optimizer gradient and the average of its descendants, following Armstrong,
Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Lemma 2.13.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The squared parent-to-descendant-average mismatch is integrable, and its
variance is bounded by the expected response decrement. -/
theorem integrable_sq_and_variance_sourceGradientMismatch_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    let Z := fun a => Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q
        (regularCoefficient a).toFun i -
      descendantsAverage Q j (fun R =>
        Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
          (regularCoefficient a).toFun i)
    Integrable (fun a => (Z a) ^ 2) P ∧
    ProbabilityTheory.variance Z P ≤ (4 * d) *
      ((∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P) -
      (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P)) := by
  classical
  intro Z
  let G := fun a : Coefficient d K => descendantsAverage Q j (fun R =>
    vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
        (regularCoefficient a).toFun -
      Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
        (regularCoefficient a).toFun))
  have hG := integrable_and_integral_sourceGradientMismatch_le hK P hstat Q j n hscale k hk p q
  change Integrable G P ∧ _ at hG
  have hcoord (R : TriadicCube d) : AEMeasurable (fun a =>
      Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
        (regularCoefficient a).toFun i) P :=
    (aemeasurable_pi_iff.mp (aemeasurable_sourceResponseGradientAverage P R R p q)) i
  have hY : AEMeasurable (fun a => descendantsAverage Q j (fun R =>
      Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
        (regularCoefficient a).toFun i)) P := by
    dsimp only [descendantsAverage]
    exact (Finset.aemeasurable_fun_sum _ (fun R _ => hcoord R)).const_mul _
  have hZ : AEMeasurable Z P := (hcoord Q).sub hY
  have hbound (a : Coefficient d K) : (Z a) ^ 2 ≤ G a :=
    sq_sourceGradientAverage_sub_descendantsAverage_le_meanMismatch a Q j p q i
  have hsq : Integrable (fun a => (Z a) ^ 2) P := by
    apply hG.1.mono' (hZ.pow_const 2).aestronglyMeasurable
    filter_upwards [] with a
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hbound a
  refine ⟨hsq, ?_⟩
  calc
    ProbabilityTheory.variance Z P ≤ ∫ a, (Z a) ^ 2 ∂P :=
      ProbabilityTheory.variance_le_expectation_sq hZ.aestronglyMeasurable
    _ ≤ ∫ a, G a ∂P := integral_mono hsq hG.1 hbound
    _ ≤ _ := hG.2

end EinsteinFull.Homogenization
