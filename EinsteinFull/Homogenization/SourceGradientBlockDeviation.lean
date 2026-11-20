import EinsteinFull.Homogenization.SourceResponseGradientExpectation
import EinsteinFull.Homogenization.SourceOptimizerGradientBridge
import EinsteinFull.Homogenization.SourceOptimizerGradientMoments

/-!
# Block deviations of response optimizer gradients

The optimizer gradient on a parent cube is compared with the optimizers on
its descendants by the second-variation estimate of Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The mean squared deviation of parent optimizer block averages is bounded
by the response decrement and the corresponding deviations of descendant
optimizers. All terms in the expectation are integrable. -/
theorem integrable_and_integral_sourceGradientBlockDeviation_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q b : Vec d) :
    let G := fun a => descendantsAverage Q j (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
        (regularCoefficient a).toFun - b))
    let H := fun a => descendantsAverage Q j (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
        (regularCoefficient a).toFun - b))
    Integrable G P ∧ Integrable H P ∧
    (∫ a, G a ∂P) ≤ (8 * d) *
      ((∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P) -
      (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P)) +
      2 * ∫ a, H a ∂P := by
  classical
  intro G H
  let M := fun a : Coefficient d K => descendantsAverage Q j (fun R =>
    vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
        (regularCoefficient a).toFun -
      Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
        (regularCoefficient a).toFun))
  have hM := integrable_and_integral_sourceGradientMismatch_le hK P hstat Q j n hscale k hk p q
  change Integrable M P ∧ _ at hM
  have hH : Integrable H P := by
    have hR (R : TriadicCube d) : Integrable (fun a =>
        vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
          (regularCoefficient a).toFun - b)) P := by
      have hi (i : Fin d) : MemLp (fun a =>
          (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
            (regularCoefficient a).toFun - b) i) 2 P := by
        have h := (memLp_sourceResponseAverageGradient_cube P R k hk p q i 2).sub
          (memLp_const (b i))
        change MemLp (fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain R)
          (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)
          (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain R)
            (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)) p q).toSolution i - b i) 2 P at h
        simpa only [Pi.sub_apply, sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)] using h
      have hs := integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ => (hi i).integrable_sq)
      simpa only [vecNormSq, vecDot, sq] using hs
    dsimp only [H, descendantsAverage]
    exact (integrable_finsetSum _ (fun R _ => hR R)).const_mul _
  have hmeas : AEMeasurable G P := by
    have hR (R : TriadicCube d) : AEMeasurable (fun a =>
        vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
          (regularCoefficient a).toFun - b)) P := by
      have h := aemeasurable_sourceResponseGradientAverage P Q R p q
      have hi (i : Fin d) : AEMeasurable (fun a =>
          Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
            (regularCoefficient a).toFun i - b i) P :=
        ((aemeasurable_pi_iff.mp h) i).sub aemeasurable_const
      simpa [vecNormSq, vecDot] using
        (Finset.univ.aemeasurable_fun_sum (μ := P) (fun i _ => (hi i).mul (hi i)))
    dsimp only [G, descendantsAverage]
    exact (Finset.aemeasurable_fun_sum _ (fun R _ => hR R)).const_mul _
  have hpoint (a : Coefficient d K) : G a ≤ 2 * M a + 2 * H a := by
    have hR (R : TriadicCube d) :
        vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
          (regularCoefficient a).toFun - b) ≤
        2 * vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
          (regularCoefficient a).toFun -
            Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
              (regularCoefficient a).toFun) +
        2 * vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
          (regularCoefficient a).toFun - b) := by
      have h := vecNormSq_add_le
        (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
            (regularCoefficient a).toFun -
          Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
            (regularCoefficient a).toFun)
        (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
            (regularCoefficient a).toFun - b)
      simpa only [sub_add_sub_cancel, mul_add] using h
    calc
      G a ≤ descendantsAverage Q j (fun R =>
          2 * vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
            (regularCoefficient a).toFun -
              Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
                (regularCoefficient a).toFun) +
          2 * vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
            (regularCoefficient a).toFun - b)) :=
        descendantsAverage_le_descendantsAverage Q j (fun R _ => hR R)
      _ = 2 * M a + 2 * H a := by
        simp only [M, H, descendantsAverage, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
  have hG : Integrable G P := by
    apply ((hM.1.const_mul 2).add (hH.const_mul 2)).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with a
    rw [Real.norm_of_nonneg (descendantsAverage_nonneg Q j _ (fun R _ => vecNormSq_nonneg _))]
    exact hpoint a
  refine ⟨hG, hH, ?_⟩
  calc
    _ ≤ ∫ a, 2 * M a + 2 * H a ∂P :=
      integral_mono hG ((hM.1.const_mul 2).add (hH.const_mul 2)) hpoint
    _ = 2 * (∫ a, M a ∂P) + 2 * ∫ a, H a ∂P := by
      rw [integral_add (hM.1.const_mul 2) (hH.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ _ := by linarith [hM.2]

end EinsteinFull.Homogenization
