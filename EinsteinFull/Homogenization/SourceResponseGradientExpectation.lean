import EinsteinFull.Homogenization.SourceResponseGradientBound
import EinsteinFull.Homogenization.SourceResponseGradientMeasurability
import EinsteinFull.Homogenization.SourceResponseExpectedDefect

/-!
# Expected optimizer gradient mismatch

The second-variation bound and stationarity in Lemma 2.13 of Armstrong, Kuusi
and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, control the expected squared mismatch by a response decrement.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The integrable mean squared parent-child gradient mismatch is controlled by
`4d` times the decrease of expected response from the descendant to parent scale. -/
theorem integrable_and_integral_sourceGradientMismatch_le
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    let G := fun a => descendantsAverage Q j (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
          (regularCoefficient a).toFun -
        Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
          (regularCoefficient a).toFun))
    Integrable G P ∧
    (∫ a, G a ∂P) ≤ (4 * d) *
      ((∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P) -
      (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P)) := by
  classical
  intro G
  let D := fun a => descendantsAverage Q j (fun R => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
      (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q) -
    Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q
  have hD : Integrable D P := by
    have hs : Integrable (fun a => ∑ R ∈ descendantsAtDepth Q j,
        Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
          (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q) P :=
      integrable_finsetSum _ (fun R _ => integrable_sourceResponseJ_cube hK P R k hk p q)
    have havg := hs.const_mul (((descendantsAtDepth Q j).card : ℝ)⁻¹)
    have havg' : Integrable (fun a => descendantsAverage Q j (fun R =>
        Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
          (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q)) P := by
      simpa only [descendantsAverage] using havg
    exact havg'.sub (integrable_sourceResponseJ_cube hK P Q k hk p q)
  have hmeas : AEMeasurable G P := by
    have hR (R : TriadicCube d) : AEMeasurable (fun a =>
        vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
            (regularCoefficient a).toFun -
          Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
            (regularCoefficient a).toFun)) P := by
      have h₁ := aemeasurable_sourceResponseGradientAverage P Q R p q
      have h₂ := aemeasurable_sourceResponseGradientAverage P R R p q
      have hi (i : Fin d) := ((aemeasurable_pi_iff.mp h₁) i).sub ((aemeasurable_pi_iff.mp h₂) i)
      simpa [vecNormSq, vecDot] using
        (Finset.univ.aemeasurable_fun_sum (μ := P)
          (fun i _ => (hi i).mul (hi i)))
    dsimp only [G, descendantsAverage]
    exact (Finset.aemeasurable_fun_sum _ (fun R _ => hR R)).const_mul _
  have hnonneg (a : Coefficient d K) : 0 ≤ G a := by
    dsimp only [G]
    apply descendantsAverage_nonneg
    intro R _
    exact vecNormSq_nonneg _
  have hpoint (a : Coefficient d K) : G a ≤ (4 * d) * D a :=
    descendantsAverage_sourceGradientMismatch_le_four_mul_dim_mul_defect a Q j k hk p q
  have hG : Integrable G P := by
    apply (hD.const_mul (4 * d)).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with a
    rw [Real.norm_of_nonneg (hnonneg a)]
    exact hpoint a
  refine ⟨hG, ?_⟩
  calc
    (∫ a, G a ∂P) ≤ ∫ a, (4 * d) * D a ∂P :=
      integral_mono hG (hD.const_mul (4 * d)) hpoint
    _ = (4 * d) * ∫ a, D a ∂P := integral_const_mul _ _
    _ = _ := by rw [integral_sourceResponseDefect_eq_sub hK P hstat Q j n hscale k hk p q]

end EinsteinFull.Homogenization
