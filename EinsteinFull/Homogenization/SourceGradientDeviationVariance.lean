import EinsteinFull.Homogenization.SourceGradientBlockStationarity
import EinsteinFull.Homogenization.SourceGradientVectorVariance

/-!
# Optimizer gradient deviations and variance

The mean-square deviation of a vector from a deterministic loading is bounded
by its variance and the deviation of its mean, as used in Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Section 2.2.
-/

open MeasureTheory
open _root_.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

namespace EinsteinFull.Homogenization

/-- For a square-integrable finite vector, the expected squared deviation
from a deterministic vector is bounded by twice its variance plus twice the
squared deviation of its mean. -/
theorem integrable_and_integral_vecNormSq_sub_le_variance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (F : Ω → Vec d) (hF : ∀ i, MemLp (fun a => F a i) 2 P) (b : Vec d) :
    (∀ i, Integrable (fun a => F a i) P) ∧
    Integrable (fun a => vecNormSq (F a - b)) P ∧
    (∫ a, vecNormSq (F a - b) ∂P) ≤
      2 * (∑ i : Fin d, ProbabilityTheory.variance (fun a => F a i) P) +
      2 * vecNormSq ((fun i => ∫ a, F a i ∂P) - b) := by
  classical
  let m : Vec d := fun i => ∫ a, F a i ∂P
  have hmean := integrable_and_integral_vecNormSq_sub_mean_eq_sum_variance P F hF
  change (∀ i, Integrable (fun a => F a i) P) ∧
    Integrable (fun a => vecNormSq (F a - m)) P ∧
    (∫ a, vecNormSq (F a - m) ∂P) = _ at hmean
  have hsub : Integrable (fun a => vecNormSq (F a - b)) P := by
    have hi (i : Fin d) : Integrable (fun a => (F a i - b i) ^ 2) P :=
      ((hF i).sub (memLp_const (b i))).integrable_sq
    have hs := integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ => hi i)
    simpa only [vecNormSq, vecDot, Pi.sub_apply, sq] using hs
  refine ⟨hmean.1, hsub, ?_⟩
  have hpoint (a : Ω) : vecNormSq (F a - b) ≤
      2 * vecNormSq (F a - m) + 2 * vecNormSq (m - b) := by
    have h := vecNormSq_add_le (F a - m) (m - b)
    simpa only [sub_add_sub_cancel, mul_add] using h
  calc
    _ ≤ ∫ a, 2 * vecNormSq (F a - m) + 2 * vecNormSq (m - b) ∂P :=
      integral_mono hsub ((hmean.2.1.const_mul 2).add (integrable_const _)) hpoint
    _ = 2 * (∫ a, vecNormSq (F a - m) ∂P) + 2 * vecNormSq (m - b) := by
      rw [integral_add (hmean.2.1.const_mul 2) (integrable_const _), integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul]
    _ = _ := by rw [hmean.2.2]

/-- Parent-block deviations are controlled by the response gap, descendant
variance and the mismatch between the descendant mean and the target slope. -/
theorem integrable_and_integral_sourceGradientBlockDeviation_le_variance
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q b : Vec d) :
    let G := fun a => descendantsAverage Q j (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
        (regularCoefficient a).toFun - b))
    let X := fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)) p q).toSolution
    let J := fun R a => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
      (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q
    Integrable G P ∧ (∀ i, Integrable (fun a => X a i) P) ∧
    Integrable (J (originCube d (n : ℤ))) P ∧ Integrable (J Q) P ∧
    (∫ a, G a ∂P) ≤
      (8 * d) * ((∫ a, J (originCube d (n : ℤ)) a ∂P) - ∫ a, J Q a ∂P) +
      4 * (∑ i : Fin d, ProbabilityTheory.variance (fun a => X a i) P) +
      4 * vecNormSq ((fun i => ∫ a, X a i ∂P) - b) := by
  intro G X J
  have hblock := integrable_and_integral_sourceGradientBlockDeviation_le
    hK P hstat Q j n hscale k hk p q b
  change Integrable G P ∧ _ at hblock
  have hdesc := integrable_and_integral_descendantsGradientDeviation_eq_origin
    P hstat Q j n hscale k hk p q b
  have hX (i : Fin d) : MemLp (fun a => X a i) 2 P :=
    memLp_sourceResponseAverageGradient_cube P (originCube d (n : ℤ)) k hk p q i 2
  have hvar := integrable_and_integral_vecNormSq_sub_le_variance P X hX b
  refine ⟨hblock.1, hvar.1, integrable_sourceResponseJ_cube hK P _ k hk p q,
    integrable_sourceResponseJ_cube hK P _ k hk p q, ?_⟩
  have hblock' := hblock.2.2
  change (∫ a, G a ∂P) ≤ (8 * d) *
    ((∫ a, J (originCube d (n : ℤ)) a ∂P) - ∫ a, J Q a ∂P) +
    2 * (∫ a, descendantsAverage Q j (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
        (regularCoefficient a).toFun - b)) ∂P) at hblock'
  rw [hdesc.2.2] at hblock'
  linarith [hblock', hvar.2.2]

end EinsteinFull.Homogenization
