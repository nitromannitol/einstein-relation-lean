import EinsteinFull.Homogenization.SourceGradientBlockDeviation
import EinsteinFull.Homogenization.SourceGradientMeanStationarity

/-!
# Stationarity of squared optimizer-gradient deviations

Translation covariance reduces the descendant-optimizer term in the
multiscale argument of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Section 2.2, to an origin cube.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Squared deviations of a gradient coordinate have equal expectations on
cubes of the same nonnegative scale. -/
theorem integrable_and_integral_sq_sourceGradient_sub_eq_origin
    {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (n k : ℕ) (hscale : Q.scale = n)
    (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) (b : ℝ) :
    let F := fun R a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain R)
      (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain R)
          (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)) p q).toSolution i
    Integrable (fun a => (F Q a - b) ^ 2) P ∧
    (∫ a, (F Q a - b) ^ 2 ∂P) = ∫ a, (F (originCube d (n : ℤ)) a - b) ^ 2 ∂P := by
  intro F
  have hF (R : TriadicCube d) : MemLp (fun a => F R a - b) 2 P := by
    have h := (memLp_sourceResponseAverageGradient_cube P R k hk p q i 2).sub (memLp_const b)
    exact h
  refine ⟨(hF Q).integrable_sq, ?_⟩
  let z : LatticeIndex d := fun l => Q.index l * (3 : ℤ) ^ n
  have hmp : MeasurePreserving (translateCoefficient (latticeShift z)) P P :=
    ⟨measurable_translateCoefficient _, hstat z⟩
  have heq : F Q = fun a => F (originCube d (n : ℤ))
      (translateCoefficient (latticeShift z) a) := by
    funext a
    exact sourceResponseAverageGradient_cube_eq_origin a Q n k hscale hk p q i
  rw [heq]
  have hm := (measurable_sourceResponseAverageGradient_cube (K := K)
    (originCube d (n : ℤ)) k hk p q i).mono
      (coefficientLocalSigma_le_coefficientSigma _) le_rfl
  have hi := integral_map (f := fun a : Coefficient d K =>
      (F (originCube d (n : ℤ)) a - b) ^ 2) hmp.measurable.aemeasurable (by
    rw [hmp.map_eq]
    exact ((hm.sub (measurable_const : Measurable (fun _ : Coefficient d K => b))).pow_const 2).aestronglyMeasurable)
  rw [hmp.map_eq] at hi
  exact hi.symm

/-- The expected squared descendant-optimizer deviations equal those on a
single origin cube of the descendant scale. -/
theorem integrable_and_integral_descendantsGradientDeviation_eq_origin
    {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q b : Vec d) :
    let H := fun a => descendantsAverage Q j (fun R =>
      vecNormSq (Book.Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q
        (regularCoefficient a).toFun - b))
    let X := fun R a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain R)
      (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain R)
          (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk)) p q).toSolution
    Integrable H P ∧
    Integrable (fun a => vecNormSq (X (originCube d (n : ℤ)) a - b)) P ∧
    (∫ a, H a ∂P) = ∫ a, vecNormSq (X (originCube d (n : ℤ)) a - b) ∂P := by
  classical
  intro H X
  have hR (R : TriadicCube d) : Integrable (fun a => vecNormSq (X R a - b)) P := by
    have hi (i : Fin d) : Integrable (fun a => (X R a i - b i) ^ 2) P := by
      have h := (memLp_sourceResponseAverageGradient_cube P R k hk p q i 2).sub (memLp_const (b i))
      have h' : MemLp (fun a => X R a i - b i) 2 P := h
      exact h'.integrable_sq
    have hsum := integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ => hi i)
    simpa only [vecNormSq, vecDot, Pi.sub_apply, sq] using hsum
  have heq (R : TriadicCube d) (hRscale : R.scale = n) :
      (∫ a, vecNormSq (X R a - b) ∂P) =
        ∫ a, vecNormSq (X (originCube d (n : ℤ)) a - b) ∂P := by
    simp only [vecNormSq, vecDot, Pi.sub_apply, ← sq]
    rw [integral_finsetSum _ (fun i _ =>
      (integrable_and_integral_sq_sourceGradient_sub_eq_origin P hstat R n k hRscale hk p q i (b i)).1),
      integral_finsetSum _ (fun i _ =>
      (integrable_and_integral_sq_sourceGradient_sub_eq_origin P hstat
        (originCube d (n : ℤ)) n k rfl hk p q i (b i)).1)]
    exact Finset.sum_congr rfl (fun i _ =>
      (integrable_and_integral_sq_sourceGradient_sub_eq_origin P hstat R n k hRscale hk p q i (b i)).2)
  have hH : Integrable H P := by
    dsimp only [H, descendantsAverage]
    simp_rw [sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)]
    exact (integrable_finsetSum _ (fun R _ => hR R)).const_mul _
  refine ⟨hH, hR _, ?_⟩
  dsimp only [H]
  simp_rw [sourceCanonicalGradientAverage_self_eq (k := k) (hk := hk)]
  change (∫ a, descendantsAverage Q j (fun R => vecNormSq (X R a - b)) ∂P) = _
  unfold descendantsAverage
  rw [integral_const_mul, integral_finsetSum _ (fun R _ => hR R)]
  have hn : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j)
  have hmean (R : TriadicCube d) (hRmem : R ∈ descendantsAtDepth Q j) :
      (∫ a, vecNormSq (X R a - b) ∂P) =
        ∫ a, vecNormSq (X (originCube d (n : ℤ)) a - b) ∂P := by
    apply heq R
    rw [scale_eq_sub_of_mem_descendantsAtDepth hRmem, hscale]
    simp
  rw [Finset.sum_congr rfl (fun R hRmem => hmean R hRmem), Finset.sum_const,
    nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end EinsteinFull.Homogenization
