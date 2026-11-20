import EinsteinFull.Homogenization.SourceOptimizerGradientMoments
import EinsteinFull.Homogenization.VarianceContraction

/-!
# Contraction of optimizer gradient fluctuations

Finite-range independence contracts the variance of averages of response
optimizer gradients in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Lemma 2.13.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- If two cubes in a same-scale family are separated beyond the finite-range
threshold, the variance of the average of their optimizer gradient coordinates
has a strict gain over the one-cube variance. -/
theorem variance_average_sourceResponseGradient_le_of_separated_pair
    {ι : Type*} [Fintype ι] {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : ι → TriadicCube d) (n k : ℕ) (hscale : ∀ i, (Q i).scale = n)
    (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (coord : Fin d)
    (i₀ j₀ : ι) (s : ℝ) (hs : 1 < s)
    (hsep : ∀ x ∈ cubeSet (Q i₀), ∀ y ∈ cubeSet (Q j₀),
      s ≤ EinsteinRelation.euclideanNorm (x - y)) :
    let X := fun i a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain (Q i))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (Q i))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk)) p q).toSolution coord
    ProbabilityTheory.variance ((Fintype.card ι : ℝ)⁻¹ • (∑ i, X i)) P ≤
      (1 - (Fintype.card ι : ℝ)⁻¹ ^ 2) * ProbabilityTheory.variance (X i₀) P := by
  classical
  intro X
  let R : Bool → TriadicCube d := fun b => if b then Q j₀ else Q i₀
  have hnorm (x y : Vec d) : EinsteinRelation.euclideanNorm (x - y) =
      EinsteinRelation.euclideanNorm (y - x) := by
    unfold EinsteinRelation.euclideanNorm EinsteinRelation.euclideanSq EinsteinRelation.dot
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  have hsep' : ∀ b c : Bool, b ≠ c → ∀ x ∈ cubeSet (R b), ∀ y ∈ cubeSet (R c),
      s ≤ EinsteinRelation.euclideanNorm (x - y) := by
    intro b c hbc x hx y hy
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact hsep x hx y hy
    · rw [hnorm]
      exact hsep y hy x hx
    · exact (hbc rfl).elim
  have hI := iIndepFun_sourceResponseAverageGradient_of_separated P hP s hs R hsep'
    k hk (fun _ => p) (fun _ => q) (fun _ => coord)
  have hpair : ProbabilityTheory.IndepFun (X i₀) (X j₀) P := by
    simpa [R, X] using hI.indepFun (show false ≠ true by decide)
  apply variance_average_le_of_independent_pair P X
  · intro i
    exact memLp_sourceResponseAverageGradient_cube P (Q i) k hk p q coord 2
  · intro i
    calc
      ProbabilityTheory.variance (X i) P = ProbabilityTheory.variance
          (fun a => Book.Ch02.averageGradient (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
            (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)
            (Book.Ch02.canonicalMaximizer
              (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
                (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk))
              p q).toSolution coord) P :=
        variance_sourceResponseAverageGradient_eq_origin P hstat (Q i) n k (hscale i) hk p q coord
      _ = ProbabilityTheory.variance (X i₀) P :=
        (variance_sourceResponseAverageGradient_eq_origin P hstat (Q i₀) n k
          (hscale i₀) hk p q coord).symm
  · exact hpair

end EinsteinFull.Homogenization
