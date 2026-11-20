import EinsteinFull.Homogenization.SeparatedChildCubes

/-!
# Contraction on triadic children

Averages of response optimizer gradients over triadic children satisfy the
finite-range contraction step of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Lemma 2.13.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- At child scales at least three, averaging all child optimizer gradients
contracts their coordinate variance by a dimension-dependent factor. -/
theorem variance_average_childResponseGradient_le
    {d : ℕ} [NeZero d] {K : ℝ} (P : Measure (Coefficient d K))
    [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (n k : ℕ) (hscale : Q.scale = (n : ℤ) + 2)
    (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (coord : Fin d) :
    let X := fun R : {R // R ∈ descendantsAtDepth Q 1} => fun a =>
      Book.Ch02.averageGradient (Book.Ch02.cubeDomain R.1)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R.1) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain R.1)
            (sourceCoeffOn a (Book.Ch02.cubeDomain R.1) k hk)) p q).toSolution coord
    ProbabilityTheory.variance (((3 ^ d : ℕ) : ℝ)⁻¹ • (∑ R, X R)) P ≤
      (1 - (((3 ^ d : ℕ) : ℝ)⁻¹) ^ 2) *
      ProbabilityTheory.variance (fun a => Book.Ch02.averageGradient
        (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk)
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory
            (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
            (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk))
          p q).toSolution coord) P := by
  classical
  intro X
  obtain ⟨R, hR, S, hS, hsep⟩ := exists_separated_childCubes Q n hscale
  let r : {R // R ∈ descendantsAtDepth Q 1} := ⟨R, hR⟩
  let s : {R // R ∈ descendantsAtDepth Q 1} := ⟨S, hS⟩
  have hchild (R : {R // R ∈ descendantsAtDepth Q 1}) :
      R.1.scale = ((n + 1 : ℕ) : ℤ) := by
    have h := scale_eq_sub_of_mem_descendantsAtDepth R.2
    rw [hscale] at h
    push_cast
    omega
  have h := variance_average_sourceResponseGradient_le_of_separated_pair P hP hstat
    (fun R : {R // R ∈ descendantsAtDepth Q 1} => R.1) (n + 1) k hchild hk p q coord
    r s 2 (by norm_num) hsep
  have hvar := variance_sourceResponseAverageGradient_eq_origin P hstat R (n + 1) k
    (hchild r) hk p q coord
  change ProbabilityTheory.variance (X r) P = _ at hvar
  dsimp only at h
  rw [hvar] at h
  simpa only [Fintype.card_coe, descendantsAtDepth_card, pow_one] using h

end EinsteinFull.Homogenization
