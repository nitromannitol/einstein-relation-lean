import EinsteinFull.Homogenization.SourceResponseAnnealed
import Homogenization.Book.Ch02.Theorems.SubadditivityScaling

/-!
# Locality and subadditivity of the response

The response quantity in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Chapter 2, is locally measurable
and subadditive on triadic partitions.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The response on an open triadic cube is measurable with respect to
coefficient observations on the corresponding half-open cube. -/
theorem measurable_sourceResponseJ_cube {d : ℕ} [NeZero d] {K : ℝ}
    (Q : TriadicCube d) (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    @Measurable (Coefficient d K) ℝ (localSigma (cubeSet Q)) _
      (fun a => Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q) := by
  have hd : @Measurable (Coefficient d K) ℝ (localSigma (cubeSet Q)) _
      (fun a => sourceDirichletEnergy a (openCubeSet Q) (-p)) := by
    let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
      simpa [volumeMeasureOn] using
        (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
    have hm := measurable_regularCoefficient_Mu (K := K) Q (-p, 0)
    convert hm using 1
    funext a
    rw [sourceDirichletEnergy_eq_Mu_regularCoefficient a (isOpen_openCubeSet Q) (-p)]
    exact (Mu_cubeSet_eq_openCubeSet_of_triadicCube Q (-p, 0)
      (regularCoefficient a).toFun).symm
  have h := (hd.add (measurable_sourceDualEnergy_cube Q q)).sub
    (measurable_const (a := vecDot p q))
  convert h using 1
  funext a
  rw [responseJ_eq_sourceDirichlet_add_sourceDual]
  rfl

/-- The response is integrable on every triadic cube under a finite law. -/
theorem integrable_sourceResponseJ_cube {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P] (Q : TriadicCube d)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    Integrable (fun a => Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q) P := by
  have h := ((integrable_sourceDirichletEnergy_openCube hK P Q (-p)).add
    (integrable_sourceDualEnergy_cube P Q q)).sub (integrable_const (vecDot p q))
  convert h using 1
  funext a
  rw [responseJ_eq_sourceDirichlet_add_sourceDual]
  rfl

/-- The response is subadditive over a partition into admissible domains. -/
theorem sourceResponseJ_subadditive {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Book.Ch02.Domain d) (P : Book.Ch02.DomainPartition U)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    Book.Ch02.responseJ U (sourceCoeffOn a U k hk) p q ≤
      P.weightedAverage (fun i => Book.Ch02.responseJ (P.cell i)
        (sourceCoeffOn a (P.cell i) k hk) p q) := by
  have hrestr : ∀ i : P.Cell, Book.Ch02.CoeffOn.RestrictsTo
      (sourceCoeffOn a U k hk) (sourceCoeffOn a (P.cell i) k hk) := by
    intro i
    exact Filter.Eventually.of_forall fun _ => rfl
  exact (Book.Ch02.responseSubadditivityAndScalingTheory U
    (sourceCoeffOn a U k hk)).responseJ_subadditive P
      (fun i => sourceCoeffOn a (P.cell i) k hk) hrestr p q

/-- The response on a triadic cube is bounded by the average of its
responses on descendants at a fixed depth. -/
theorem sourceResponseJ_le_descendantsAverage {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (Q : TriadicCube d) (j k : ℕ)
    (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ≤
    descendantsAverage Q j (fun R => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
      (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q) := by
  have h := sourceResponseJ_subadditive a (Book.Ch02.cubeDomain Q)
    (Book.Ch02.descendantsDomainPartition Q j) k hk p q
  change Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
    (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ≤
    (Book.Ch02.descendantsDomainPartition Q j).weightedAverage (fun i =>
      Book.Ch02.responseJ (Book.Ch02.cubeDomain i.1)
        (sourceCoeffOn a (Book.Ch02.cubeDomain i.1) k hk) p q) at h
  rw [Book.Ch02.descendantsDomainPartition_weightedAverage Q j
    (fun R => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
      (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q)] at h
  exact h

end EinsteinFull.Homogenization
