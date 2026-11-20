import EinsteinFull.Homogenization.SourceResponseDefect
import Homogenization.Book.Ch04.Theorems.CanonicalSolutions.Measurability
import Homogenization.Probability.RegCoeffField.EllipticSupport

/-!
# Measurability of response optimizer averages

The local optimizer-gradient averages used in Lemma 2.13 of Armstrong, Kuusi
and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, are measurable for the source coefficient law.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The source coefficient law pushes forward to a Chapter 4 law carrier. -/
theorem regularCoefficient_lawCarrier {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] :
    Book.Ch04.RestrictionLawCarrier (Measure.map regularCoefficient P) := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  let P' := Measure.map regularCoefficient P
  apply Book.Ch04.lawCarrier_of_aeLocallyUniformlyElliptic
  have hs : ∀ᵐ a ∂P', ∀ Q : TriadicCube d,
      IsAEEllipticFieldOn 1 ((k : ℝ) + 1) (openCubeSet Q) a.toFun := by
    apply (ae_map_iff measurable_regularCoefficient.aemeasurable
      (measurableSet_forall_openCubeSet_isAEEllipticFieldOn 1 ((k : ℝ) + 1))).2
    filter_upwards [] with a Q
    have h := Book.Ch05.Section53.JUpperBoundWeakNorms.ch02_coeffOn_isAEEllipticFieldOn
      (unitLowerSourceCoeffOn a (Book.Ch02.cubeDomain Q) k hK)
    simpa [unitLowerSourceCoeffOn, Book.Ch02.cubeDomain_coe] using h
  filter_upwards [hs] with a ha Q
  exact ⟨1, (k : ℝ) + 1, zero_lt_one, by linarith [Nat.cast_nonneg (α := ℝ) k], ha Q⟩

/-- Each canonical response optimizer gradient average is almost everywhere
measurable under a source coefficient probability law. -/
theorem aemeasurable_sourceResponseGradientAverage {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (Q R : TriadicCube d) (p q : Vec d) :
    AEMeasurable (fun a => Book.Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q
      (regularCoefficient a).toFun) P := by
  have h := Book.Ch04.RestrictionLawCarrier.aemeasurable_canonicalScalarResponseGradientAverage_cubeSet
    (regularCoefficient_lawCarrier P) Q R p q
  exact h.comp_measurable measurable_regularCoefficient

end EinsteinFull.Homogenization
