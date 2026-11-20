import EinsteinFull.Homogenization.SourceResponseLocality
import Mathlib.Probability.Independence.Basic

/-!
# Independence of separated responses

Under the finite-range law of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Chapter 1, responses on
separated triadic cubes are independent. The induction follows the argument for
finite families of separated local observations in
`EinsteinRelation.Environment.SeparatedIndependence`.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- Coefficient observations are monotone in their spatial support. -/
theorem coefficient_localSigma_mono {d : ℕ} {K : ℝ} {U V : Set (Vec d)} (hUV : U ⊆ V) :
    (localSigma U : MeasurableSpace (Coefficient d K)) ≤ localSigma V := by
  unfold localSigma
  refine iSup_le fun u => iSup_le fun i => iSup_le fun j => ?_
  exact le_iSup_of_le ⟨u.1, u.2.trans hUV⟩ (le_iSup_of_le i (le_iSup_of_le j le_rfl))

/-- Local coefficient sigma algebras over separated sets are jointly independent. -/
theorem iIndep_coefficient_localSigma_of_separated {ι : Type*} [Fintype ι] {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (s : ℝ) (hs : 1 < s) (U : ι → Set (Vec d)) (hU : ∀ i, MeasurableSet (U i))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j,
      s ≤ EinsteinRelation.euclideanNorm (x - y)) :
    ProbabilityTheory.iIndep (fun i => localSigma (U i)) P := by
  classical
  rw [ProbabilityTheory.iIndep_iff]
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro f _
    simp
  | insert a S ha ih =>
    intro f hf
    have hS : ∀ i ∈ S, MeasurableSet[localSigma (U i)] (f i) :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hWmeas : MeasurableSet (⋃ j ∈ S, U j) :=
      Finset.measurableSet_biUnion S fun j _ => hU j
    have hgap : ∃ t : ℝ, 1 < t ∧ ∀ x ∈ U a, ∀ y ∈ (⋃ j ∈ S, U j),
        t ≤ EinsteinRelation.euclideanNorm (x - y) := by
      refine ⟨s, hs, fun x hx y hy => ?_⟩
      obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
      have hne : a ≠ j := by
        rintro rfl
        exact ha hj
      exact hsep a j hne x hx y hyj
    have hind := hP (U a) (⋃ j ∈ S, U j) (hU a) hWmeas hgap
    have hG : MeasurableSet[localSigma (⋃ j ∈ S, U j)] (⋂ i ∈ S, f i) :=
      Finset.measurableSet_biInter S fun i hi =>
        coefficient_localSigma_mono (fun y hy => Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩) _ (hS i hi)
    rw [Finset.set_biInter_insert, Finset.prod_insert ha, ← ih (f := f) hS]
    exact (ProbabilityTheory.Indep_iff _ _ P).mp hind (f a) (⋂ i ∈ S, f i)
      (hf a (Finset.mem_insert_self a S)) hG

/-- Responses on a finite family of mutually separated triadic cubes are
jointly independent. -/
theorem iIndepFun_sourceResponseJ_of_separated {ι : Type*} [Fintype ι]
    {d : ℕ} [NeZero d] {K : ℝ} (P : Measure (Coefficient d K))
    [IsProbabilityMeasure P] (hP : AKMFiniteRange P) (s : ℝ) (hs : 1 < s)
    (Q : ι → TriadicCube d)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ cubeSet (Q i), ∀ y ∈ cubeSet (Q j),
      s ≤ EinsteinRelation.euclideanNorm (x - y))
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : ι → Vec d) :
    ProbabilityTheory.iIndepFun (fun i a => Book.Ch02.responseJ (Book.Ch02.cubeDomain (Q i))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk) (p i) (q i)) P := by
  let X := fun i a => Book.Ch02.responseJ (Book.Ch02.cubeDomain (Q i))
    (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk) (p i) (q i)
  have hI := iIndep_coefficient_localSigma_of_separated P hP s hs
    (fun i => cubeSet (Q i)) (fun i => measurableSet_cubeSet (Q i)) hsep
  refine (ProbabilityTheory.iIndepFun_iff_iIndep (fun _ : ι => Real.measurableSpace) X P).mpr ?_
  rw [ProbabilityTheory.iIndep_iff]
  intro S f hf
  have hH : ∀ i ∈ S, MeasurableSet[localSigma (cubeSet (Q i))] (f i) := fun i hi =>
    (measurable_iff_comap_le.mp (measurable_sourceResponseJ_cube (Q i) k hk (p i) (q i))) _
      (hf i hi)
  exact (ProbabilityTheory.iIndep_iff _ P).mp hI S hH

end EinsteinFull.Homogenization
