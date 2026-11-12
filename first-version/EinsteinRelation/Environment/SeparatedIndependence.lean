import EinsteinRelation.Environment.Basic
import EinsteinRelation.Probability.LocalSigma
import Mathlib.Probability.Independence.Basic

/-! # Independence of separated local families

Observation sets at pairwise Euclidean distance at least `s > r₀` have jointly
independent local σ-algebras under a law of finite range `r₀`. The proof is a
finite induction: the next set is split off from the union of the previous ones,
and that union stays at distance at least `s` from it.
-/

open MeasureTheory

namespace EinsteinRelation

/-- The local σ-algebra of one piece of a finite union lies in that of the union. -/
theorem localSigma_le_biUnion {d : ℕ} {ι : Type*} {S : Finset ι} {U : ι → Set (Vec d)} {i : ι}
    (hi : i ∈ S) : localSigma (U i) ≤ localSigma (⋃ j ∈ S, U j) := by
  apply EinsteinRelation.Probability.localSigma_mono
  intro y hy
  exact Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩

/-- The local σ-algebras of the pieces of a finite union are contained in that of the union. -/
theorem iSup_localSigma_le_biUnion {d : ℕ} {ι : Type*} (S : Finset ι) (U : ι → Set (Vec d)) :
    (⨆ i ∈ S, localSigma (U i)) ≤ localSigma (⋃ j ∈ S, U j) :=
  iSup₂_le fun _ hi => localSigma_le_biUnion hi

/-- Finite families of observation sets with pairwise distance at least `s > r₀` are
jointly independent for their local σ-algebras. -/
theorem iIndep_localSigma_of_separated {ι : Type*} [Fintype ι] {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (r₀ s : ℝ)
    (hs : r₀ < s) (hQ : HasFiniteRange r₀ Q) (U : ι → Set (Vec d))
    (hU : ∀ i, MeasurableSet (U i))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, s ≤ euclideanNorm (x - y)) :
    ProbabilityTheory.iIndep (fun i => localSigma (U i)) Q := by
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
    have hgap : ∃ t : ℝ, r₀ < t ∧ ∀ x ∈ U a, ∀ y ∈ (⋃ j ∈ S, U j), t ≤ euclideanNorm (x - y) := by
      refine ⟨s, hs, fun x hx y hy => ?_⟩
      obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
      have hne : a ≠ j := by
        rintro rfl
        exact ha hj
      exact hsep a j hne x hx y hyj
    have hind : ProbabilityTheory.Indep (localSigma (U a)) (localSigma (⋃ j ∈ S, U j)) Q :=
      hQ (U a) (⋃ j ∈ S, U j) (hU a) hWmeas hgap
    have hG : MeasurableSet[localSigma (⋃ j ∈ S, U j)] (⋂ i ∈ S, f i) :=
      Finset.measurableSet_biInter S fun i hi => localSigma_le_biUnion hi _ (hS i hi)
    rw [Finset.set_biInter_insert, Finset.prod_insert ha, ← ih (f := f) hS]
    exact (ProbabilityTheory.Indep_iff _ _ Q).mp hind (f a) (⋂ i ∈ S, f i)
      (hf a (Finset.mem_insert_self a S)) hG

/-- Real random variables measurable for the local σ-algebras of separated observation sets
are jointly independent. -/
theorem iIndepFun_of_separated {ι : Type*} [Fintype ι] {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (r₀ s : ℝ)
    (hs : r₀ < s) (hQ : HasFiniteRange r₀ Q) (U : ι → Set (Vec d))
    (hU : ∀ i, MeasurableSet (U i))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, s ≤ euclideanNorm (x - y))
    (X : ι → FieldPair d → ℝ) (hX : ∀ i, Measurable[localSigma (U i)] (X i)) :
    ProbabilityTheory.iIndepFun X Q := by
  have hI := iIndep_localSigma_of_separated Q r₀ s hs hQ U hU hsep
  refine (ProbabilityTheory.iIndepFun_iff_iIndep (fun _ : ι => Real.measurableSpace) X Q).mpr ?_
  rw [ProbabilityTheory.iIndep_iff]
  intro S f hf
  have hH : ∀ i ∈ S, MeasurableSet[localSigma (U i)] (f i) := fun i hi =>
    (measurable_iff_comap_le.mp (hX i)) _ (hf i hi)
  exact (ProbabilityTheory.iIndep_iff _ Q).mp hI S hH

end EinsteinRelation
