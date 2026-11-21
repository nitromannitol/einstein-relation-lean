import EinsteinFull.Regeneration.IdenticalMaximaVelocity
import EinsteinFull.Regeneration.RecordCycleIndependence
import EinsteinFull.Regeneration.RecordCycleObservables

/-!
# Velocity from the regeneration records

Suppose that the records at the regeneration times are carried into each other by a measurable
shift, that every record after the first has the law of the first record under the conditioned
law `ν`, and that under `ν` the duration and displacement of the first cycle are independent of
the next record. Then the later cycle durations and displacements are pairwise independent and
identically distributed, the later cycle maxima are identically distributed, and with
integrable first-cycle duration and maxima the coupled path has a deterministic velocity with
positive force component (GMP 2012, Theorem 5.6 and Proposition 5.9).
-/

open MeasureTheory Filter ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal ProbabilityTheory Function

namespace EinsteinFull.Regeneration

variable {d : ℕ}

/-- The duration and the coordinate displacements of the first cycle of a record. -/
noncomputable def recordCycle (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (y : FutureState d i R) :
    ℝ × (Fin d → ℝ) :=
  (recordDuration Δ lam R i y, fun j => recordDisplacement Δ lam R i j y)

/-- Identical distribution passes to almost surely equal random variables. -/
theorem identDistrib_congr_ae {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {μ : Measure α} {X X' Y Y' : α → γ} (h : IdentDistrib X Y μ μ) (hX : X' =ᵐ[μ] X)
    (hY : Y' =ᵐ[μ] Y) (hX' : AEMeasurable X' μ) (hY' : AEMeasurable Y' μ) :
    IdentDistrib X' Y' μ μ :=
  ((IdentDistrib.of_ae_eq hX' hX).trans h).trans (IdentDistrib.of_ae_eq hY' hY).symm

theorem measurable_recordCycle (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) :
    Measurable (recordCycle Δ lam R i) :=
  (measurable_recordDuration Δ lam R i).prodMk
    (measurable_pi_iff.mpr fun j => measurable_recordDisplacement Δ lam R i j)

/-- The regeneration-record structure gives a quenched velocity with positive force component. -/
theorem quenched_velocity_of_record_factorization
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (hpath : HasPathMarginals Q K P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i R K)
    (ν : Measure (FieldPair d × CoupledSample d)) [IsProbabilityMeasure ν]
    (hfinite : ∀ᵐ q ∂annealedCoupledLaw Q K, ∀ k, regenerationTime Δ lam R q.2 i k ≠ ⊤)
    (Θ : FutureState d i R → FutureState d i R) (hΘm : Measurable Θ)
    (hΘμ : ∀ k, ∀ᵐ q ∂annealedCoupledLaw Q K,
      Θ (iteratedRecord Δ lam R i k q) = iteratedRecord Δ lam R i (k + 1) q)
    (hΘν : ∀ k, ∀ᵐ q ∂ν, Θ (iteratedRecord Δ lam R i k q) = iteratedRecord Δ lam R i (k + 1) q)
    (hμ : ∀ k, 1 ≤ k → (annealedCoupledLaw Q K).map (iteratedRecord Δ lam R i k) =
      ν.map (iteratedRecord Δ lam R i 0))
    (hν : ∀ k, 1 ≤ k → ν.map (iteratedRecord Δ lam R i k) = ν.map (iteratedRecord Δ lam R i 0))
    (hfac : (fun q => recordCycle Δ lam R i (iteratedRecord Δ lam R i 0 q)) ⟂ᵢ[ν]
      iteratedRecord Δ lam R i 1)
    (hdur : Integrable (fun q => recordDuration Δ lam R i (iteratedRecord Δ lam R i 0 q)) ν)
    (hmax : ∀ j, Integrable (fun q => recordMaximum Δ lam R i j (iteratedRecord Δ lam R i 0 q)) ν) :
    ∃ v : Vec d, HasQuenchedVelocity Q (originLaw P) v ∧ 0 < v i := by
  set μ := annealedCoupledLaw Q K with hμdef
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  set Y := iteratedRecord Δ lam R i with hYdef
  have hY : ∀ k, Measurable (Y k) := fun k => measurable_iteratedRecord Δ lam R i k
  obtain ⟨hind, hid⟩ := indepFun_identDistrib_of_record_factorization μ ν Y hY Θ hΘm hΘμ hΘν
    hμ hν (recordCycle Δ lam R i) (measurable_recordCycle Δ lam R i) hfac
  -- identically distributed functions of the later records
  have hlaw : ∀ (f : FutureState d i R → ℝ), Measurable f → ∀ n,
      IdentDistrib (fun q => f (Y (n + 1) q)) (fun q => f (Y 0 q)) μ ν := by
    intro f hf n
    refine ⟨(hf.comp (hY _)).aemeasurable, (hf.comp (hY _)).aemeasurable, ?_⟩
    have h1 : (fun q => f (Y (n + 1) q)) = f ∘ Y (n + 1) := rfl
    have h2 : (fun q => f (Y 0 q)) = f ∘ Y 0 := rfl
    rw [h1, h2, ← Measure.map_map hf (hY _), ← Measure.map_map hf (hY _), hμ (n + 1) (by omega)]
  have hdurM : Measurable (recordDuration Δ lam R i) := measurable_recordDuration Δ lam R i
  have hdispM : ∀ j, Measurable (recordDisplacement Δ lam R i j) := fun j =>
    measurable_recordDisplacement Δ lam R i j
  have hmaxM : ∀ j, Measurable (recordMaximum Δ lam R i j) := fun j =>
    measurable_recordMaximum Δ lam R i j
  -- the later-cycle variables agree almost surely with record observables
  have hdt_ae : ∀ n, laterDuration Δ lam R i n =ᵐ[μ]
      fun q => recordDuration Δ lam R i (Y (n + 1) q) := fun n => by
    filter_upwards [hfinite] with q hq
    exact laterDuration_eq_recordDuration Δ lam R i n q hq
  have hdr_ae : ∀ j n, laterCoordinateReward Δ lam R i j n =ᵐ[μ]
      fun q => recordDisplacement Δ lam R i j (Y (n + 1) q) := fun j n => by
    filter_upwards [hfinite] with q hq
    exact laterCoordinateReward_eq_recordDisplacement Δ lam R i j n q hq
  have hdm_ae : ∀ j n, laterCoordinateMaximum Δ lam R i j n =ᵐ[μ]
      fun q => recordMaximum Δ lam R i j (Y (n + 1) q) := fun j n => by
    filter_upwards [hfinite] with q hq
    exact laterCoordinateMaximum_eq_recordMaximum Δ lam R i j n q hq
  -- pairwise independence of projections
  have hpair : ∀ (f : ℝ × (Fin d → ℝ) → ℝ), Measurable f → ∀ (X : ℕ → _ → ℝ),
      (∀ n, X n =ᵐ[μ] fun q => f (recordCycle Δ lam R i (Y (n + 1) q))) →
      Pairwise ((· ⟂ᵢ[μ] ·) on X) := by
    intro f hf X hX m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact ((hind m n h).comp hf hf).congr (hX m).symm (hX n).symm
    · exact (((hind n m h).comp hf hf).congr (hX n).symm (hX m).symm).symm
  have hfst : Measurable fun p : ℝ × (Fin d → ℝ) => p.1 := measurable_fst
  have hsnd : ∀ j, Measurable fun p : ℝ × (Fin d → ℝ) => p.2 j := fun j =>
    (measurable_pi_apply j).comp measurable_snd
  have hit := hpair (fun p => p.1) hfst (laterDuration Δ lam R i) hdt_ae
  have hir : ∀ j, Pairwise ((· ⟂ᵢ[μ] ·) on laterCoordinateReward Δ lam R i j) := fun j =>
    hpair (fun p => p.2 j) (hsnd j) (laterCoordinateReward Δ lam R i j) (hdr_ae j)
  have hdt : ∀ n, IdentDistrib (laterDuration Δ lam R i n) (laterDuration Δ lam R i 0) μ μ :=
    fun n => identDistrib_congr_ae ((hlaw _ hdurM n).trans (hlaw _ hdurM 0).symm) (hdt_ae n)
      (hdt_ae 0) (measurable_laterDuration Δ lam R i n).aemeasurable
      (measurable_laterDuration Δ lam R i 0).aemeasurable
  have hdr : ∀ j n, IdentDistrib (laterCoordinateReward Δ lam R i j n)
      (laterCoordinateReward Δ lam R i j 0) μ μ := fun j n =>
    identDistrib_congr_ae ((hlaw _ (hdispM j) n).trans (hlaw _ (hdispM j) 0).symm) (hdr_ae j n)
      (hdr_ae j 0) (measurable_laterCoordinateReward Δ lam R i j n).aemeasurable
      (measurable_laterCoordinateReward Δ lam R i j 0).aemeasurable
  have hdm : ∀ j n, IdentDistrib (laterCoordinateMaximum Δ lam R i j n)
      (laterCoordinateMaximum Δ lam R i j 0) μ μ := fun j n =>
    identDistrib_congr_ae ((hlaw _ (hmaxM j) n).trans (hlaw _ (hmaxM j) 0).symm) (hdm_ae j n)
      (hdm_ae j 0) (measurable_laterCoordinateMaximum Δ lam R i j n).aemeasurable
      (measurable_laterCoordinateMaximum Δ lam R i j 0).aemeasurable
  have ht : Integrable (laterDuration Δ lam R i 0) μ :=
    ((hlaw _ hdurM 0).integrable_iff.mpr hdur).congr (hdt_ae 0).symm
  have hm : ∀ j, Integrable (laterCoordinateMaximum Δ lam R i j 0) μ := fun j =>
    ((hlaw _ (hmaxM j) 0).integrable_iff.mpr (hmax j)).congr (hdm_ae j 0).symm
  exact quenched_velocity_of_later_cycle_laws_of_identDistrib_maxima Q P K hK hpath Δ hΔ lam R
    hlam hR i hsupport hfinite ht hit hdt hir hdr hm hdm

end EinsteinFull.Regeneration
