import EinsteinFull.Regeneration.PhysicalVelocityFromCycles
import EinsteinFull.Regeneration.LaterMaximumMeasurability

/-!
# Velocity from joint regeneration cycle laws

The source regeneration factorization supplies one joint law for each cycle.
Its measurable projections give the cycle observables needed by the velocity
and physical-clock strong laws.
-/

open MeasureTheory Filter ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology ProbabilityTheory Function

namespace EinsteinFull.Regeneration

/-- Duration, displacement, maximal displacement and physical-clock increment
of one later regeneration cycle. -/
noncomputable def laterCycleState {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (n : ℕ)
    (q : FieldPair d × CoupledSample d) : ℝ × (Fin d → ℝ) × (Fin d → ℝ) × ℝ :=
  (laterDuration Δ lam R i n q,
    fun j => laterCoordinateReward Δ lam R i j n q,
    fun j => laterCoordinateMaximum Δ lam R i j n q,
    laterProfileReward Δ lam R i physicalClockProfile n q)

/-- The joint cycle state is measurable. -/
theorem measurable_laterCycleState {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (n : ℕ) :
    Measurable (laterCycleState Δ lam R i n) := by
  have hr : Measurable (fun q : FieldPair d × CoupledSample d =>
      fun j => laterCoordinateReward Δ lam R i j n q) :=
    Measurable.of_eval (fun j => measurable_laterCoordinateReward Δ lam R i j n)
  have hm : Measurable (fun q : FieldPair d × CoupledSample d =>
      fun j => laterCoordinateMaximum Δ lam R i j n q) :=
    Measurable.of_eval (fun j => measurable_laterCoordinateMaximum Δ lam R i j n)
  exact (measurable_laterDuration Δ lam R i n).prodMk
    (hr.prodMk (hm.prodMk (measurable_later_physicalClockReward Δ lam R i n)))

/-- Joint later-cycle independence and identical distributions imply the physical
velocity when the actual cycle moments, finiteness, and clock-law identity hold. -/
theorem physical_quenched_velocity_of_joint_cycle_laws {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (PX : Kernel (FieldPair d) (Path d))
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K) (hpath : HasPathMarginals Q K P)
    (L : ℝ) (hreg : ∀ᵐ ω ∂Q, IsRegular L ω)
    (hTC : ∀ᵐ ω ∂Q, ∀ hω : IsRegular L ω,
      PX ω = Measure.map (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ L hω) (P (0, ω)))
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i R K)
    (hfinite : ∀ᵐ q ∂annealedCoupledLaw Q K, ∀ n, regenerationTime Δ lam R q.2 i n ≠ ⊤)
    (ht : Integrable (laterDuration Δ lam R i 0) (annealedCoupledLaw Q K))
    (hm : ∀ j, Integrable (laterCoordinateMaximum Δ lam R i j 0) (annealedCoupledLaw Q K))
    (hind : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterCycleState Δ lam R i))
    (hident : ∀ n, IdentDistrib (laterCycleState Δ lam R i n) (laterCycleState Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K)) :
    ∃ v : Vec d, HasQuenchedVelocity Q PX v ∧ 0 < v i := by
  have hit : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterDuration Δ lam R i) := by
    intro m n hmn
    simpa only [Function.comp_def, laterCycleState] using (hind hmn).comp measurable_fst measurable_fst
  have hdt : ∀ n, IdentDistrib (laterDuration Δ lam R i n) (laterDuration Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K) := by
    intro n
    simpa only [Function.comp_def, laterCycleState] using (hident n).comp measurable_fst
  have hir : ∀ j, Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterCoordinateReward Δ lam R i j) := by
    intro j m n hmn
    have hm : Measurable (fun p : ℝ × (Fin d → ℝ) × (Fin d → ℝ) × ℝ => p.2.1 j) :=
      (measurable_pi_apply j).comp measurable_snd.fst
    simpa only [Function.comp_def, laterCycleState] using (hind hmn).comp hm hm
  have hdr : ∀ j n, IdentDistrib (laterCoordinateReward Δ lam R i j n) (laterCoordinateReward Δ lam R i j 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K) := by
    intro j n
    have hm : Measurable (fun p : ℝ × (Fin d → ℝ) × (Fin d → ℝ) × ℝ => p.2.1 j) :=
      (measurable_pi_apply j).comp measurable_snd.fst
    simpa only [Function.comp_def, laterCycleState] using (hident n).comp hm
  have him : ∀ j, Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterCoordinateMaximum Δ lam R i j) := by
    intro j m n hmn
    have hm : Measurable (fun p : ℝ × (Fin d → ℝ) × (Fin d → ℝ) × ℝ => p.2.2.1 j) :=
      (measurable_pi_apply j).comp measurable_snd.snd.fst
    simpa only [Function.comp_def, laterCycleState] using (hind hmn).comp hm hm
  have hdm : ∀ j n, IdentDistrib (laterCoordinateMaximum Δ lam R i j n) (laterCoordinateMaximum Δ lam R i j 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K) := by
    intro j n
    have hm : Measurable (fun p : ℝ × (Fin d → ℝ) × (Fin d → ℝ) × ℝ => p.2.2.1 j) :=
      (measurable_pi_apply j).comp measurable_snd.snd.fst
    simpa only [Function.comp_def, laterCycleState] using (hident n).comp hm
  have hic : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on
      laterProfileReward Δ lam R i physicalClockProfile) := by
    intro m n hmn
    have hm : Measurable (fun p : ℝ × (Fin d → ℝ) × (Fin d → ℝ) × ℝ => p.2.2.2) :=
      measurable_snd.snd.snd
    simpa only [Function.comp_def, laterCycleState] using (hind hmn).comp hm hm
  have hdc : ∀ n, IdentDistrib (laterProfileReward Δ lam R i physicalClockProfile n)
      (laterProfileReward Δ lam R i physicalClockProfile 0) (annealedCoupledLaw Q K) (annealedCoupledLaw Q K) := by
    intro n
    have hm : Measurable (fun p : ℝ × (Fin d → ℝ) × (Fin d → ℝ) × ℝ => p.2.2.2) :=
      measurable_snd.snd.snd
    simpa only [Function.comp_def, laterCycleState] using (hident n).comp hm
  exact physical_quenched_velocity_of_cycle_laws Q P PX K hK hpath L hreg hTC Δ hΔ lam R
    hlam hR i hsupport hfinite ht hit hdt hir hdr hm him hdm hic hdc

end EinsteinFull.Regeneration
