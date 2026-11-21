import EinsteinFull.Regeneration.LaterCoordinateVelocity
import EinsteinFull.Regeneration.PhysicalClockRate
import EinsteinFull.Regeneration.PhysicalClockCycleBounds

/-!
# Physical velocity from regeneration cycle laws

The regeneration and physical-clock strong laws combine to give the physical quenched
velocity. Finiteness, cycle laws, moments and the identification of the physical law with
the inverse-clock image are retained as explicit hypotheses.
-/

open MeasureTheory Filter ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology ProbabilityTheory Function

namespace EinsteinFull.Regeneration

/-- Literal regeneration cycle laws and the physical inverse-clock identification imply a
physical quenched velocity with positive force component. -/
theorem physical_quenched_velocity_of_cycle_laws {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (PX : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K) (hpath : HasPathMarginals Q K P)
    (L : ℝ) (hreg : ∀ᵐ ω ∂Q, IsRegular L ω)
    (hTC : ∀ᵐ ω ∂Q, ∀ hω : IsRegular L ω,
      PX ω = Measure.map (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ L hω) (P (0, ω)))
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i R K)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤)
    (ht : Integrable (laterDuration Δ lam R i 0) (annealedCoupledLaw Q K))
    (hit : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterDuration Δ lam R i))
    (hdt : ∀ n, IdentDistrib (laterDuration Δ lam R i n) (laterDuration Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hir : ∀ j, Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterCoordinateReward Δ lam R i j))
    (hdr : ∀ j n, IdentDistrib (laterCoordinateReward Δ lam R i j n) (laterCoordinateReward Δ lam R i j 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hm : ∀ j, Integrable (laterCoordinateMaximum Δ lam R i j 0) (annealedCoupledLaw Q K))
    (him : ∀ j, Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterCoordinateMaximum Δ lam R i j))
    (hdm : ∀ j n, IdentDistrib (laterCoordinateMaximum Δ lam R i j n) (laterCoordinateMaximum Δ lam R i j 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hic : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterProfileReward Δ lam R i physicalClockProfile))
    (hdc : ∀ n, IdentDistrib (laterProfileReward Δ lam R i physicalClockProfile n)
      (laterProfileReward Δ lam R i physicalClockProfile 0) (annealedCoupledLaw Q K) (annealedCoupledLaw Q K)) :
    ∃ v : Vec d, HasQuenchedVelocity Q PX v ∧ 0 < v i := by
  obtain ⟨v, hv, hvpos⟩ := quenched_velocity_of_later_cycle_laws Q P K hK hpath
    Δ hΔ lam R hlam hR i hsupport hfinite ht hit hdt hir hdr hm him hdm
  have hregJoint : ∀ᵐ ωz ∂annealedCoupledLaw Q K, IsRegular L ωz.1 :=
    Measure.ae_compProd_of_ae_fst (Probability.probabilityPart (originCoupledLaw K))
      (Sharpness.measurableSet_isRegular_fieldPair L) hreg
  have hV : ∀ᵐ ωz ∂annealedCoupledLaw Q K, ∀ x, |ωz.1.2 x| ≤ L :=
    hregJoint.mono fun _ h => h.2.1
  have hc := integrable_later_physicalClockReward Q K Δ lam R L i hfinite hV ht
  let η : ℝ := (∫ ωz, laterProfileReward Δ lam R i physicalClockProfile 0 ωz ∂annealedCoupledLaw Q K) /
    ∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K
  have ha := annealed_physical_clock_rate_of_cycle_laws Q K hK Δ hΔ lam R i hfinite
    ht hit hdt hc hic hdc
  have hclock : ∀ᵐ ω ∂Q, ∀ᵐ γ ∂originLaw P ω,
      Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 η) :=
    quenched_physical_clock_rate_of_annealed Q P K hK hpath η ha
  have hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω) := by
    filter_upwards [hK.1, hpath.1] with ω hω hmap
    rw [originLaw_apply, ← hmap]
    exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).2 hω
  have hη : 0 < η := physical_clock_rate_pos Q (originLaw P) L η hreg hprob hclock
  have hTC' : ∀ᵐ ω ∂Q, ∀ hω : IsRegular L ω,
      PX ω = Measure.map (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ L hω) (originLaw P ω) :=
    hTC
  exact ⟨η⁻¹ • v, quenched_velocity_of_inverse_clock Q PX (originLaw P) L hreg hTC' v η hη hv hclock,
    inverse_clock_velocity_component_pos v i η hη hvpos⟩

end EinsteinFull.Regeneration
