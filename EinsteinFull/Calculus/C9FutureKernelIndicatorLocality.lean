import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinRelation.Diffusion.StoppedPathLocality
import EinsteinRelation.Regeneration.NoBacktrackingPrefix

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

open EinsteinRelation.Diffusion EinsteinRelation.Regeneration

/-- On the surviving event, stopping at the larger half-space changes no path point. -/
theorem future_locality_stoppedPath_eq_of_noBacktracking {d : ℕ} (R : ℝ)
    (hR : 0 < R) (i : Fin d) (γ : Path d) (hγ : NoBacktracking R γ i) :
    localityStoppedPath {x : Vec d | γ 0 i - 2 * R < x i} γ = γ := by
  have hU : IsOpen {x : Vec d | γ 0 i - 2 * R < x i} :=
    isOpen_lt continuous_const (continuous_apply i)
  have hstay : ∀ t : ℝ≥0, γ 0 i - 2 * R < γ t i := by
    intro t
    have ht := (noBacktracking_iff_forall R γ i).mp hγ t
    linarith
  apply ContinuousMap.ext
  intro t
  exact localityStoppedPath_eq_of_le_exit _ γ t
    (lt_localityExitTime_of_stays _ hU γ t (fun s _ => hstay s)).le

/-- The killed event itself is determined by the larger-half-space stopped path. -/
theorem future_locality_noBacktracking_stopped_iff {d : ℕ} (R : ℝ)
    (hR : 0 < R) (i : Fin d) (γ : Path d) :
    NoBacktracking R (localityStoppedPath {x : Vec d | γ 0 i - 2 * R < x i} γ) i ↔
      NoBacktracking R γ i := by
  let U : Set (Vec d) := {x | γ 0 i - 2 * R < x i}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_apply i)
  constructor
  · intro h
    have hinfinite : localityExitTime U γ = ⊤ := by
      by_contra hfinite
      have hout := localityExitTime_mem_compl U hU γ hfinite
      have ht := (noBacktracking_iff_forall R (localityStoppedPath U γ) i).mp h
        (localityExitTime U γ).toNNReal
      rw [localityStoppedPath_eq_of_le_exit U γ _
        (le_of_eq (ENNReal.coe_toNNReal hfinite)),
        localityStoppedPath_eq_of_le_exit U γ 0 (by simp)] at ht
      change ¬ γ 0 i - 2 * R < γ (localityExitTime U γ).toNNReal i at hout
      linarith
    change NoBacktracking R (localityStoppedPath U γ) i at h
    rwa [show localityStoppedPath U γ = γ from ite_eq_left hinfinite] at h
  · intro h
    rw [future_locality_stoppedPath_eq_of_noBacktracking R hR i γ h]
    exact h

/-- Killing removes precisely the paths whose full record is not recoverable from
the larger-half-space stopped path. The Bernoulli sequence and both fields remain literal. -/
theorem future_locality_killedFutureTest_stopped {d : ℕ} (R : ℝ) (hR : 0 < R)
    (i : Fin d) (Φ : FutureState d i R → ℝ)
    (xω : Vec d × FieldPair d) (z : CoupledSample d) :
    killedFutureTest R i Φ (xω,
      (localityStoppedPath {x : Vec d | z.1 0 i - 2 * R < x i} z.1, z.2)) =
      killedFutureTest R i Φ (xω, z) := by
  classical
  by_cases h : NoBacktracking R z.1 i
  · rw [future_locality_stoppedPath_eq_of_noBacktracking R hR i z.1 h]
  · have hs := (future_locality_noBacktracking_stopped_iff R hR i z.1).not.mpr h
    simp only [killedFutureTest, hs, h, ↓reduceIte]

/-- The actual coupling starts at the origin on the origin fibres specified in
its path-marginal clause. No product-a.e. clause is substituted for this one. -/
theorem future_locality_ae_starts_at_origin_of_coupling {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ z ∂K (0, ω), z.1 0 = 0 := by
  filter_upwards [hK.2.1.1, hK.2.2.1] with ω hm hp
  obtain ⟨_, r, hr⟩ := hp
  have hs := r.pathLaw_starts_at 0
  rw [← hr 0, ← hm] at hs
  exact ae_of_ae_map measurable_fst.aemeasurable hs

/-- The literal quenched killed-future integral uses only the fixed-half-space
stopped sample. This is an identity for the given coupling, without a locality premise. -/
theorem future_locality_integral_stopped_of_coupling {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K)
    (R : ℝ) (hR : 0 < R) (i : Fin d) (Φ : FutureState d i R → ℝ) :
    (fun ω => ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω)) =ᵐ[Q.measure]
      fun ω => ∫ z, killedFutureTest R i Φ ((0, ω),
        (localityStoppedPath {x : Vec d | -2 * R < x i} z.1, z.2)) ∂K (0, ω) := by
  filter_upwards [future_locality_ae_starts_at_origin_of_coupling hd Q lam l δ h₀ h₁ P K hK]
    with ω hω
  apply integral_congr_ae
  filter_upwards [hω] with z hz
  simpa only [hz, Pi.zero_apply, zero_sub, neg_mul] using
    (future_locality_killedFutureTest_stopped R hR i Φ (0, ω) z).symm

/- SUPERVISOR EXACT TARGET; comment only, no proof claim.
theorem future_kernel_indicator_local_version_of_coupling :
∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    ∀ S : Set (Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam)),
      MeasurableSet S →
      ∃ B : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d |
          -2 * (l / lam) ≤ x (Regeneration.Renewal.forceCoord hd)}] B ∧
        (fun ω => ∫ z, Regeneration.killedFutureTest (l / lam)
          (Regeneration.Renewal.forceCoord hd) (S.indicator (fun _ => (1 : ℝ))) ((0, ω), z) ∂K (0, ω)) =ᵐ[Q.measure] B
-/
end EinsteinFull.Blueprint
