import EinsteinFull.Calculus.C10S3StoppedTubeProducer
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3TubeProbability
import EinsteinFull.Calculus.C17TubeCoefficientMesh

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint

/-- Conditional tube adapter: only the selected realization, regeneration time,
    and half-radius endpoint estimate are requested. -/
theorem c4_uniform_tube_of_selected_killed_lower
    (lower : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l : ℝ), 0 < l → ∀ (P : QuenchedPathLaws d),
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P →
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂Q.measure,
        ∃ (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
          (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
            (one_le_sourceReducedBound Q.ellipticity_parameter)
            (zeroPotentialReducedPair ω) hω lam h0.le h1),
        (∀ x : Vec d, P (x, ω) = G.pathLaw x) ∧
        ∀ (x : Vec d) (A : Set (Vec d)), MeasurableSet A →
          A ⊆ {y | euclideanNorm (y - x) < ((l / lam) / 2) / 16} →
          ENNReal.ofReal c * volume A ≤
            gmpKilledEndpointKernel G (PDE.euclideanBall x ((l / lam) / 2))
              (PDE.isOpen_euclideanBall x ((l / lam) / 2))
              (Regeneration.Renewal.regenDelta lam) x A)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      ENNReal.ofReal ε ≤ P (x, ω)
        {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Regeneration.Renewal.regenDelta lam),
          euclideanNorm (γ s - x) ≤ (l / lam) / 2} := by
  have hr : 0 < (l / lam) / 2 := by positivity
  obtain ⟨c, hc, hdom⟩ := lower hd Q lam h0 h1 l hl P hK.2.2.1
  obtain ⟨ε, hε, hε1, hvol⟩ := c17_uniform_endpoint_volume_eta ((l / lam) / 2) c hr hc
  refine ⟨ε, hε, hε1, ?_⟩
  filter_upwards [hdom] with ω hdomω
  obtain ⟨hω, G, hG, hbound⟩ := hdomω
  intro x
  let A : Set (Vec d) := {y | euclideanNorm (y - x) < ((l / lam) / 2) / 16}
  have hball : PDE.euclideanBall x (((l / lam) / 2) / 16) = A := by
    ext y
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)
  have hA : MeasurableSet A := by
    rw [← hball]
    exact PDE.measurableSet_euclideanBall x _
  have hid : gmpKilledEndpointKernel G (PDE.euclideanBall x ((l / lam) / 2))
      (PDE.isOpen_euclideanBall x ((l / lam) / 2))
      (Regeneration.Renewal.regenDelta lam) x A =
      P (x, ω) {γ | (∀ s ∈ Set.Icc (0 : ℝ≥0) (Regeneration.Renewal.regenDelta lam),
        euclideanNorm (γ s - x) < (l / lam) / 2) ∧ γ (Regeneration.Renewal.regenDelta lam) ∈ A} := by
    rw [TubeProbability.killedEndpoint_apply_set G _ _ _ x A hA, hG x]
    congr 1
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, zero_le, true_and]
    rw [lt_localityExitTime_iff (PDE.euclideanBall x ((l / lam) / 2))
      (PDE.isOpen_euclideanBall x ((l / lam) / 2)) γ _]
    constructor
    · rintro ⟨hstays, hend⟩
      exact ⟨fun s hs => (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp (hstays s hs), hend⟩
    · rintro ⟨hstays, hend⟩
      exact ⟨fun s hs => (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mpr (hstays s hs), hend⟩
  have hbound' := hbound x A hA (Set.Subset.rfl)
  rw [hid] at hbound'
  exact (hvol x).trans (hbound'.trans
    (measure_mono (fun γ hγ s hs => (hγ.1 s hs).le)))

/-- The fixed-time selected-realization lower bound supplies c10's stopped tube. -/
theorem c4_stopped_tube_of_selected_killed_lower
    (lower : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l : ℝ), 0 < l → ∀ (P : QuenchedPathLaws d),
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P →
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂Q.measure,
        ∃ (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
          (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
            (one_le_sourceReducedBound Q.ellipticity_parameter)
            (zeroPotentialReducedPair ω) hω lam h0.le h1),
        (∀ x : Vec d, P (x, ω) = G.pathLaw x) ∧
        ∀ (x : Vec d) (A : Set (Vec d)), MeasurableSet A →
          A ⊆ {y | euclideanNorm (y - x) < ((l / lam) / 2) / 16} →
          ENNReal.ofReal c * volume A ≤
            gmpKilledEndpointKernel G (PDE.euclideanBall x ((l / lam) / 2))
              (PDE.isOpen_euclideanBall x ((l / lam) / 2))
              (Regeneration.Renewal.regenDelta lam) x A)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let μ := Regeneration.annealedCoupledLaw Q.measure K; let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; let Tube := {q : FieldPair d × Regeneration.CoupledSample d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ, euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 ((couplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) - (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 (couplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}; ε * μ.real E ≤ μ.real (E ∩ Tube) := by
  obtain ⟨ε, hε, hε1, hTube⟩ :=
    c4_uniform_tube_of_selected_killed_lower lower hd Q lam h0 h1 l δ hl P K hK
  exact ⟨ε, hε, hε1,
    c10_s3_stopped_tube_of_uniform_quenched_tube hd Q lam h0 h1 l δ
      hl hsep hδ0 hδ1 P K hK ε hε hTube⟩


end EinsteinFull.Blueprint
