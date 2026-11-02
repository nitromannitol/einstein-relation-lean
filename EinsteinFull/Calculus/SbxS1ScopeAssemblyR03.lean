import EinsteinFull.Calculus.SbxS1AllScaleTrialR02
import EinsteinFull.Calculus.SbxS3LatticeRestartR02
import EinsteinFull.Calculus.SbxTakeoverFutureKernelReductionR01

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

/-- A bound proved for one actual reduced kernel transfers to every supplied
kernel, on the same conull set as its lattice stopping-time restart. -/
theorem s1_supplied_tube_and_lattice_restart_of_witness
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (μ : ℝ) (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (P P' : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q μ h0 h1 P)
    (hP' : IsGMPReducedKernel hd Q.ellipticity_parameter Q μ h0 h1 P')
    (A : Vec d → Set (Path d)) (ε : ℝ≥0∞)
    (hbound : ∀ᵐ ω ∂Q.measure, ∀ x, ε ≤ P' (x, ω) (A x)) :
    ∀ᵐ ω ∂Q.measure,
      (∀ x, ε ≤ P (x, ω) (A x)) ∧
      ∀ (x : Vec d) (Δ : ℝ≥0) (_hΔ : 0 < Δ)
        (τ : Path d → WithTop ℝ≥0)
        (hτ : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) τ),
        (∀ γ, τ γ = ⊤ ∨ ∃ n : ℕ, τ γ = (((n : ℝ≥0) * Δ : ℝ≥0) : WithTop ℝ≥0)) →
        ∀ (F : Path d → ℝ), StronglyMeasurable F → ∀ C : ℝ, (∀ γ, ‖F γ‖ ≤ C) →
        ∀ᵐ γ ∂P (x, ω), τ γ ≠ ⊤ →
          ((P (x, ω))[fun η => F (MarkovProcess.ContinuousPath.shift (WithTop.untopD 0 (τ η)) η) |
            hτ.measurableSpace]) γ =
          ∫ η, F η ∂P (γ (WithTop.untopD 0 (τ γ)), ω) := by
  filter_upwards [s1_transfer_uniform_quenched_path_lower_bound hd Q μ h0 h1 P P' hP hP' A ε hbound,
    EinsteinFull.s3_supplied_reduced_lattice_condExp_restart hd Q μ h0 h1 P hP] with ω ht hr
  exact ⟨ht, hr⟩

/-- Conditional scope assembly from the two separate analytic producers.
The tube producer may use one actual reduced kernel per law and signed force;
the positive auxiliary force is its absolute value. The future-kernel and
finite-history endpoint inputs are supplied by their proved reductions. -/
theorem s1_scope_of_minorization_and_one_kernel_tube
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (hminor : SbxS1CouplingAssemblyR02.UniformSourceMinorization)
    (hTube : ∀ {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
          (h0 : 0 < |lam|) (h1 : |lam| ≤ 1),
          ∃ P : QuenchedPathLaws d,
            IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam| h0.le h1 P ∧
            ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
              ENNReal.ofReal ε ≤ P (x, ω)
                {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta |lam|),
                  euclideanNorm (γ s - x) ≤ (l / |lam|) / 2}) :
    node_app_u3A_factorization_u23_coupling_u2D_scopeStmt := by
  apply s1_scope_of_uniform_quenched_tube_and_future_kernel
    node_app_u3A_factorization_u23_future_u2D_kernel_of_deps htails hminor
  intro d hd Λ₀ r₀ l hl
  obtain ⟨ε, hε, hε1, hbound⟩ := hTube hd Λ₀ r₀ l hl
  refine ⟨ε, hε, hε1, ?_⟩
  intro Q lam h0 h1 P hP
  have habs : |lam| = lam := abs_of_pos h0
  obtain ⟨P', hP', htube⟩ := hbound Q lam (by simpa only [habs] using h0)
    (by simpa only [habs] using h1)
  have hP'' : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0.le h1 P' := by
    simpa only [habs] using hP'
  have htube' : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      ENNReal.ofReal ε ≤ P' (x, ω)
        {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
          euclideanNorm (γ s - x) ≤ (l / lam) / 2} := by
    simpa only [habs] using htube
  filter_upwards [s1_supplied_tube_and_lattice_restart_of_witness hd Q lam h0.le h1 P P'
    hP hP'' (fun x => {γ | ∀ s ∈ Set.Icc (0 : ℝ≥0) (Renewal.regenDelta lam),
      euclideanNorm (γ s - x) ≤ (l / lam) / 2}) (ENNReal.ofReal ε) htube'] with ω hω
  exact hω.1

end EinsteinFull.Blueprint
