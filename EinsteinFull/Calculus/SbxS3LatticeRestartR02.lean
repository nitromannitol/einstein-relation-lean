import EinsteinFull.Calculus.SbxS3SuppliedRestartR02
import MarkovProcess.Trajectory.StoppingLtTop
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

open EinsteinRelation EinsteinFull MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal

namespace EinsteinFull

/-- Restart at a finite lattice-valued stopping time of the canonical path filtration. -/
theorem s3_supplied_reduced_lattice_condExp_restart
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (Δ : ℝ≥0) (_hΔ : 0 < Δ)
      (τ : Path d → WithTop ℝ≥0)
      (hτ : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) τ),
      (∀ γ, τ γ = ⊤ ∨ ∃ n : ℕ, τ γ = (((n : ℝ≥0) * Δ : ℝ≥0) : WithTop ℝ≥0)) →
      ∀ (F : Path d → ℝ), StronglyMeasurable F → ∀ C : ℝ, (∀ γ, ‖F γ‖ ≤ C) →
      ∀ᵐ γ ∂P (x, ω), τ γ ≠ ⊤ →
        ((P (x, ω))[fun η => F (MarkovProcess.ContinuousPath.shift (WithTop.untopD 0 (τ η)) η) |
          hτ.measurableSpace]) γ =
        ∫ η, F η ∂P (γ (WithTop.untopD 0 (τ γ)), ω) := by
  filter_upwards [s3_supplied_reduced_countable_condExp_restart hd Q lam h0 h1 P hP, hP] with ω hω hreal
  obtain ⟨_, R, hR⟩ := hreal
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  intro x Δ hΔ τ hτ hgrid F hF C hC
  let μ := P (x, ω)
  have : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (P (x, ω))
    rw [hR x]
    infer_instance
  let s : ℕ → ℝ≥0 := fun n => (n : ℝ≥0) * Δ
  let G : Path d → ℝ := fun η => F (MarkovProcess.ContinuousPath.shift (WithTop.untopD 0 (τ η)) η)
  have hdet := hω x s (fun _ => F) (fun _ => hF) (fun _ => C) (fun _ => hC)
  have hlocal : ∀ n, ∀ᵐ γ ∂μ, τ γ = (s n : WithTop ℝ≥0) →
      μ[G | hτ.measurableSpace] γ = μ[(fun η => F (MarkovProcess.ContinuousPath.shift (s n) η)) |
        MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) (s n)] γ := by
    intro n
    let A : Set (Path d) := {γ | τ γ = (s n : WithTop ℝ≥0)}
    have hA : MeasurableSet[hτ.measurableSpace] A := hτ.measurableSet_eq' (s n)
    have hslice := condExp_ae_eq_restrict_of_measurableSpace_eq_on (μ := μ)
      (f := G) hτ.measurableSpace_le
      ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le (s n)) hA (by
        intro t
        simpa only [Set.inter_comm] using (hτ.measurableSet_inter_eq_iff t (s n)))
    have hG : Integrable G μ := by
      apply Integrable.of_bound (hF.measurable.comp
        (MarkovProcess.ContinuousPath.measurable_shift_untopD_stoppingTime τ hτ)).aestronglyMeasurable C
      exact Filter.Eventually.of_forall fun γ => hC _
    have hfixed : Integrable (fun η => F (MarkovProcess.ContinuousPath.shift (s n) η)) μ := by
      apply Integrable.of_bound (hF.measurable.comp
        (MarkovProcess.ContinuousPath.measurable_shift_fixed (s n))).aestronglyMeasurable C
      exact Filter.Eventually.of_forall fun γ => hC _
    have hzero : μ[(fun η => G η - F (MarkovProcess.ContinuousPath.shift (s n) η)) |
        MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) (s n)] =ᵐ[μ.restrict A] 0 := by
      apply condExp_ae_eq_restrict_zero (hτ.measurableSet_eq (s n))
      filter_upwards [ae_restrict_mem ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le (s n) _ (hτ.measurableSet_eq (s n)))] with γ hγ
      change τ γ = (s n : WithTop ℝ≥0) at hγ
      change G γ - F (MarkovProcess.ContinuousPath.shift (s n) γ) = 0
      dsimp only [G]
      rw [hγ]
      simp only [WithTop.untopD_coe, sub_self]
    have hsub := condExp_sub hG hfixed (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) (s n))
    have hsub' := ae_restrict_of_ae hsub (s := A)
    rw [Filter.EventuallyEq] at hslice hzero
    rw [ae_restrict_iff' ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le (s n) _ (hτ.measurableSet_eq (s n)))] at hslice hzero hsub'
    filter_upwards [hslice, hzero, hsub'] with γ ha hz hb hγ
    have ha := ha hγ
    have hz := hz hγ
    have hb := hb hγ
    change μ[G - (fun η => F (MarkovProcess.ContinuousPath.shift (s n) η)) |
      MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) (s n)] γ = 0 at hz
    dsimp only [Pi.sub_apply, Pi.zero_apply] at hz hb
    linarith
  filter_upwards [hdet, ae_all_iff.mpr hlocal] with γ hdet hlocal hfinite
  obtain htop | ⟨n, hn⟩ := hgrid γ
  · exact (hfinite htop).elim
  · rw [hlocal n hn, hdet n]
    simp [s] at hn ⊢
    rw [hn]
    rfl

end EinsteinFull
