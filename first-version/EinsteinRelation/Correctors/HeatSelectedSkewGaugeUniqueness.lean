import EinsteinRelation.Correctors.HeatSelectedSkewMeaningSupport
import EinsteinRelation.Correctors.NormalizedScalarCorrectorUniqueness
import EinsteinRelation.Calculus.WeakRepresentativeOperations
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Gauge uniqueness for the heat-selected flux corrector

Source: `paper/main.tex:755-756`. The local L² limits of the literal
heat-gradient truncations are unique. Equal weak gradients then make
the potentials equal up to entrywise spatial constants.
-/

open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning NormalizedScalarCorrectorUniqueness

/-- Local L² convergence of the same approximants has a unique a.e. limit. -/
theorem ae_eq_of_common_L2_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : ℕ × ℕ → Ω → ℝ) (f g : Ω → ℝ)
    (hT : ∀ n, MemLp (T n) 2 μ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hTf : Tendsto (fun n => eLpNorm (T n - f) 2 μ) atTop (𝓝 0))
    (hTg : Tendsto (fun n => eLpNorm (T n - g) 2 μ) atTop (𝓝 0)) :
    f =ᵐ[μ] g := by
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun n => (hT n).aestronglyMeasurable) hf.aestronglyMeasurable hTf)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun n => (hT n).aestronglyMeasurable) hg.aestronglyMeasurable hTg)

/-- The frozen heat selection fixes each potential entry modulo a constant;
there is no additional uniqueness hypothesis. -/
theorem ae_heatSelectedSkew_potentials_differ_by_constants
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (σ τ : FieldPair d → Vec d → Mat d)
    (hσ : HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ)
    (hτ : HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i τ) :
    ∀ᵐ ρ ∂reducedEnvironmentLaw Q, ∀ j k : Fin d, ∃ c : ℝ,
      (fun x => σ ρ x j k) =ᵐ[volume] (fun x => τ ρ x j k + c) := by
  obtain ⟨F, _, hF⟩ := hσ
  obtain ⟨G, _, hG⟩ := hτ
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  have hcover : (⋃ R : ℕ, Metric.ball (0 : Vec d) ((R + 1 : ℕ) : ℝ)) = Set.univ := by
    apply Set.iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine ⟨N, ?_⟩
    simp only [Metric.mem_ball, dist_zero_right, Nat.cast_add, Nat.cast_one]
    linarith
  filter_upwards [hF, hG] with ρ hFρ hGρ
  intro j k
  have heq (ℓ : Fin d) :
      (fun x => F (translate x ρ) j k ℓ) =ᵐ[volume]
        (fun x => G (translate x ρ) j k ℓ) := by
    have hlocal (R : ℕ) :
        (fun x => F (translate x ρ) j k ℓ) =ᵐ[
          volume.restrict (Metric.ball (0 : Vec d) ((R + 1 : ℕ) : ℝ))]
        (fun x => G (translate x ρ) j k ℓ) := by
      have hF' := hFρ.2.1 j k ℓ R
      have hG' := hGρ.2.1 j k ℓ R
      exact ae_eq_of_common_L2_limit _
        (fun n x => iteratedAKMHeatGradientTruncation _ n.1 n.2 j k ℓ x) _ _
        (fun n => hF'.2.1 n.1 n.2) hF'.2.2.1 hG'.2.2.1 hF'.2.2.2 hG'.2.2.2
    have h := (ae_restrict_iUnion_iff _ _).mpr hlocal
    simpa only [hcover, Measure.restrict_univ] using h
  have hweakF := hFρ.2.2 j k
  have hweakG : HasWeakGradient Set.univ (fun x => τ ρ x j k)
      (fun x ℓ => F (translate x ρ) j k ℓ) := by
    intro ℓ
    apply (hGρ.2.2 j k ℓ).congr_ae (ae_eq_refl _)
    simpa only [Measure.restrict_univ] using (heq ℓ).symm
  have hloc : LocallyIntegrable (fun x => σ ρ x j k - τ ρ x j k) volume :=
    (locallyIntegrableOn_univ.mp (hweakF ⟨0, hd⟩).1).sub
      (locallyIntegrableOn_univ.mp (hweakG ⟨0, hd⟩).1)
  obtain ⟨c, hc⟩ := ae_eq_const_of_zero_weak_gradient hloc
    (fun ℓ η hη => integral_sub_mul_coordinateDerivative_eq_zero hweakF hweakG ℓ hη)
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  change σ ρ x j k - τ ρ x j k = c at hx
  linarith

end EinsteinRelation.Correctors
