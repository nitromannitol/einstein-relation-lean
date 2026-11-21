import EinsteinFull.External.DFGW.ErgodicFixedObservable
import EinsteinFull.External.DFGW.TransitionConstant
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-! # Mean ergodic theorem for the state semigroup

For each positive time step, the Cesàro averages of the transition operator converge in `L²` to
the stationary mean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Discrete-time averages of any state observable converge in `L²` to its stationary mean. -/
theorem tendsto_transitionOperator_birkhoffAverage
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (hμ : μ Set.univ ≠ ⊤)
    {t : ℝ≥0} (ht : 0 < t)
    (f : Lp ℝ 2 μ) :
    Tendsto (birkhoffAverage ℝ (transitionOperator hP t) id · f) atTop
      (𝓝 (indicatorConstLp 2 MeasurableSet.univ hμ
        (∫ x, f x ∂μ))) := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let U := transitionOperator hP t
  let K := U.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  let p := K.orthogonalProjectionOnto f
  have hpfix : U p = p := p.property
  obtain ⟨c, hc⟩ := ae_eq_const_of_transitionOperator_fixed hP p ht hpfix
  let one : Lp ℝ 2 μ := indicatorConstLp 2 MeasurableSet.univ hμ 1
  have honefix : U one = one := transitionOperator_indicator_univ hP _ 1 t
  have honeK : one ∈ K := honefix
  have hinner : inner ℝ one p = inner ℝ one f := by
    have hp := K.inner_orthogonalProjectionOnto_eq_of_mem_right ⟨one, honeK⟩ f
    change inner ℝ (p : Lp ℝ 2 μ) one = inner ℝ f one at hp
    exact (real_inner_comm (p : Lp ℝ 2 μ) one).trans (hp.trans (real_inner_comm one f))
  have honeae : one =ᵐ[μ] fun _ => (1 : ℝ) := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := measure_ne_top μ Set.univ) (c := (1 : ℝ))] with x hx
    simpa only [one, Set.indicator_univ] using hx
  have hinnerp : inner ℝ one p = c := by
    rw [L2.inner_def]
    calc
      _ = ∫ _ : S, c ∂μ := by
        apply integral_congr_ae
        filter_upwards [honeae, hc] with x ho hp
        simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, ho, hp, mul_one]
      _ = c := by simp
  have hinnerf : inner ℝ one f = ∫ x, f x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [honeae] with x hx
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, mul_one]
  have hcmean : c = ∫ x, f x ∂μ := hinnerp.symm.trans (hinner.trans hinnerf)
  have hpeq : (p : Lp ℝ 2 μ) =
      indicatorConstLp 2 MeasurableSet.univ hμ (∫ x, f x ∂μ) := by
    apply Lp.ext
    filter_upwards [hc, indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := measure_ne_top μ Set.univ) (c := ∫ x, f x ∂μ)] with x hx hy
    simp only [Set.indicator_univ] at hy
    rw [hx, hy, hcmean]
  have h := ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection U
    (norm_transitionOperator_le_one hP t) f
  change Tendsto (birkhoffAverage ℝ U id · f) atTop (𝓝 (p : Lp ℝ 2 μ)) at h
  rw [hpeq] at h
  exact h

end EinsteinFull.External.DFGW
