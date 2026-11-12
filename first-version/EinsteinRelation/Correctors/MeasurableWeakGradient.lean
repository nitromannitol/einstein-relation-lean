import EinsteinRelation.Correctors.ShiftedMollifierMeans
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.LiminfLimsup

/-! # Joint measurable versions of actual weak gradients

Source: `paper/main.tex:789–816,913–925`. A jointly measurable scalar field
with samplewise whole-space Sobolev gradients determines a jointly measurable
gradient version. It is recovered from derivatives of scalar convolutions,
not from an assumed measurable selection of the supplied gradients.
-/

open MeasureTheory Filter
open scoped Topology Convolution

namespace EinsteinRelation.Correctors

private noncomputable def gradientRecoveryBump (d n : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := 1 / ((n : ℝ) + 1) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith only [h]

private theorem ae_tendsto_recovered_weakDerivative {d : ℕ}
    {f g : Vec d → ℝ} {j : Fin d}
    (hfg : HasWeakPartialDerivative Set.univ j f g) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      Tendsto (fun n => (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        coordinateDerivative j ((gradientRecoveryBump d n).normed volume)) x)
        atTop (𝓝 (g x)) := by
  have hg : LocallyIntegrable g volume := locallyIntegrableOn_univ.mp hfg.2.1
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) (φ := gradientRecoveryBump d)
    tendsto_one_div_add_atTop_nhds_zero_nat
    (Filter.Eventually.of_forall fun n => (show
      1 / ((n : ℝ) + 1) ≤ 2 * (1 / ((n : ℝ) + 1) / 2) by ring_nf; rfl)) hg
  filter_upwards [hconv] with x hx
  convert hx using 1
  funext n
  rw [convolution_coordinateDerivative_eq_weakDerivative hfg
    (gradientRecoveryBump d n).contDiff_normed
    (gradientRecoveryBump d n).hasCompactSupport_normed]
  rw [convolution_eq_swap]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => mul_comm _ _

private noncomputable def mollifiedGradientCoordinate {Ω : Type*} {d : ℕ}
    (f : Ω → Vec d → ℝ) (n : ℕ) (j : Fin d) (z : Ω × Vec d) : ℝ :=
  (f z.1 ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    coordinateDerivative j ((gradientRecoveryBump d n).normed volume)) z.2

private theorem measurable_mollifiedGradientCoordinate {Ω : Type*}
    [MeasurableSpace Ω] {d : ℕ} (f : Ω → Vec d → ℝ)
    (hfm : Measurable (fun z : Ω × Vec d => f z.1 z.2)) (n : ℕ) (j : Fin d) :
    Measurable (mollifiedGradientCoordinate f n j) := by
  have hD : Continuous (coordinateDerivative j ((gradientRecoveryBump d n).normed volume)) :=
    ((contDiff_infty_iff_fderiv.mp (gradientRecoveryBump d n).contDiff_normed).2.clm_apply
      contDiff_const).continuous
  have hm : Measurable (fun z : (Ω × Vec d) × Vec d =>
      f z.1.1 z.2 * coordinateDerivative j ((gradientRecoveryBump d n).normed volume)
        (z.1.2 - z.2)) :=
    (hfm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hD.measurable.comp ((measurable_snd.comp measurable_fst).sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- A jointly measurable scalar field determines a measurable recovery of
all its actual whole-space weak gradients. No measurability of a chosen
gradient family is assumed. Source: `paper/main.tex:789–816,913–925`. -/
theorem exists_measurable_spatialGradient_recovery {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (f : Ω → Vec d → ℝ)
    (hfm : Measurable (fun z : Ω × Vec d => f z.1 z.2)) :
    ∃ H : Ω → Vec d → Vec d,
      Measurable (fun z : Ω × Vec d => H z.1 z.2) ∧
      ∀ (ω : Ω) (G : Vec d → Vec d), HasWeakGradient Set.univ (f ω) G →
        (fun x => H ω x) =ᵐ[volume] G := by
  let H : Ω → Vec d → Vec d := fun ω x j =>
    liminf (fun n => mollifiedGradientCoordinate f n j (ω, x)) atTop
  refine ⟨H, ?_, ?_⟩
  · apply measurable_pi_lambda
    intro j
    exact Measurable.liminf (fun n => measurable_mollifiedGradientCoordinate f hfm n j)
  · intro ω G hω
    have hconv (j : Fin d) : ∀ᵐ x ∂(volume : Measure (Vec d)),
        Tendsto (fun n => mollifiedGradientCoordinate f n j (ω, x)) atTop (𝓝 (G x j)) := by
      change ∀ᵐ x ∂(volume : Measure (Vec d)),
        Tendsto (fun n => ((f ω) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          coordinateDerivative j ((gradientRecoveryBump d n).normed volume)) x)
          atTop (𝓝 (G x j))
      exact ae_tendsto_recovered_weakDerivative
        (f := f ω) (g := fun x => G x j) (j := j) (hω j)
    filter_upwards [ae_all_iff.mpr hconv] with x hx
    funext j
    exact (hx j).liminf_eq

/-- An almost surely specified Sobolev gradient has a jointly measurable
version recovered from its scalar potential. Source: `paper/main.tex:789–816,913–925`. -/
theorem exists_measurable_weakGradient_version {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (Q : Measure Ω) (f : Ω → Vec d → ℝ) (G : Ω → Vec d → Vec d)
    (hfm : Measurable (fun z : Ω × Vec d => f z.1 z.2))
    (hweak : ∀ᵐ ω ∂Q, HasWeakGradient Set.univ (f ω) (G ω)) :
    ∃ H : Ω → Vec d → Vec d,
      Measurable (fun z : Ω × Vec d => H z.1 z.2) ∧
      ∀ᵐ ω ∂Q, (fun x => H ω x) =ᵐ[volume] (G ω) := by
  obtain ⟨H, hHm, hHG⟩ := exists_measurable_spatialGradient_recovery f hfm
  exact ⟨H, hHm, hweak.mono fun ω hω => hHG ω (G ω) hω⟩

end EinsteinRelation.Correctors
