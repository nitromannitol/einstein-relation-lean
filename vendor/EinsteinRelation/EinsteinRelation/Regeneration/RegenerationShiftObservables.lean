import EinsteinRelation.Regeneration.Measurability
import EinsteinRelation.Regeneration.Coupling

/-! # Measurability of the regeneration-shift observables

Source `paper/main.tex:377–403,477–487`. The literal regeneration time
`regenerationTime Δ lam R · i n` is measurable on the coupled sample space
(`measurable_regenerationTime`). Joint evaluation of a path at a time, the
time shift of the coupled sample, spatial recentering, and the physical
translation of the environment are composed from it, so each observable is
measurable as a function of the sample (and of the environment, where stated).

The regeneration time is totalized by `ENNReal.toNNReal`, so an infinite value
is sent to `0`; no finiteness of the regeneration time is claimed or assumed.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

/-- Joint evaluation `(t, γ) ↦ γ t` of a path at a nonnegative time. -/
theorem measurable_path_eval {d : ℕ} :
    Measurable (fun p : ℝ≥0 × Path d => p.2 p.1) := by
  have hcont : Continuous (fun p : ℝ≥0 × Path d => p.2 p.1) :=
    continuous_snd.eval continuous_fst
  exact hcont.measurable

/-- Spatial recentering `(x, z) ↦ z - x` of a coupled sample is jointly measurable. -/
theorem measurable_recenterSample {d : ℕ} :
    Measurable (fun q : Vec d × CoupledSample d => recenterSample q.1 q.2) := by
  have hpath : Measurable (fun q : Vec d × CoupledSample d =>
      (⟨fun t => q.2.1 t - q.1, q.2.1.continuous.sub continuous_const⟩ : Path d)) :=
    (Probability.continuous_path_recenter (d := d)).measurable.comp
      (measurable_fst.prodMk measurable_snd.fst)
  exact hpath.prodMk measurable_snd.snd

/-- Source regeneration recentering. The coupled sample time-shifted to the
regeneration time, recentered at the path position at that same time, is
measurable in the coupled sample. -/
theorem measurable_regeneration_recentered_sample {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (n : ℕ) :
    Measurable (fun z : CoupledSample d =>
      recenterSample (z.1 ((regenerationTime Δ lam R z i n).toNNReal))
        (sampleTimeShift Δ z ((regenerationTime Δ lam R z i n).toNNReal))) := by
  have hτ : Measurable (fun z : CoupledSample d => (regenerationTime Δ lam R z i n).toNNReal) :=
    (measurable_regenerationTime Δ lam R i n).ennreal_toNNReal
  have hx : Measurable (fun z : CoupledSample d =>
      z.1 ((regenerationTime Δ lam R z i n).toNNReal)) :=
    (measurable_path_eval (d := d)).comp (hτ.prodMk measurable_fst)
  have hs : Measurable (fun z : CoupledSample d =>
      sampleTimeShift Δ z ((regenerationTime Δ lam R z i n).toNNReal)) :=
    (measurable_sampleTimeShift Δ).comp (hτ.prodMk measurable_id)
  exact (measurable_recenterSample (d := d)).comp (hx.prodMk hs)

/-- Source regeneration environment. The environment translated by the path
position at the regeneration time is measurable as a function of the pair of
environment and coupled sample. -/
theorem measurable_regeneration_environment {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (n : ℕ) :
    Measurable (fun ωz : FieldPair d × CoupledSample d =>
      translate (ωz.2.1 ((regenerationTime Δ lam R ωz.2 i n).toNNReal)) ωz.1) := by
  have hτ : Measurable (fun ωz : FieldPair d × CoupledSample d =>
      (regenerationTime Δ lam R ωz.2 i n).toNNReal) :=
    ((measurable_regenerationTime Δ lam R i n).comp measurable_snd).ennreal_toNNReal
  have hx : Measurable (fun ωz : FieldPair d × CoupledSample d =>
      ωz.2.1 ((regenerationTime Δ lam R ωz.2 i n).toNNReal)) :=
    (measurable_path_eval (d := d)).comp (hτ.prodMk measurable_snd.fst)
  exact (Probability.continuous_translate (d := d)).measurable.comp (hx.prodMk measurable_fst)

end EinsteinRelation.Regeneration
