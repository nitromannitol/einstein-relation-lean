import EinsteinRelation.Correctors.MeasurableRegularRepresentative
import EinsteinRelation.Correctors.ContinuousAverageRecovery

/-! Source: `paper/main.tex:688-702,754-758`. Shrinking averages select
continuous versions on an exhaustion, with joint measurability inherited
from the supplied spatial field. No samplewise choice enters the selector. -/

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace EinsteinRelation.Correctors

/-- The shrinking-average selector agrees at every interior point with
a continuous local representative of its spatial volume class. -/
theorem spatialRegularRepresentative_eq_of_continuousOn_ae {d : ℕ}
    (f v : Vec d → ℝ) (U : Set (Vec d)) (hU : IsOpen U)
    (hv : ContinuousOn v U) (heq : f =ᵐ[volume.restrict U] v) (x : Vec d) (hx : x ∈ U) :
    spatialRegularRepresentative (fun _ : Unit => f) () x = v x := by
  exact (tendsto_local_average_of_continuousOn_ae f v U hU hv heq x hx).limUnder_eq

/-- Continuous local versions on the integer-ball exhaustion identify
a global continuous version selected entirely by measurable averages. -/
theorem continuous_spatialRegularRepresentative_of_ball_versions {d : ℕ}
    (f : Vec d → ℝ)
    (h : ∀ n : ℕ, ∃ v : Vec d → ℝ,
      ContinuousOn v (Metric.ball 0 ((n : ℝ) + 1)) ∧
      f =ᵐ[volume.restrict (Metric.ball 0 ((n : ℝ) + 1))] v) :
    Continuous (spatialRegularRepresentative (fun _ : Unit => f) ()) ∧
      f =ᵐ[volume] spatialRegularRepresentative (fun _ : Unit => f) () := by
  let r := spatialRegularRepresentative (fun _ : Unit => f) ()
  have heq (n : ℕ) (v : Vec d → ℝ)
      (hv : ContinuousOn v (Metric.ball 0 ((n : ℝ) + 1)))
      (he : f =ᵐ[volume.restrict (Metric.ball 0 ((n : ℝ) + 1))] v) :
      Set.EqOn r v (Metric.ball 0 ((n : ℝ) + 1)) := by
    intro x hx
    exact spatialRegularRepresentative_eq_of_continuousOn_ae f v _ Metric.isOpen_ball hv he x hx
  have hxball (x : Vec d) : ∃ n : ℕ, x ∈ Metric.ball (0 : Vec d) ((n : ℝ) + 1) := by
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    exact ⟨n, by simpa only [Metric.mem_ball, dist_zero_right] using hn.trans (by linarith)⟩
  refine ⟨continuous_iff_continuousAt.mpr (fun x => ?_), ?_⟩
  · obtain ⟨n, hxn⟩ := hxball x
    obtain ⟨v, hv, hfv⟩ := h n
    have hrv := heq n v hv hfv
    have hnear : r =ᶠ[𝓝 x] v := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxn] with y hy
      exact hrv hy
    change Tendsto r (𝓝 x) (𝓝 (r x))
    rw [hrv hxn]
    exact (hv.continuousAt (Metric.isOpen_ball.mem_nhds hxn)).congr' hnear.symm
  · have hall : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure (Vec d)),
        x ∈ Metric.ball 0 ((n : ℝ) + 1) → f x = r x := by
      intro n
      obtain ⟨v, hv, hfv⟩ := h n
      have ha : ∀ᵐ x ∂volume.restrict (Metric.ball 0 ((n : ℝ) + 1)), f x = r x := by
        filter_upwards [hfv, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxm
        exact hx.trans (heq n v hv hfv hxm).symm
      exact (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp ha
    filter_upwards [ae_all_iff.mpr hall] with x hx
    obtain ⟨n, hn⟩ := hxball x
    exact hx n hn

/-- The generic measurable selector regularizes almost every environment
on a single event, without any measurability premise on local witnesses. -/
theorem ae_continuous_spatialRegularRepresentative_of_ball_versions
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → Vec d → ℝ)
    (h : ∀ᵐ ω ∂μ, ∀ n : ℕ, ∃ v : Vec d → ℝ,
      ContinuousOn v (Metric.ball 0 ((n : ℝ) + 1)) ∧
      f ω =ᵐ[volume.restrict (Metric.ball 0 ((n : ℝ) + 1))] v) :
    ∀ᵐ ω ∂μ, Continuous (spatialRegularRepresentative f ω) ∧
      f ω =ᵐ[volume] spatialRegularRepresentative f ω := by
  filter_upwards [h] with ω hω
  exact continuous_spatialRegularRepresentative_of_ball_versions (f ω) hω

end EinsteinRelation.Correctors
