import EinsteinRelation.Correctors.HolderContinuity
import EinsteinRelation.Correctors.SpatialBallVolume

/-! Source: `paper/main.tex:735-743`. Locally bounded Hölder sources
have the local L² data required for the Poisson dimension lift. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Bounded component Hölder norms imply local square integrability. -/
theorem memLp_on_euclidean_balls_of_holder_components {d : ℕ}
    (F : Vec d → Vec d) (hFm : Measurable F)
    (hF : ∀ R : ℝ, 0 < R → ∃ K : ℝ, ∀ j,
      HolderBound (ball 0 R) (1 / 2) (fun x => F x j) K) :
    ∀ R : ℝ, 0 < R → MemLp F 2 (volume.restrict (ball 0 R)) := by
  intro R hR
  obtain ⟨K, hK⟩ := hF R hR
  have hvol := ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr hvol.2.ne
  apply MemLp.of_bound hFm.aestronglyMeasurable |K|
  filter_upwards [ae_restrict_mem (by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet)] with x hx
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg K)).mpr
  intro j
  obtain ⟨S, H, _, hH, hSH, hs, _⟩ := hK j
  rw [Real.norm_eq_abs]
  exact (hs x hx).trans (by linarith [le_abs_self K])

end EinsteinRelation.Correctors
