import EinsteinRelation.Correctors.CubeMaximalWeakBound
import Mathlib.MeasureTheory.Group.Integral

/-!
# Localization of the cube maximal bound

Source: `paper/main.tex:693-698`. Truncating a locally integrable spatial
field on an enlarged cube reduces bad centers in a bounded observation
cube to the global deterministic maximal estimate.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- Translate an integral on a coordinate cube to the cube with translated
center. -/
theorem integerCube_integral_add_right {d : ℕ} (f : Vec d → ℝ) (x : Vec d) (r : ℝ) :
    (∫ y in Metric.closedBall (0 : Vec d) r, f (y + x) ∂volume) =
      ∫ y in Metric.closedBall x r, f y ∂volume := by
  have hp : (fun y : Vec d => y + x) ⁻¹' Metric.closedBall x r =
      Metric.closedBall 0 r := by
    ext y
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm,
      add_sub_cancel_right, sub_zero]
  have hm := measurePreserving_add_right (volume : Measure (Vec d)) x
  rw [← hp]
  exact hm.setIntegral_preimage_emb (MeasurableEquiv.addRight x).measurableEmbedding f _

/-- A whole-space weak maximal bound controls bad centers in any finite
observation cube, using only local integrability on its enlargement. -/
theorem localized_integerCube_maximal_bound (d : ℕ) (C : ℝ)
    (hmax : ∀ f : Vec d → ℝ, Integrable f volume → (∀ x, 0 ≤ f x) →
      ∀ S t : ℝ, 0 < S → 0 < t →
        volume {x | ∃ r : ℝ, 0 < r ∧ r ≤ S ∧
          t * volume.real (Metric.closedBall x r) <
            ∫ y in Metric.closedBall x r, f y ∂volume} ≤
          ENNReal.ofReal (C / t * ∫ y, f y ∂volume))
    (f : Vec d → ℝ) (hf : ∀ x, 0 ≤ f x)
    (N : ℕ) (R t : ℝ) (hR : 0 < R) (ht : 0 < t)
    (hint : IntegrableOn f (Metric.closedBall 0 (R + (N : ℝ) + 1)) volume) :
    volume {x | x ∈ Metric.closedBall (0 : Vec d) R ∧
      ∃ n : ℕ, n < N ∧
        t * volume.real (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)) <
          ∫ y in Metric.closedBall (0 : Vec d) ((n : ℝ) + 1), f (y + x) ∂volume} ≤
      ENNReal.ofReal (C / t * ∫ y in Metric.closedBall 0 (R + (N : ℝ) + 1), f y ∂volume) := by
  let K := Metric.closedBall (0 : Vec d) (R + (N : ℝ) + 1)
  let F := K.indicator f
  have hF : Integrable F volume := hint.integrable_indicator measurableSet_closedBall
  have hFn : ∀ x, 0 ≤ F x := fun x => Set.indicator_nonneg (fun y _ => hf y) x
  have hs : {x | x ∈ Metric.closedBall (0 : Vec d) R ∧
      ∃ n : ℕ, n < N ∧ t * volume.real (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)) <
        ∫ y in Metric.closedBall (0 : Vec d) ((n : ℝ) + 1), f (y + x) ∂volume} ⊆
      {x | ∃ r : ℝ, 0 < r ∧ r ≤ (N : ℝ) + 1 ∧
        t * volume.real (Metric.closedBall x r) < ∫ y in Metric.closedBall x r, F y ∂volume} := by
    rintro x ⟨hx, n, hn, hb⟩
    have hsub : Metric.closedBall x ((n : ℝ) + 1) ⊆ K := by
      intro y hy
      have hh := (dist_triangle y x 0).trans (add_le_add hy hx)
      apply hh.trans
      have hcast : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.le
      linarith
    refine ⟨(n : ℝ) + 1, by positivity, ?_, ?_⟩
    · exact_mod_cast Nat.add_le_add_right hn.le 1
    · have heq : (∫ y in Metric.closedBall x ((n : ℝ) + 1), F y ∂volume) =
          ∫ y in Metric.closedBall x ((n : ℝ) + 1), f y ∂volume := by
        apply setIntegral_congr_fun measurableSet_closedBall
        intro y hy
        exact Set.indicator_of_mem (hsub hy) f
      rw [heq, ← integerCube_integral_add_right]
      have hv : volume.real (Metric.closedBall x ((n : ℝ) + 1)) =
          volume.real (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)) := by
        simp only [Measure.real]
        rw [Real.volume_pi_closedBall x (by positivity),
          Real.volume_pi_closedBall 0 (by positivity)]
      rwa [hv]
  calc
    _ ≤ volume {x | ∃ r : ℝ, 0 < r ∧ r ≤ (N : ℝ) + 1 ∧
        t * volume.real (Metric.closedBall x r) < ∫ y in Metric.closedBall x r, F y ∂volume} :=
      measure_mono hs
    _ ≤ ENNReal.ofReal (C / t * ∫ y, F y ∂volume) :=
      hmax F hF hFn _ t (by positivity) ht
    _ = _ := by rw [integral_indicator measurableSet_closedBall]

end EinsteinRelation.Correctors
