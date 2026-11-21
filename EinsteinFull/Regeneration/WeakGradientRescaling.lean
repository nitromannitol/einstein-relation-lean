import EinsteinFull.Regeneration.ExitPayoffBoundary
import EinsteinRelation.Correctors.SpatialWeakDilation
import EinsteinRelation.Calculus.WeakGradientTranslation

/-!
# Affine rescaling of weak gradients

A full-space weak gradient whose data are square integrable on compact sets is carried by
the affine map `z ↦ c + r • z` to the rescaled gradient `r • g (c + r • z)`, and the
rescaled data remain square integrable on compact sets.
-/

open MeasureTheory Set EinsteinRelation

namespace EinsteinFull.Regeneration

variable {d : ℕ}

/-- Square integrability on compact sets gives it on Euclidean balls. -/
theorem memLp_euclideanBall_of_compact {E : Type*} [NormedAddCommGroup E] (f : Vec d → E)
    (hf : ∀ K : Set (Vec d), IsCompact K → MemLp f 2 (volume.restrict K)) (R : ℝ) :
    MemLp f 2 (volume.restrict (External.AKM.ball (0 : Vec d) R)) := by
  apply (hf (Metric.closedBall 0 R) (isCompact_closedBall 0 R)).mono_measure
  apply Measure.restrict_mono_set
  intro x hx
  change euclideanNorm (x - 0) < R at hx
  rw [sub_zero] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_euclideanNorm x).trans hx.le

/-- Translation preserves square integrability on Euclidean balls. -/
theorem memLp_comp_add_left_euclideanBall {E : Type*} [NormedAddCommGroup E] (f : Vec d → E)
    (hf : ∀ K : Set (Vec d), IsCompact K → MemLp f 2 (volume.restrict K)) (c : Vec d)
    (R : ℝ) :
    MemLp (fun y => f (c + y)) 2 (volume.restrict (External.AKM.ball (0 : Vec d) R)) := by
  have hmp := (measurePreserving_add_left (volume : Measure (Vec d)) c).restrict_preimage_emb
    (Homeomorph.addLeft c).measurableEmbedding (Metric.closedBall c R)
  have h := (hf _ (isCompact_closedBall c R)).comp_measurePreserving hmp
  have hpre : (fun y : Vec d => c + y) ⁻¹' Metric.closedBall c R = Metric.closedBall 0 R := by
    ext y
    simp only [mem_preimage, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      sub_zero]
  rw [hpre] at h
  apply h.mono_measure
  apply Measure.restrict_mono_set
  intro x hx
  change euclideanNorm (x - 0) < R at hx
  rw [sub_zero] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_euclideanNorm x).trans hx.le

/-- Affine changes of variable preserve square integrability on compact sets. -/
theorem memLp_comp_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Vec d → E)
    (hf : ∀ K : Set (Vec d), IsCompact K → MemLp f 2 (volume.restrict K)) (c : Vec d)
    (r a : ℝ) (hr : 0 < r) :
    ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun z => a • f (c + r • z)) 2 (volume.restrict K) := by
  have h := Correctors.memLp_two_on_euclidean_balls_dilation (fun y => f (c + y))
    (fun R _ => memLp_comp_add_left_euclideanBall f hf c R) r a hr
  exact Correctors.memLp_on_compacts_of_euclidean_balls _ h

/-- The affine image `z ↦ c + r • z` of a full-space weak gradient whose data are square
integrable on compact sets. -/
theorem hasWeakGradient_affine_rescale (u : Vec d → ℝ) (g : Vec d → Vec d)
    (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K))
    (hg : ∀ K : Set (Vec d), IsCompact K → MemLp g 2 (volume.restrict K))
    (hw : HasWeakGradient Set.univ u g) (c : Vec d) (r : ℝ) (hr : 0 < r) :
    HasWeakGradient Set.univ (fun z => u (c + r • z)) (fun z => r • g (c + r • z)) := by
  have h1 := Correctors.hasWeakGradient_dilation u g
    (fun R _ => memLp_euclideanBall_of_compact u hu R)
    (fun R _ => memLp_euclideanBall_of_compact g hg R) hw r 1 hr
  have h2 := h1.comp_add_left (r⁻¹ • c)
  have hpt : ∀ z : Vec d, r • (r⁻¹ • c + z) = c + r • z := fun z => by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  simp only [one_mul, hpt] at h2
  exact h2

end EinsteinFull.Regeneration
