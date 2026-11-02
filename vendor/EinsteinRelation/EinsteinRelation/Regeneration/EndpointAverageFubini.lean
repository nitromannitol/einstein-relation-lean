import EinsteinRelation.Regeneration.EndpointBallVolume
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure

/-!
# Fubini for the actual endpoint balls

Source `paper/main.tex:391–397`. The endpoint ball has a volume independent
of its centre. Bounded tests supported in that moving ball are integrable
for a probability law times spatial volume, so the endpoint average may
be interchanged with the past-law integral.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

/-- Translation of the endpoint ball preserves its spatial volume. -/
theorem endpointBall_volume_eq {d : ℕ} (i : Fin d) (R : ℝ) (x : Vec d) :
    volume (endpointBall i R x) = volume (endpointBall i R 0) := by
  have hs : endpointBall i R x =
      (fun y : Vec d => -x + y) ⁻¹' endpointBall i R 0 := by
    ext y
    change euclideanNorm (y - (x + (9 * R) • unitVector i)) < R ↔
      euclideanNorm ((-x + y) - (0 + (9 * R) • unitVector i)) < R
    abel_nf
  rw [hs, measure_preimage_add]

private theorem continuous_euclideanNorm_fubini {d : ℕ} :
    Continuous (fun v : Vec d => euclideanNorm v) := by
  unfold euclideanNorm euclideanSq dot
  exact Real.continuous_sqrt.comp
    (continuous_finset_sum _ (fun j _ => (continuous_apply j).mul (continuous_apply j)))

/-- Membership in the endpoint ball is measurable jointly in its base point
and in the endpoint. -/
theorem measurableSet_endpointBall_pair {d : ℕ} (i : Fin d) (R : ℝ) :
    MeasurableSet {p : Vec d × Vec d | p.2 ∈ endpointBall i R p.1} := by
  have hcont : Continuous (fun p : Vec d × Vec d =>
      euclideanNorm (p.2 - (p.1 + (9 * R) • unitVector i))) :=
    continuous_euclideanNorm_fubini.comp
      (continuous_snd.sub (continuous_fst.add continuous_const))
  exact (isOpen_lt hcont continuous_const).measurableSet

/-- A jointly measurable future version has a measurable endpoint average,
also when its base point depends on the past. -/
theorem measurable_endpointAverage {d : ℕ} {α : Type*} [MeasurableSpace α]
    (i : Fin d) (R : ℝ) (X : α → Vec d) (hX : Measurable X)
    (B : α × Vec d → ℝ) (hB : Measurable B) :
    Measurable (fun a => endpointAverage i R (X a) (fun y => B (a, y))) := by
  let J : α × Vec d → ℝ := fun q =>
    (endpointBall i R (X q.1)).indicator (fun y => B (q.1, y)) q.2
  have hset : MeasurableSet {q : α × Vec d | q.2 ∈ endpointBall i R (X q.1)} :=
    (measurableSet_endpointBall_pair i R).preimage
      ((hX.comp measurable_fst).prodMk measurable_snd)
  have hJ : Measurable J := hB.indicator hset
  have hm := (hJ.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Vec d)))).measurable.div_const
    (volume (endpointBall i R (0 : Vec d))).toReal
  convert hm using 1
  funext a
  have hs : MeasurableSet (endpointBall i R (X a)) :=
    (measurableSet_endpointBall_pair i R).preimage (measurable_const.prodMk measurable_id)
  simp only [J, integral_indicator hs, endpointAverage, endpointBall_volume_eq]

/-- Endpoint averaging preserves an everywhere bound. -/
theorem boundedRealTest_endpointAverage {d : ℕ} {α : Type*}
    (i : Fin d) (R : ℝ) (hR : 0 < R) (X : α → Vec d)
    (B : α × Vec d → ℝ) (hb : BoundedRealTest B) :
    BoundedRealTest (fun a => endpointAverage i R (X a) (fun y => B (a, y))) := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨max C 0, fun a => ?_⟩
  have hV : 0 < (volume (endpointBall i R (X a))).toReal :=
    ENNReal.toReal_pos (endpointBall_volume_pos i R hR _).ne'
      (endpointBall_volume_ne_top i R hR _)
  dsimp only
  rw [endpointAverage, abs_div, abs_of_pos hV]
  apply (div_le_iff₀ hV).mpr
  simpa only [Real.norm_eq_abs, measureReal_def] using
    (norm_setIntegral_le_of_norm_le_const (f := fun y => B (a, y)) (C := max C 0)
      (endpointBall_volume_ne_top i R hR (X a)).lt_top
      (fun y _ => by simpa only [Real.norm_eq_abs] using (hC (a, y)).trans (le_max_left C 0)))

/-- The bounded moving-ball integrand in `regen.slice-factor` is integrable
against the past law and spatial volume. This supplies the Fubini premise. -/
theorem integrable_endpointBall_indicator {d : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : Fin d) (R : ℝ) (hR : 0 < R)
    (X : α → Vec d) (hX : Measurable X)
    (F : α × Vec d → ℝ) (hF : Measurable F) (hb : BoundedRealTest F) :
    Integrable (fun q : α × Vec d =>
      (endpointBall i R (X q.1)).indicator (fun y => F (q.1, y)) q.2)
      (μ.prod volume) := by
  let J : α × Vec d → ℝ := fun q =>
    (endpointBall i R (X q.1)).indicator (fun y => F (q.1, y)) q.2
  have hset : MeasurableSet {q : α × Vec d | q.2 ∈ endpointBall i R (X q.1)} :=
    (measurableSet_endpointBall_pair i R).preimage
      ((hX.comp measurable_fst).prodMk measurable_snd)
  have hJ : Measurable J := hF.indicator hset
  obtain ⟨C, hC⟩ := hb
  have hball : ∀ x : Vec d, MeasurableSet (endpointBall i R x) := fun x =>
    (measurableSet_endpointBall_pair i R).preimage (measurable_const.prodMk measurable_id)
  have hfinite : ∀ x : Vec d, volume (endpointBall i R x) < ⊤ :=
    fun x => (endpointBall_volume_ne_top i R hR x).lt_top
  have hsection : ∀ a, Integrable (fun y => J (a, y)) volume := by
    intro a
    change Integrable ((endpointBall i R (X a)).indicator (fun y => F (a, y))) volume
    haveI : IsFiniteMeasure (volume.restrict (endpointBall i R (X a))) := ⟨by
      simpa only [Measure.restrict_apply_univ] using hfinite (X a)⟩
    have hm : Measurable (fun y : Vec d => F (a, y)) := hF.comp measurable_prodMk_left
    have hi : IntegrableOn (fun y => F (a, y)) (endpointBall i R (X a)) volume :=
      Integrable.of_bound hm.aestronglyMeasurable C
        (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hC (a, y))
    exact hi.integrable_indicator (hball _)
  apply (integrable_prod_iff hJ.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall hsection, ?_⟩
  apply Integrable.of_bound hJ.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    (C * (volume (endpointBall i R (0 : Vec d))).toReal)
  apply Filter.Eventually.of_forall
  intro a
  have hnorm : (fun y => ‖J (a, y)‖) =
      (endpointBall i R (X a)).indicator (fun y => ‖F (a, y)‖) := by
    funext y
    by_cases hy : y ∈ endpointBall i R (X a) <;> simp [J, hy]
  rw [hnorm, integral_indicator (hball _)]
  calc
    ‖∫ y in endpointBall i R (X a), ‖F (a, y)‖‖ ≤
        C * (volume (endpointBall i R (X a))).toReal :=
      norm_setIntegral_le_of_norm_le_const (hfinite _) (fun y _ => by
        simpa only [Real.norm_eq_abs, abs_abs] using hC (a, y))
    _ = C * (volume (endpointBall i R (0 : Vec d))).toReal := by
      rw [endpointBall_volume_eq]

/-- Endpoint averaging and integration over the past law commute, with the
literal spatial ball and its constant denominator (`paper/main.tex:391–397`). -/
theorem integral_mul_endpointAverage_eq {d : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : Fin d) (R : ℝ) (hR : 0 < R)
    (X : α → Vec d) (hX : Measurable X)
    (G : α → ℝ) (hG : Measurable G) (hbG : BoundedRealTest G)
    (B : α × Vec d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B) :
    (∫ a, G a * endpointAverage i R (X a) (fun y => B (a, y)) ∂μ) =
      (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
        ∫ y, ∫ a, (endpointBall i R (X a)).indicator
          (fun y => G a * B (a, y)) y ∂μ := by
  let F : α × Vec d → ℝ := fun q => G q.1 * B q
  have hF : Measurable F := (hG.comp measurable_fst).mul hB
  have hbF : BoundedRealTest F := by
    obtain ⟨CG, hCG⟩ := hbG
    obtain ⟨CB, hCB⟩ := hbB
    refine ⟨max CG 0 * max CB 0, fun q => ?_⟩
    dsimp [F]
    rw [abs_mul]
    exact mul_le_mul ((hCG _).trans (le_max_left _ _))
      ((hCB _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  have hi := integrable_endpointBall_indicator μ i R hR X hX F hF hbF
  have hball : ∀ x : Vec d, MeasurableSet (endpointBall i R x) := fun x =>
    (measurableSet_endpointBall_pair i R).preimage (measurable_const.prodMk measurable_id)
  calc
    _ = ∫ a, (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
        (∫ y, (endpointBall i R (X a)).indicator (fun y => F (a, y)) y) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a
      dsimp only
      rw [integral_indicator (hball _), show (fun y => F (a, y)) =
        (fun y => G a * B (a, y)) from rfl, integral_const_mul,
        endpointAverage, endpointBall_volume_eq]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_integral_swap hi]


end EinsteinRelation.Regeneration
