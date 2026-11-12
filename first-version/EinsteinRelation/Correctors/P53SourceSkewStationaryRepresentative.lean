import EinsteinRelation.Environment.AKMMeasurableRepresentative
import EinsteinRelation.Calculus.HorizontalTranslationLp

/-!
# Stationary representatives of covariant spatial fields

Source: `paper/main.tex:732-748`. AKM (6.7) defines the gradient of the flux
corrector as a stationary field. A jointly measurable family of locally
integrable spatial fields which is covariant under each translation, almost
surely, is the orbit of one measurable environment observable: the upper
limit of its smooth averages at the origin. Lebesgue differentiation and
Fubini's theorem identify the orbit; no measurable selection is used.
-/

open MeasureTheory Filter Topology
open scoped Convolution
noncomputable section
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport

/-- The smooth average at the origin whose upper limit is the representative. -/
def originBumpAverage {d : ℕ} (f : Vec d → ℝ) (n : ℕ) : ℝ :=
  ∫ y, (representativeBump d n).normed volume (-y) * f y

/-- The upper limit of the smooth origin averages of a sample field. -/
def stationaryRepresentative {d : ℕ} (G : FieldPair d → Vec d → ℝ)
    (ρ : FieldPair d) : ℝ :=
  limsup (fun n => originBumpAverage (G ρ) n) atTop

theorem measurable_stationaryRepresentative {d : ℕ} {G : FieldPair d → Vec d → ℝ}
    (hG : Measurable (fun p : FieldPair d × Vec d => G p.1 p.2)) :
    Measurable (stationaryRepresentative G) := by
  apply Measurable.limsup
  intro n
  have hb : Measurable (fun y : Vec d => (representativeBump d n).normed volume (-y)) :=
    ((representativeBump d n).continuous_normed.comp continuous_neg).measurable
  have hj : StronglyMeasurable (fun p : FieldPair d × Vec d =>
      (representativeBump d n).normed volume (-p.2) * G p.1 p.2) :=
    ((hb.comp measurable_snd).mul hG).stronglyMeasurable
  exact hj.integral_prod_right'.measurable

/-- Along a covariant orbit the origin averages are the smooth averages of the
original sample at the translated point. -/
theorem originBumpAverage_translate_eq {d : ℕ} {f h : Vec d → ℝ} (x : Vec d)
    (hfx : ∀ᵐ y ∂(volume : Measure (Vec d)), h y = f (y + x)) (n : ℕ) :
    originBumpAverage h n =
      ((representativeBump d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x := by
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  unfold originBumpAverage
  rw [integral_congr_ae (hfx.mono fun y hy => by rw [hy])]
  have h := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
    (fun y => (representativeBump d n).normed volume (x - y) * f y) x
  simp only [sub_add_eq_sub_sub, sub_sub_cancel_left] at h
  exact h

/-- For a single locally integrable sample, the origin averages along a covariant
orbit recover the sample almost everywhere. -/
theorem ae_tendsto_originBumpAverage {d : ℕ} {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), Tendsto
      (fun n => ((representativeBump d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] f) x) atTop (𝓝 (f x)) := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      (representativeBump d n).rOut ≤ (2 : ℝ) * (representativeBump d n).rIn := by
    filter_upwards with n
    dsimp only [representativeBump]
    linarith
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure (Vec d))) (φ := representativeBump d)
    tendsto_one_div_add_atTop_nhds_zero_nat hratio hf

/-- Covariance at each fixed shift, almost surely, holds for almost every shift
on one full-measure event. -/
theorem ae_ae_covariance_of_forall {d : ℕ} (Q : Measure (FieldPair d)) [SFinite Q]
    {G : FieldPair d → Vec d → ℝ}
    (hG : Measurable (fun p : FieldPair d × Vec d => G p.1 p.2))
    (hcov : ∀ z : Vec d, ∀ᵐ ρ ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      G (translate z ρ) x = G ρ (x + z)) :
    ∀ᵐ ρ ∂Q, ∀ᵐ z ∂(volume : Measure (Vec d)), ∀ᵐ x ∂(volume : Measure (Vec d)),
      G (translate z ρ) x = G ρ (x + z) := by
  let s : Set ((Vec d × FieldPair d) × Vec d) :=
    {q | G (translate q.1.1 q.1.2) q.2 = G q.1.2 (q.2 + q.1.1)}
  have hs : MeasurableSet s := by
    have h1 : Measurable (fun q : (Vec d × FieldPair d) × Vec d =>
        G (translate q.1.1 q.1.2) q.2) :=
      hG.comp ((Probability.continuous_translate.measurable.comp measurable_fst).prodMk
        measurable_snd)
    have h2 : Measurable (fun q : (Vec d × FieldPair d) × Vec d =>
        G q.1.2 (q.2 + q.1.1)) :=
      hG.comp ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.add (measurable_fst.comp measurable_fst)))
    exact measurableSet_eq_fun h1 h2
  have hset : MeasurableSet {q : Vec d × FieldPair d |
      ∀ᵐ x ∂(volume : Measure (Vec d)), G (translate q.1 q.2) x = G q.2 (x + q.1)} := by
    have hm := measurable_measure_prodMk_left (ν := (volume : Measure (Vec d))) hs.compl
    have heq : {q : Vec d × FieldPair d |
        ∀ᵐ x ∂(volume : Measure (Vec d)), G (translate q.1 q.2) x = G q.2 (x + q.1)} =
        (fun q => (volume : Measure (Vec d)) (Prod.mk q ⁻¹' sᶜ)) ⁻¹' {0} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, ae_iff]
      rfl
    rw [heq]
    exact hm (measurableSet_singleton 0)
  exact (Measure.ae_ae_comm (μ := (volume : Measure (Vec d))) (ν := Q) hset).mp
    (ae_of_all _ hcov)

/-- A jointly measurable, locally integrable family that is covariant under every
translation, almost surely for each shift, is the orbit of a measurable observable.
Source: the stationary gradient of AKM (6.7), `paper/main.tex:732-748`. -/
theorem ae_orbit_stationaryRepresentative {d : ℕ} (Q : Measure (FieldPair d)) [SFinite Q]
    {G : FieldPair d → Vec d → ℝ}
    (hG : Measurable (fun p : FieldPair d × Vec d => G p.1 p.2))
    (hloc : ∀ᵐ ρ ∂Q, LocallyIntegrable (G ρ) volume)
    (hcov : ∀ z : Vec d, ∀ᵐ ρ ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      G (translate z ρ) x = G ρ (x + z)) :
    ∀ᵐ ρ ∂Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      stationaryRepresentative G (translate x ρ) = G ρ x := by
  filter_upwards [hloc, ae_ae_covariance_of_forall Q hG hcov] with ρ hρ hcovρ
  filter_upwards [hcovρ, ae_tendsto_originBumpAverage hρ] with x hx hlim
  unfold stationaryRepresentative
  simp_rw [originBumpAverage_translate_eq x hx]
  exact hlim.limsup_eq

end EinsteinRelation.Correctors
