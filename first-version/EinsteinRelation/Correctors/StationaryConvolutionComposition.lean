import EinsteinRelation.Correctors.StationaryKernelConvolution
import Mathlib.MeasureTheory.Group.Prod

/-! # Composition of orbit convolutions

Source: `paper/main.tex:1030–1032`. Fubini's theorem applies to the
actual stationary translation orbits, including unbounded integrable fields.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- Integrability of a weighted family of stationary translates, for an
arbitrary measurable parameter space (`paper/main.tex:1030–1032`). -/
theorem integrable_weighted_translate {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] {a : α → ℝ} (ha : Measurable a)
    (hai : Integrable a ν) {v : α → Vec d} (hv : Measurable v)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) :
    Integrable (fun q : FieldPair d × α => a q.2 * f (translate (v q.2) q.1))
      (Q.prod ν) := by
  have ht : Measurable (fun q : FieldPair d × α => translate (v q.2) q.1) :=
    Probability.continuous_translate.measurable.comp
      ((hv.comp measurable_snd).prodMk measurable_fst)
  have hm : Measurable (fun q : FieldPair d × α =>
      a q.2 * f (translate (v q.2) q.1)) := (ha.comp measurable_snd).mul (hf.comp ht)
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun z => ?_, ?_⟩
  · have hshift : Integrable f (Measure.map (translate (v z)) Q) := by
      rw [hQ (v z)]
      exact hfi
    exact (hshift.comp_measurable (Probability.measurable_translate (v z))).const_mul (a z)
  · have hnorm (z : α) : (∫ ω, ‖a z * f (translate (v z) ω)‖ ∂Q) =
        ‖a z‖ * ∫ ω, ‖f ω‖ ∂Q := by
      simp_rw [norm_mul]
      rw [integral_const_mul, Probability.integral_translate Q hQ (v z) _ hf.norm]
    simpa only [hnorm] using hai.norm.mul_const (∫ ω, ‖f ω‖ ∂Q)

/-- Two integrable kernels compose by their spatial convolution on almost
every actual orbit (`paper/main.tex:1030–1032`). -/
theorem horizontalMollify_convolution_ae {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {K L : Vec d → ℝ}
    (hK : Measurable K) (hKi : Integrable K volume)
    (hL : Measurable L) (hLi : Integrable L volume)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) :
    horizontalMollify (fun x => ∫ z, K z * L (x - z)) f =ᵐ[Q]
      horizontalMollify K (horizontalMollify L f) := by
  have hi := integrable_weighted_translate hQ (volume.prod volume)
    ((hK.comp measurable_fst).mul (hL.comp measurable_snd)) (hKi.mul_prod hLi)
    (measurable_fst.add measurable_snd) hf hfi
  filter_upwards [hi.prod_right_ae] with ω hω
  have hshear := (measurePreserving_prod_sub (volume : Measure (Vec d)) volume).integrable_comp_of_integrable hω
  have hH : Integrable (fun q : Vec d × Vec d =>
      K q.1 * L (q.2 - q.1) * f (translate q.2 ω)) (volume.prod volume) := by
    convert hshear using 1
    ext q
    dsimp only [Function.comp_def]
    rw [show q.1 + (q.2 - q.1) = q.2 by abel]
  change (∫ x, (∫ z, K z * L (x - z)) * f (translate x ω)) =
    ∫ z, K z * ∫ y, L y * f (translate y (translate z ω))
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (f := fun z x => K z * L (x - z) * f (translate x ω)) hH]
  apply integral_congr_ae
  refine ae_of_all _ fun z => ?_
  dsimp only
  rw [← integral_const_mul]
  have hc := integral_add_left_eq_self (μ := volume)
    (f := fun x : Vec d => K z * L (x - z) * f (translate x ω)) z
  rw [← hc]
  apply integral_congr_ae
  refine ae_of_all _ fun y => ?_
  dsimp only
  rw [add_sub_cancel_left, translate_add, add_comm z y]
  ring

end EinsteinRelation.Correctors
