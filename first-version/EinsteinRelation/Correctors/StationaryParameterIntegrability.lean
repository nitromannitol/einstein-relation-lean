import EinsteinRelation.Correctors.StationaryParameterAverages

/-! # Integrability of stationary path averages

Source: `paper/main.tex:1021–1029`. Integrable weights and measurable
stationary displacements produce integrable joint orbit integrands.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- Joint integrability for a weighted measurable family of translations
(`paper/main.tex:1021–1029`). -/
theorem integrable_stationary_param {d : ℕ} {S : Type*} [MeasurableSpace S]
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure S) [SFinite ν] {T : S → Vec d} (hT : Measurable T)
    {a : S → ℝ} (ha : Measurable a) (hai : Integrable a ν)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hfi : Integrable f Q) :
    Integrable (fun q : FieldPair d × S => a q.2 * f (translate (T q.2) q.1))
      (Q.prod ν) := by
  have ht : Measurable (fun q : FieldPair d × S => translate (T q.2) q.1) :=
    Probability.continuous_translate.measurable.comp
      ((hT.comp measurable_snd).prodMk measurable_fst)
  have hm : Measurable (fun q : FieldPair d × S => a q.2 * f (translate (T q.2) q.1)) :=
    (ha.comp measurable_snd).mul (hf.comp ht)
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun z => ?_, ?_⟩
  · have hs : Integrable f (Measure.map (translate (T z)) Q) := by
      rw [hQ (T z)]
      exact hfi
    exact (hs.comp_measurable (Probability.measurable_translate (T z))).const_mul (a z)
  · have hn (z : S) : (∫ ω, ‖a z * f (translate (T z) ω)‖ ∂Q) =
        ‖a z‖ * ∫ ω, ‖f ω‖ ∂Q := by
      simp_rw [norm_mul]
      rw [integral_const_mul, Probability.integral_translate Q hQ (T z) _ hf.norm]
    simpa only [hn] using hai.norm.mul_const (∫ ω, ‖f ω‖ ∂Q)

end EinsteinRelation.Correctors
