import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Map
/-! # Transport of endpoint Radon–Nikodym weights

Source `paper/main.tex:377–390`. Reweighting a killed path law by its
endpoint density commutes with invertible measurable coordinate changes.
-/

open MeasureTheory

namespace EinsteinRelation.Probability

/-- Reweighting by an endpoint density commutes with a measurable change of coordinates. -/
theorem map_endpoint_rnDeriv {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (e : α ≃ᵐ β) (j : γ ≃ᵐ δ) (f : α → γ) (g : β → δ)
    (hf : Measurable f) (hg : Measurable g) (hcomm : ∀ a, g (e a) = j (f a))
    (μ : Measure α) [IsFiniteMeasure μ] (ν : Measure γ) [IsFiniteMeasure ν] :
    Measure.map e (μ.withDensity (fun a => ν.rnDeriv (Measure.map f μ) (f a))) =
      (Measure.map e μ).withDensity (fun b =>
        (Measure.map j ν).rnDeriv (Measure.map g (Measure.map e μ)) (g b)) := by
  set μ_f := Measure.map f μ
  set ν_j := Measure.map j ν
  have h_comm_fg : g ∘ e = j ∘ f := by
    ext a; exact hcomm a
  have h_map_comp : Measure.map g (Measure.map e μ) = Measure.map j μ_f := by
    calc
      Measure.map g (Measure.map e μ) = Measure.map (g ∘ e) μ := by
        rw [Measure.map_map hg e.measurable]
      _ = Measure.map (j ∘ f) μ := by rw [h_comm_fg]
      _ = Measure.map j (Measure.map f μ) := by rw [Measure.map_map j.measurable hf]
      _ = Measure.map j μ_f := rfl
  rw [h_map_comp]
  have h_ae_eq : ∀ᵐ a ∂μ,
      ν_j.rnDeriv (Measure.map j μ_f) (j (f a)) = ν.rnDeriv μ_f (f a) := by
    have h_rnDeriv := j.measurableEmbedding.rnDeriv_map ν μ_f
    have h_ae_map := ae_of_ae_map hf.aemeasurable h_rnDeriv
    simpa [Function.comp, μ_f, ν_j] using h_ae_map
  ext s hs
  rw [Measure.map_apply e.measurable hs]
  have h_meas_rnDeriv_j : Measurable (ν_j.rnDeriv (Measure.map j μ_f)) :=
    Measure.measurable_rnDeriv _ _
  rw [withDensity_apply _ (hs.preimage e.measurable), withDensity_apply _ hs]
  -- Target: ∫⁻ a in e⁻¹' s, ν.rnDeriv μ_f (f a) ∂μ = ∫⁻ a in s, ν_j.rnDeriv (Measure.map j μ_f) (g a) ∂Measure.map e μ
  have h_map : ∫⁻ a in s, ν_j.rnDeriv (Measure.map j μ_f) (g a) ∂Measure.map e μ =
      ∫⁻ x in e ⁻¹' s, ν_j.rnDeriv (Measure.map j μ_f) (g (e x)) ∂μ := by
    simpa [Function.comp_apply] using
      setLIntegral_map (f := ν_j.rnDeriv (Measure.map j μ_f) ∘ g) (g := e) (s := s)
        hs (h_meas_rnDeriv_j.comp hg) e.measurable (μ := μ)
  rw [h_map]
  simp_rw [hcomm]
  have h_ae_eq_on : ∀ᵐ a ∂μ, a ∈ e ⁻¹' s →
      ν.rnDeriv μ_f (f a) = ν_j.rnDeriv (Measure.map j μ_f) (j (f a)) := by
    filter_upwards [h_ae_eq] with a ha _
    exact ha.symm
  rw [setLIntegral_congr_fun_ae (hs.preimage e.measurable) h_ae_eq_on]

end EinsteinRelation.Probability
