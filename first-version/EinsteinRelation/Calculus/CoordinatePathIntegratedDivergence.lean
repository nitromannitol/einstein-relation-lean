import EinsteinRelation.Calculus.CoordinatePathWeakDivergence
import EinsteinRelation.Calculus.CoordinatePathIntegrability
import EinsteinRelation.Calculus.IntegratedWeakDivergence

/-! # Averaging the coordinate path divergence

Source: `paper/main.tex:1021–1029`. Joint integrability makes the actual
path primitive compatible with the full horizontal test domain.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation

/-- Probability averaging of literal path fluxes preserves their endpoint
source (`paper/main.tex:1021–1029`). -/
theorem hasWeakHorizontalDivergence_coordinatePath_integral
    {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {f : FieldPair d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 Q)
    (hi : ∀ i : Fin d, Integrable (fun z : Vec d => |z i|) ν) :
    HasWeakHorizontalDivergence Q hQ
      (fun ω i => ∫ z, coordinatePathFlux f z ω i ∂ν)
      (fun ω => (∫ z, f (translate z ω) ∂ν) - f ω) := by
  have hfi := hf2.integrable one_le_two
  have ht := Correctors.integrable_stationary_param hQ ν measurable_id measurable_const
    (integrable_const (1 : ℝ)) hf hfi
  have hti : Integrable (fun q : Vec d × FieldPair d => f (translate q.1 q.2))
      (ν.prod Q) := by simpa only [one_mul] using ht.swap
  have h := hasWeakHorizontalDivergence_parameter_integral hQ ν
    (fun i => integrable_coordinatePathFlux_joint hQ ν hf hf2 i (hi i))
    (hti.sub (hfi.comp_snd ν))
    (ae_of_all _ (hasWeakHorizontalDivergence_coordinatePathFlux hQ hf hf2))
  apply Entropy.HasWeakHorizontalDivergence.congr_div h
  filter_upwards [hti.swap.prod_right_ae] with ω hω
  change Integrable (fun z => f (translate z ω)) ν at hω
  rw [integral_sub hω (integrable_const (f ω))]
  simp

end EinsteinRelation
