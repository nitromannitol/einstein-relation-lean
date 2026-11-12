import EinsteinRelation.Correctors.StochasticGradientTailMembership

/-! # Finite gradient increments controlled by the sharp tail

Source: `paper/main.tex:800–808`. Truncating the literal gradient at an
upper endpoint preserves its local RMS bound. The resulting finite time
integral is a genuine spatial L2 field with the same tail estimate.
-/

open MeasureTheory Set
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- A sharp local gradient moment bound controls every truncated tail,
including its actual spatial L2 membership.
Source: `paper/main.tex:800–808`. -/
theorem truncated_gradient_tail_moment
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ν : Measure X) [SigmaFinite ν]
    (G : Ω × (ℝ × X) → EuclideanSpace ℝ (Fin d)) (hG : Measurable G)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {C α T : ℝ} (hC : 0 < C) (hα : 0 < α) (hT : 0 < T)
    (hsections : ∀ᵐ ω ∂Q, ∀ᵐ t ∂volume.restrict (Ioi T),
      MemLp (fun x => G (ω,(t,x))) 2 ν)
    (hdecay : ∀ᵐ t ∂volume.restrict (Ioi T),
      eLpNorm (fun ω => Real.sqrt (∫ x, ‖G (ω,(t,x))‖^2 ∂ν)) p Q ≤
        ENNReal.ofReal (C*t^(-1-α))) (S : ℝ) :
    (∀ᵐ ω ∂Q, MemLp (fun x => ∫ t in Ioo T S, G (ω,(t,x))) 2 ν) ∧
    MemLp (fun ω => Real.sqrt (∫ x, ‖∫ t in Ioo T S, G (ω,(t,x))‖^2 ∂ν)) p Q ∧
    eLpNorm (fun ω => Real.sqrt (∫ x, ‖∫ t in Ioo T S, G (ω,(t,x))‖^2 ∂ν)) p Q ≤
      ENNReal.ofReal ((C/α)*T^(-α)) := by
  classical
  let H : Ω × (ℝ × X) → EuclideanSpace ℝ (Fin d) :=
    {z : Ω × (ℝ × X) | z.2.1 < S}.indicator G
  have hH : Measurable H := hG.indicator (measurableSet_lt measurable_snd.fst measurable_const)
  have hs : ∀ᵐ ω ∂Q, ∀ᵐ t ∂volume.restrict (Ioi T),
      MemLp (fun x => H (ω,(t,x))) 2 ν := by
    filter_upwards [hsections] with ω hω
    filter_upwards [hω] with t ht
    by_cases htS : t < S
    · simpa [H, htS] using ht
    · simp [H, htS]
  have hb : ∀ᵐ t ∂volume.restrict (Ioi T),
      eLpNorm (fun ω => Real.sqrt (∫ x, ‖H (ω,(t,x))‖^2 ∂ν)) p Q ≤
        ENNReal.ofReal (C*t^(-1-α)) := by
    filter_upwards [hdecay] with t ht
    by_cases htS : t < S
    · simpa [H, htS] using ht
    · simp [H, htS]
  have he (ω : Ω) (x : X) :
      (∫ t in Ioi T, H (ω,(t,x))) = ∫ t in Ioo T S, G (ω,(t,x)) := by
    change (∫ t in Ioi T, (Iio S).indicator (fun t => G (ω,(t,x))) t) = _
    rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    rw [show Iio S ∩ Ioi T = Ioo T S by ext t; exact and_comm]
  have htail := stochastic_local_gradient_tail_moment_le_ae Q ν H hH
    hp hpt hC hα hT hs hb
  have hmem := stochastic_local_gradient_tail_spatial_memLp_ae Q ν H hH
    hp hpt hC hα hT hs hb
  simpa only [he] using And.intro hmem htail.2

end EinsteinRelation.Correctors
