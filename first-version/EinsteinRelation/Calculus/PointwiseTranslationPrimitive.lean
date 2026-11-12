import EinsteinRelation.Calculus.HorizontalTranslationPrimitive
import EinsteinRelation.Calculus.L2IntervalRepresentatives
import EinsteinRelation.Correctors.StationaryParameterIntegrability
import EinsteinRelation.Entropy.DivergenceSecondAssertion
import EinsteinRelation.Entropy.WeakResolventFromDynkin

/-! # Samplewise translation primitives

Source: `paper/main.tex:1021–1029`.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation

/-- The literal segment primitive has the full weak endpoint divergence
(`paper/main.tex:1021–1029`). -/
theorem hasWeakHorizontalDivergence_pointwise_translationPrimitive
    {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (i : Fin d) (b : ℝ)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 Q) :
    HasWeakHorizontalDivergence Q hQ
      (fun ω => Pi.single i (∫ t in (0 : ℝ)..b, f (translate (t • unitVector i) ω)))
      (fun ω => f (translate (b • unitVector i) ω) - f ω) := by
  classical
  let X : Lp ℝ 2 Q := hf2.toLp f
  have hX : (X : FieldPair d → ℝ) =ᵐ[Q] f := hf2.coeFn_toLp
  let G : ℝ → Lp ℝ 2 Q := fun t => translationLp Q hQ (t • unitVector i) X
  have hG : Continuous G := (continuous_translationLp Q hQ).comp
    ((continuous_id.smul continuous_const).prodMk continuous_const)
  have he (t : ℝ) : (G t : FieldPair d → ℝ) =ᵐ[Q]
      fun ω => f (translate (t • unitVector i) ω) := by
    filter_upwards [coeFn_translationLp Q hQ (t • unitVector i) X,
      (measurePreserving_translate Q hQ (t • unitVector i)).quasiMeasurePreserving.ae hX]
      with ω hω hfω
    exact hω.trans hfω
  let ν : Measure ℝ := volume.restrict (Set.uIoc (0 : ℝ) b)
  haveI : IsFiniteMeasure ν := by
    change IsFiniteMeasure (volume.restrict (Set.Ioc (min 0 b) (max 0 b)))
    infer_instance
  have hF : Integrable (fun q : ℝ × FieldPair d => f (translate (q.1 • unitVector i) q.2))
      (ν.prod Q) := by
    have hi := Correctors.integrable_stationary_param hQ ν
      (measurable_id.smul_const (unitVector i)) measurable_const
      (integrable_const (1 : ℝ)) hf (hf2.integrable one_le_two)
    simpa only [one_mul] using hi.swap
  have hY := ae_coe_L2_intervalIntegral (hG.intervalIntegrable 0 b) hF (ae_of_all _ he)
  have hw := hasWeakHorizontalDivergence_translationPrimitive hQ i b X
  have hw' := hw.congr_field (hY.mono fun ω hω => congrArg (Pi.single i) hω)
  apply Entropy.HasWeakHorizontalDivergence.congr_div hw'
  filter_upwards [he b, hX] with ω hb hω
  exact congrArg₂ (fun x y : ℝ => x - y) hb hω

theorem hasWeakHorizontalDivergence_literal_translationPrimitive
    {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (i : Fin d) (b : ℝ)
    {f : FieldPair d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 Q) :
    HasWeakHorizontalDivergence Q hQ
      (fun ω => Pi.single i (∫ t in (0 : ℝ)..b, f (translate (t • unitVector i) ω)))
      (fun ω => f (translate (b • unitVector i) ω) - f ω) := by
  exact hasWeakHorizontalDivergence_pointwise_translationPrimitive hQ i b hf hf2

end EinsteinRelation
