import EinsteinRelation.Regeneration.OneIntervalBridgeSupport
import EinsteinRelation.Regeneration.SpatialRecenterEquiv
import EinsteinRelation.Probability.EquivDensityTransport
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration

/-- Source `paper/main.tex:406–408`: the actual killed bridge mixture commutes with spatial translation, including its endpoint Radon--Nikodym reweighting. -/
theorem map_recenter_killedBridgeMixture {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (hR : 0 < R) (i : Fin d)
    (P P' : QuenchedPathLaws d) (a x : Vec d) (ω ω' : FieldPair d)
    [IsProbabilityMeasure (P (a + x, ω))]
    [IsProbabilityMeasure (P' (x, ω'))]
    (heq : (P (a + x, ω)).map (recenterPathEquiv a) = P' (x, ω')) :
    (Renewal.killedBridgeMixture Δ R i P (a + x) ω).map (recenterPathEquiv a) =
      Renewal.killedBridgeMixture Δ R i P' x ω' := by
  let p := recenterPathEquiv a
  let q : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight (-a)
  let ev : Path d → Vec d := fun γ => γ Δ
  have hev : Measurable ev := (continuous_eval_const Δ).measurable
  let μ := Renewal.killedSegmentLaw Δ R i P (a + x) ω
  let ν := Renewal.killedSegmentLaw Δ R i P' x ω'
  let η := cond (volume : Measure (Vec d)) (endpointBall i R (a + x))
  let η' := cond (volume : Measure (Vec d)) (endpointBall i R x)
  haveI : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure
    ((P (a + x, ω)).restrict _))
  have hset : p ⁻¹' {γ : Path d | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R x} =
      {γ : Path d | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R (a + x)} := by
    ext γ
    change (∀ t : ℝ≥0, t ≤ Δ → euclideanNorm (γ t - a - (x + (5 * R) • unitVector i)) < 6 * R) ↔ _
    have ha : ∀ t, γ t - a - (x + (5 * R) • unitVector i) =
        γ t - (a + x + (5 * R) • unitVector i) := by intro t; abel
    simp only [ha]
    rfl
  have hk : μ.map p = ν := by
    dsimp [μ, ν, Renewal.killedSegmentLaw]
    rw [← heq, p.restrict_map, hset]
  have hv : (volume : Measure (Vec d)).map q = volume :=
    (measurePreserving_add_right volume (-a)).map_eq
  have hB : q ⁻¹' endpointBall i R x = endpointBall i R (a + x) := by
    ext y
    change (euclideanNorm (y + -a - (x + (9 * R) • unitVector i)) < R) ↔ _
    have ha : y + -a - (x + (9 * R) • unitVector i) =
        y - (a + x + (9 * R) • unitVector i) := by abel
    rw [ha]
    rfl
  have hη : η.map q = η' := by
    have hmass : (volume : Measure (Vec d)) (endpointBall i R (a + x)) =
        volume (endpointBall i R x) := by
      rw [← hB, ← q.measurableEmbedding.map_apply, hv]
    dsimp [η, η', ProbabilityTheory.cond]
    rw [Measure.map_smul, hmass, ← hB, ← q.restrict_map, hv]
  have hend : (μ.map ev).map q = ν.map ev := by
    rw [← hk, Measure.map_map hev p.measurable, Measure.map_map q.measurable hev]
    rfl
  have hrn := q.measurableEmbedding.rnDeriv_map η (μ.map ev)
  rw [hη, hend] at hrn
  have hpath := ae_of_ae_map hev.aemeasurable hrn
  have hweight : (fun γ : Path d => (η'.rnDeriv (ν.map ev)) (ev (p γ))) =ᵐ[μ]
      (fun γ => (η.rnDeriv (μ.map ev)) (ev γ)) := by
    simpa only [ev, p, q, recenterPathEquiv, MeasurableEquiv.coe_addRight,
      ContinuousMap.coe_mk, sub_eq_add_neg] using hpath
  change (μ.withDensity (fun γ => (η.rnDeriv (μ.map ev)) (ev γ))).map p =
    ν.withDensity (fun γ => (η'.rnDeriv (ν.map ev)) (ev γ))
  rw [withDensity_congr_ae hweight.symm]
  have ht := Probability.map_withDensity_equiv p μ
    (fun γ => (η'.rnDeriv (ν.map ev)) (ev (p γ)))
    ((Measure.measurable_rnDeriv _ _).comp (hev.comp p.measurable))
  simpa only [p.apply_symm_apply, hk] using ht

end EinsteinRelation.Regeneration
