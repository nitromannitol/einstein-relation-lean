import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpace
import EinsteinRelation.Correctors.StationaryGradientDomainSupport

/-! Spatial evaluation of stationary L² fields along the literal translation action. -/

open MeasureTheory

namespace EinsteinRelation.Correctors.StationarySpatialRealization

/-! A stationary L² field has a measurable spatial realization along the translation action.
This support does not construct a scalar potential or identify the realization as a
samplewise distributional gradient. -/

variable {d : ℕ}

/-- Evaluate an L² vector field along the literal translation action. -/
noncomputable def spatialRealization {Q : Measure (FieldPair d)}
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) : Vec d × FieldPair d → EuclideanSpace ℝ (Fin d) :=
  fun p => G (translate p.1 p.2)

theorem measurable_spatialRealization {Q : Measure (FieldPair d)}
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    Measurable (spatialRealization G) := by
  have hG : Measurable G := (Lp.stronglyMeasurable G).measurable
  exact hG.comp Probability.continuous_translate.measurable

private theorem map_spatialAction_prod {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (ν : Measure (Vec d))
    [IsFiniteMeasure ν] :
    Measure.map (fun p : Vec d × FieldPair d => translate p.1 p.2) (ν.prod Q) =
      ν Set.univ • Q := by
  let T : Vec d × FieldPair d → FieldPair d := fun p => translate p.1 p.2
  have hT : Measurable T := Probability.continuous_translate.measurable
  apply Measure.ext
  intro s hs
  have hsection : ∀ x : Vec d, Q {ω : FieldPair d | translate x ω ∈ s} = Q s := by
    intro x
    calc
      Q {ω : FieldPair d | translate x ω ∈ s} = Measure.map (translate x) Q s := by
        exact (Measure.map_apply (Probability.measurable_translate x) hs).symm
      _ = Q s := congrArg (fun μ : Measure (FieldPair d) => μ s) (hQ x)
  rw [Measure.map_apply hT hs, Measure.prod_apply (hT hs)]
  calc
    (∫⁻ x, Q {ω : FieldPair d | translate x ω ∈ s} ∂ν) =
        ∫⁻ _x, Q s ∂ν := by
          apply lintegral_congr
          intro x
          exact hsection x
    _ = ν Set.univ * Q s := by rw [lintegral_const, mul_comm]
    _ = (ν Set.univ • Q) s := by rw [Measure.smul_apply, smul_eq_mul]

/-- Changing the chosen measurable representative of an L² class does not change its spatial
realization almost everywhere on the space-time product. -/
theorem ae_spatialRealization_congr {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (ν : Measure (Vec d))
    [IsFiniteMeasure ν] {G H : Lp (EuclideanSpace ℝ (Fin d)) 2 Q}
    (hGH : G =ᵐ[Q] H) :
    spatialRealization G =ᵐ[ν.prod Q] spatialRealization H := by
  let T : Vec d × FieldPair d → FieldPair d := fun p => translate p.1 p.2
  have hT : AEMeasurable T (ν.prod Q) :=
    Probability.continuous_translate.measurable.aemeasurable
  have hset : MeasurableSet {ω : FieldPair d | G ω = H ω} :=
    measurableSet_eq_fun ((Lp.stronglyMeasurable G).measurable)
      ((Lp.stronglyMeasurable H).measurable)
  have hmapEq : Measure.map T (ν.prod Q) = ν Set.univ • Q := by
    simpa only [T] using map_spatialAction_prod hQ ν
  have hmap : ∀ᵐ ω ∂Measure.map T (ν.prod Q), G ω = H ω := by
    rw [hmapEq]
    rw [MeasureTheory.ae_iff, Measure.smul_apply, smul_eq_mul,
      MeasureTheory.ae_iff.mp hGH, mul_zero]
  have hcomp := (ae_map_iff hT hset).1 hmap
  simpa only [spatialRealization, T] using! hcomp

/-- Product-space L² control for the spatial realization. Stationarity identifies the pushforward
of spatial volume times the environment law with a scalar multiple of the environment law. -/
theorem memLp_spatialRealization_prod {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (ν : Measure (Vec d))
    [IsFiniteMeasure ν] (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    MemLp (spatialRealization G) 2 (ν.prod Q) := by
  have hG : Measurable G := (Lp.stronglyMeasurable G).measurable
  have hT : AEMeasurable (fun p : Vec d × FieldPair d => translate p.1 p.2) (ν.prod Q) :=
    Probability.continuous_translate.measurable.aemeasurable
  have hGmap : AEStronglyMeasurable G
      (Measure.map (fun p : Vec d × FieldPair d => translate p.1 p.2) (ν.prod Q)) :=
    hG.aestronglyMeasurable
  have hscaled : MemLp G 2 (ν Set.univ • Q) :=
    (Lp.memLp G).smul_measure (measure_ne_top ν Set.univ)
  have hmap : MemLp G 2
      (Measure.map (fun p : Vec d × FieldPair d => translate p.1 p.2) (ν.prod Q)) := by
    rw [map_spatialAction_prod hQ ν]
    exact hscaled
  have hcomp := (memLp_map_measure_iff hGmap hT).1 hmap
  simpa only [spatialRealization, Function.comp_apply] using! hcomp

/-- On any finite spatial measure, almost every environment section of the spatial realization
is locally square integrable. -/
theorem ae_spatialRealization_memLp_of_finite {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (ν : Measure (Vec d))
    [IsFiniteMeasure ν] (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    ∀ᵐ ω ∂Q, MemLp (fun x : Vec d => G (translate x ω)) 2 ν := by
  have hprod := memLp_spatialRealization_prod hQ ν G
  have hsq : Integrable (fun p : Vec d × FieldPair d =>
      ‖spatialRealization G p‖ ^ 2) (ν.prod Q) :=
    (memLp_two_iff_integrable_sq_norm hprod.aestronglyMeasurable).mp hprod
  have hsections := (integrable_prod_iff' hsq.aestronglyMeasurable).mp hsq
  filter_upwards [hsections.1] with ω hω
  have hmeas : AEStronglyMeasurable
      (fun x : Vec d => G (translate x ω)) ν := by
    exact ((measurable_spatialRealization G).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  change Integrable (fun x : Vec d => ‖G (translate x ω)‖ ^ 2) ν at hω
  exact hω

/-- Local square integrability on one common full-measure set for the countable closed-ball
exhaustion of Euclidean space. Every compact region is contained in one of these balls. -/
theorem ae_spatialRealization_locallyL2 {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    ∀ᵐ ω ∂Q, ∀ n : ℕ,
      MemLp (fun x : Vec d => G (translate x ω)) 2
        (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1))) := by
  apply ae_all_iff.2
  intro n
  let K : Set (Vec d) := Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)
  have hK : volume K ≠ ⊤ := (isCompact_closedBall (0 : Vec d) _).measure_ne_top
  letI : IsFiniteMeasure (volume.restrict K) := (isFiniteMeasure_restrict).2 hK
  simpa only [K] using ae_spatialRealization_memLp_of_finite hQ (volume.restrict K) G

/-- One common full-measure set works for every compact spatial region: each compact lies in
some member of the countable closed-ball exhaustion, and restriction decreases the measure. -/
theorem ae_spatialRealization_memLp_on_all_compacts {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    ∀ᵐ ω ∂Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x : Vec d => G (translate x ω)) 2 (volume.restrict K) := by
  filter_upwards [ae_spatialRealization_locallyL2 hQ G] with ω hω
  intro K hK
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hK.isBounded
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hrad : R ≤ (n : ℝ) + 1 := le_trans hn.le (by norm_num)
  have hsubset : K ⊆ Metric.closedBall (0 : Vec d) ((n : ℝ) + 1) :=
    hR.trans (Metric.closedBall_subset_closedBall hrad)
  exact (hω n).mono_measure (Measure.restrict_mono_set volume hsubset)

end EinsteinRelation.Correctors.StationarySpatialRealization
