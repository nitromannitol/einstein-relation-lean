import EinsteinRelation.Correctors.CorrectorConditionalStatement
import EinsteinRelation.Correctors.SpatialCovarianceCongruence
import EinsteinRelation.Correctors.StationaryOrbitEquality
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Identifying continuous versions of the canonical gradient

Source: `paper/main.tex:860–875`. Spatial almost-everywhere identification
with a stationary orbit determines a continuous version at each fixed point,
almost surely in the environment. Covariance of that version is derived;
no point evaluation of a spatial null set or uniqueness premise is used.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport

/-- A continuous version of a stationary orbit inherits pointwise spatial
covariance for each fixed translation. Source: `paper/main.tex:860–875`. -/
theorem ae_continuous_orbit_version_covariance {d : ℕ}
    (P : Measure (FieldPair d)) (hP : IsStationary P)
    (F : FieldPair d → Vec d) (g : FieldPair d → Vec d → Vec d)
    (hc : ∀ᵐ ω ∂P, Continuous (g ω))
    (hid : ∀ᵐ ω ∂P, g ω =ᵐ[volume] fun x => F (translate x ω))
    (y : Vec d) :
    ∀ᵐ ω ∂P, ∀ x, g ω (x + y) = g (translate y ω) x := by
  have hmp : MeasurePreserving (translate y) P P :=
    ⟨Probability.measurable_translate y, hP y⟩
  have hcov := ae_spatial_covariance_congr P (translate y) hmp y g
    (fun ω x => F (translate x ω)) hid (Filter.Eventually.of_forall fun ω =>
      Filter.Eventually.of_forall fun x => by
        change F (translate (x + y) ω) = F (translate x (translate y ω))
        rw [translate_add])
  filter_upwards [hcov, hc, hmp.quasiMeasurePreserving.ae hc] with ω hω hcω hcy
  exact congrFun (Measure.eq_of_ae_eq hω
    (hcω.comp (continuous_id.add continuous_const)) hcy)

/-- Joint measurability and spatial continuity identify every prescribed
point of an a.e. version with the canonical stationary gradient. The
almost-sure event may depend on the prescribed point.
Source: `paper/main.tex:860–875`. -/
theorem ae_continuous_version_eq_conditionalCorrectorGradient
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (g : FieldPair d → Vec d → Vec d)
    (hm : Measurable (fun z : FieldPair d × Vec d => g z.1 z.2))
    (hc : ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (g ω))
    (hid : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      g ω =ᵐ[volume] fun x => conditionalCorrectorGradient Q i (WithLp.toLp 2 x) ω)
    (y : Point d) :
    (fun ω => g ω y.ofLp) =ᵐ[reducedEnvironmentLaw Q]
      conditionalCorrectorGradient Q i y := by
  let P := reducedEnvironmentLaw Q
  let F : FieldPair d → Vec d := conditionalCorrectorGradient Q i 0
  have hFm : Measurable F := by
    exact (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
      ((Lp.stronglyMeasurable (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 P)).measurable.comp
          (Probability.measurable_translate 0))
  have hid' : ∀ᵐ ω ∂P, g ω =ᵐ[volume] fun x => F (translate x ω) := by
    simpa only [F, conditionalCorrectorGradient,
      StationarySpatialRealization.spatialRealization, WithLp.ofLp_toLp,
      WithLp.ofLp_zero, translate_zero] using hid
  have hpoint (x : Vec d) : ∀ᵐ ω ∂P, g ω x = g (translate x ω) 0 := by
    filter_upwards [ae_continuous_orbit_version_covariance P
      (reducedEnvironmentLaw_stationary Q) F g hc hid' x] with ω hω
    simpa only [zero_add] using hω 0
  have hjoint : MeasurableSet {z : FieldPair d × Vec d |
      g z.1 z.2 = g (translate z.2 z.1) 0} :=
    measurableSet_eq_fun hm (hm.comp
      ((Probability.continuous_translate.measurable.comp measurable_swap).prodMk
        measurable_const))
  have hsp : ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      g (translate x ω) 0 = F (translate x ω) := by
    have hx := (Measure.ae_ae_comm (μ := P) (ν := (volume : Measure (Vec d))) hjoint).mpr
      (Filter.Eventually.of_forall hpoint)
    filter_upwards [hx, hid'] with ω hxω hiω
    filter_upwards [hxω, hiω] with x hx hi
    exact hx.symm.trans hi
  have hzero : (fun ω => g ω 0) =ᵐ[P] F := by
    have hcoords (j : Fin d) : (fun ω => g ω 0 j) =ᵐ[P] fun ω => F ω j :=
      ae_eq_of_ae_spatial_orbit_eq P (reducedEnvironmentLaw_stationary Q)
        (((measurable_pi_apply j).comp (hm.comp (measurable_id.prodMk
          measurable_const))).aestronglyMeasurable)
        (((measurable_pi_apply j).comp hFm).aestronglyMeasurable)
        (hsp.mono fun ω hω => hω.mono fun x hx => congrFun hx j)
    filter_upwards [ae_all_iff.mpr hcoords] with ω hω
    exact funext hω
  have hmp : MeasurePreserving (translate y.ofLp) P P :=
    ⟨Probability.measurable_translate _, reducedEnvironmentLaw_stationary Q _⟩
  filter_upwards [hpoint y.ofLp, hmp.quasiMeasurePreserving.ae hzero] with ω hp hz
  exact hp.trans (by simpa only [F, conditionalCorrectorGradient,
    StationarySpatialRealization.spatialRealization, WithLp.ofLp_zero,
    translate_zero] using hz)

end EinsteinRelation.Correctors
