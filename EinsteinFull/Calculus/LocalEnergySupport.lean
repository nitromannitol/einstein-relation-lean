import EinsteinFull.Frozen.LocalSpatialEnergy
import EinsteinFull.Frozen.ReducedLawProbability
import EinsteinFull.Frozen.ReducedLawStationary
import EinsteinRelation.Probability.LocalSigma
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- Finite spatial windows of any integrable stationary observable are integrable
for almost every environment. This is a Fubini fact, with no diffusion estimate. -/
theorem ae_integrableOn_stationary_orbit {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {u : FieldPair d → ℝ}
    (hum : Measurable u) (hui : Integrable u Q)
    {S : Set (Vec d)} (hSf : volume S ≠ ⊤) :
    ∀ᵐ ω ∂Q, IntegrableOn (fun x => u (translate x ω)) S := by
  haveI : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hSf
  have hFm : Measurable (fun p : FieldPair d × Vec d => u (translate p.2 p.1)) :=
    hum.comp (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_fst))
  have hFint : Integrable (fun p : FieldPair d × Vec d => u (translate p.2 p.1))
      (Q.prod (volume.restrict S)) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · have h : Integrable u (Measure.map (translate x) Q) := by
        rw [hQ x]
        exact hui
      exact h.comp_measurable (Probability.measurable_translate x)
    · refine Integrable.congr (integrable_const (∫ ω, ‖u ω‖ ∂Q))
        (Filter.Eventually.of_forall fun x => ?_)
      exact (Probability.integral_translate Q hQ x (fun η => ‖u η‖) hum.norm).symm
  exact hFint.prod_right_ae

/-- The actual local-energy integrand has a genuine finite spatial integral
on any finite-volume window, almost surely. -/
theorem ae_integrableOn_localSpatialEnergy_integrand {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (t : ℝ)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q))
    {S : Set (Vec d)} (hSf : volume S ≠ ⊤) :
    ∀ᵐ ω ∂reducedLaw Q, IntegrableOn (fun y : Vec d =>
      (∑ j : Fin d, ‖G j (translate y ω)‖ ^ 2) + t * ‖V (translate y ω)‖ ^ 2) S := by
  letI := reducedLaw_probability Q
  apply ae_integrableOn_stationary_orbit (reducedLaw_stationary Q)
    (u := fun η => (∑ j : Fin d, ‖G j η‖ ^ 2) + t * ‖V η‖ ^ 2) _ _ hSf
  · exact (Finset.measurable_sum _ fun j _ => (Lp.stronglyMeasurable (G j)).measurable.norm.pow_const 2).add
      (measurable_const.mul ((Lp.stronglyMeasurable V).measurable.norm.pow_const 2))
  · exact (integrable_finset_sum _ fun j _ =>
      (Lp.memLp (G j)).integrable_norm_pow (by norm_num)).add
        (((Lp.memLp V).integrable_norm_pow (by norm_num)).const_mul t)

/-- Equal measurable representatives remain equal on spatial orbits for almost
all environments, with the spatial null set allowed to depend on the environment. -/
theorem ae_ae_stationary_orbit_eq {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {u v : FieldPair d → ℝ}
    (hu : Measurable u) (hv : Measurable v) (huv : u =ᵐ[Q] v) :
    ∀ᵐ ω ∂Q, ∀ᵐ x : Vec d ∂volume, u (translate x ω) = v (translate x ω) := by
  have hm : Measurable (fun p : Vec d × FieldPair d => translate p.1 p.2) :=
    Probability.continuous_translate.measurable
  have hmeq : MeasurableSet {p : Vec d × FieldPair d |
      u (translate p.1 p.2) = v (translate p.1 p.2)} :=
    measurableSet_eq_fun (hu.comp hm) (hv.comp hm)
  apply (Measure.ae_ae_comm (μ := volume) (ν := Q)
    (p := fun x ω => u (translate x ω) = v (translate x ω)) hmeq).mp
  apply Filter.Eventually.of_forall
  intro x
  apply ae_of_ae_map (μ := Q) (p := fun η => u η = v η)
    (Probability.measurable_translate x).aemeasurable
  rwa [hQ x]

/-- Spatial integrals of stationary observables do not depend on their a.e.
representatives. No integrability assumption is used to assert equality. -/
theorem ae_setIntegral_stationary_orbit_congr {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {u v : FieldPair d → ℝ}
    (hu : Measurable u) (hv : Measurable v) (huv : u =ᵐ[Q] v) (S : Set (Vec d)) :
    ∀ᵐ ω ∂Q, (∫ x in S, u (translate x ω)) = ∫ x in S, v (translate x ω) := by
  filter_upwards [ae_ae_stationary_orbit_eq hQ hu hv huv] with ω hω
  exact integral_congr_ae (ae_restrict_of_ae hω)

end EinsteinFull
