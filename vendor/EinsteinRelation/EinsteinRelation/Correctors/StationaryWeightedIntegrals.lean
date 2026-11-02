import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelation.External.AKMEnergyDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Stationary spatial integrals and the corrector flux cell

Source: `paper/main.tex:693-698,727-729`; AKM Remark 3.18, (3.93),
p. 101. For a continuously stationary law, an integrable spatial weight
times a stationary integrable observable is integrable on the product.
In particular every volume-one cell gives the same expected canonical
flux. This supplies the cell-change calculation for the actual continuum
law, without asserting it for an arbitrary lattice-stationary corrector.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Stationarity gives product integrability for every integrable scalar
weight, including after a measurable spatial rescaling. -/
theorem integrable_weighted_stationary_prod
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [SFinite ν]
    {F : FieldPair d → E} (hF : Measurable F) (hFi : Integrable F Q)
    {w : Vec d → ℝ} (hw : Measurable w) (hwi : Integrable w ν)
    {σ : Vec d → Vec d} (hσ : Measurable σ) :
    Integrable (fun p : Vec d × FieldPair d => w p.1 • F (translate (σ p.1) p.2))
      (ν.prod Q) := by
  have hm : Measurable
      (fun p : Vec d × FieldPair d => w p.1 • F (translate (σ p.1) p.2)) :=
    (hw.comp measurable_fst).smul
      (hF.comp (Probability.continuous_translate.measurable.comp
        ((hσ.comp measurable_fst).prodMk measurable_snd)))
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun x =>
    ((measurePreserving_translate Q hQ (σ x)).integrable_comp_of_integrable hFi).smul
      (w x), ?_⟩
  have heq (x : Vec d) :
      (∫ ω, ‖w x • F (translate (σ x) ω)‖ ∂Q) = |w x| * ∫ ω, ‖F ω‖ ∂Q := by
    simp_rw [norm_smul, Real.norm_eq_abs]
    rw [integral_const_mul, Probability.integral_translate Q hQ (σ x) _ hF.norm]
  simp_rw [heq]
  exact hwi.abs.mul_const _

/-- The environment expectation of a weighted spatial integral factors
into the mass of the weight and the expectation of the observable. -/
theorem integral_weighted_stationary [CompleteSpace E]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [SFinite ν]
    {F : FieldPair d → E} (hF : Measurable F) (hFi : Integrable F Q)
    {w : Vec d → ℝ} (hw : Measurable w) (hwi : Integrable w ν)
    {σ : Vec d → Vec d} (hσ : Measurable σ) :
    (∫ ω, ∫ x, w x • F (translate (σ x) ω) ∂ν ∂Q) =
      (∫ x, w x ∂ν) • ∫ ω, F ω ∂Q := by
  rw [← integral_integral_swap (integrable_weighted_stationary_prod Q hQ ν hF hFi hw hwi hσ)]
  have ht (x : Vec d) : (∫ ω, F (translate (σ x) ω) ∂Q) = ∫ ω, F ω ∂Q := by
    have h := integral_map (μ := Q) (Probability.measurable_translate (σ x)).aemeasurable
      hF.aestronglyMeasurable
    rw [hQ (σ x)] at h
    exact h.symm
  simp_rw [integral_smul, ht]
  exact integral_smul_const _ _

/-- The spatial integral of a stationary integrable observable over a
finite measurable region is itself integrable in the environment. -/
theorem integrable_stationary_setIntegral
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {F : FieldPair d → E} (hF : Measurable F) (hFi : Integrable F Q)
    {S : Set (Vec d)} (hSf : volume S ≠ ⊤) :
    Integrable (fun ω => ∫ x in S, F (translate x ω) ∂volume) Q := by
  letI : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hSf.lt_top⟩
  have h := integrable_weighted_stationary_prod Q hQ (volume.restrict S) hF hFi
    (measurable_const : Measurable fun _ => (1 : ℝ)) (integrable_const 1) measurable_id
  simpa only [one_smul, id_eq] using h.integral_prod_right

/-- The expected canonical flux over every volume-one measurable set is
the canonical expected flux at the origin. -/
theorem canonicalCorrectorFlux_cell_expectation {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) {S : Set (Vec d)} (hvol : volume S = 1) :
    (∫ ω, ∫ x in S, canonicalCorrectorFlux Q i (translate x ω) ∂volume
      ∂reducedEnvironmentLaw Q) = expectedCorrectorFlux Q i := by
  letI : IsFiniteMeasure (volume.restrict S) := ⟨by simp [hvol]⟩
  have h := integral_weighted_stationary (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) (volume.restrict S)
    (Lp.stronglyMeasurable (canonicalCorrectorFlux Q i)).measurable
    (canonicalCorrectorFlux_integrable Q i)
    (measurable_const : Measurable fun _ => (1 : ℝ)) (integrable_const 1) measurable_id
  simpa [Measure.real, hvol, expectedCorrectorFlux] using h

/-- The centered cell in the Lean AKM boundary has volume one. -/
theorem volume_akm_unitCell (d : ℕ) : volume (External.AKM.unitCell d) = 1 := by
  norm_num [External.AKM.unitCell, volume_pi, Measure.pi_pi]

/-- For the actual continuum-stationary canonical flux, changing from
AKM's `[0,1]^d` cell (up to its null boundary) to the centered cell changes
neither the expectation nor its integrability. -/
theorem canonicalCorrectorFlux_centeredCell_eq_sourceCell {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    (∫ ω, ∫ x in External.AKM.unitCell d,
      canonicalCorrectorFlux Q i (translate x ω) ∂volume ∂reducedEnvironmentLaw Q) =
    ∫ ω, ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ico (0 : ℝ) 1),
      canonicalCorrectorFlux Q i (translate x ω) ∂volume ∂reducedEnvironmentLaw Q := by
  rw [canonicalCorrectorFlux_cell_expectation Q i (volume_akm_unitCell d)]
  symm
  apply canonicalCorrectorFlux_cell_expectation Q i
  simp [volume_pi, Measure.pi_pi]

end EinsteinRelation.Correctors

