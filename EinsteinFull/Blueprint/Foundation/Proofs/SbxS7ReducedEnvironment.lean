import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Probability.ReductionLocality
import EinsteinRelation.Sharpness.PhysicalRegularityMeasurability

/-!
Support for `app:factorization#coupling-scope`, paper/main.tex:1474–1487,
1516–1523. The literal zero-potential reduction `(exp(-2V) a₀, 0)` pushes
the supplied environment law to a genuine `EnvironmentLaw` at
`sourceReducedBound Λ₀`, with the same joint finite-range radius. This is
different from the coefficient/clock pair `(exp(-2V) a₀, exp(-2V))`.

To apply physical GMP velocity on this law, a further construction must
produce a measurable physical-origin kernel `P₀` on the transformed law and
identify `P₀ (zeroPotentialReducedPair ω)` with the supplied reduced origin
law for `Q`-almost every `ω`. The original kernel is indexed by the original
environment, so measurability and this identification do not follow merely
from the pushforward construction. No choice of representatives of the
many-to-one reduction, kernel descent, or directional transience is asserted.
-/

open MeasureTheory

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- The actual zero-potential reduction is continuous on the field-pair carrier. -/
theorem coupling_scope_continuous_zeroPotentialReducedPair {d : ℕ} :
    Continuous (zeroPotentialReducedPair (d := d)) :=
  Probability.continuous_reduce.fst.prodMk continuous_const

/-- Its pushforward uses the measurable branch of `Measure.map`. -/
theorem coupling_scope_measurable_zeroPotentialReducedPair {d : ℕ} :
    Measurable (zeroPotentialReducedPair (d := d)) :=
  coupling_scope_continuous_zeroPotentialReducedPair.measurable

/-- A joint local observation after zero-potential reduction sees only the
original joint fields on that same set. -/
theorem coupling_scope_localSigma_zeroPotentialReducedPair_comap_le {d : ℕ}
    (U : Set (Vec d)) :
    (localSigma U).comap (zeroPotentialReducedPair (d := d)) ≤ localSigma U := by
  unfold localSigma
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro x
  rw [MeasurableSpace.comap_comp]
  apply le_trans _ (le_iSup _ x)
  let F : Mat d × ℝ → Mat d × ℝ := fun p =>
    (Real.exp (-2 * p.2) • p.1, 0)
  have hF : Measurable F :=
    (((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).smul
      continuous_fst).prodMk continuous_const).measurable
  have h := MeasurableSpace.comap_mono
    (g := fun ω : FieldPair d => (ω.1 x, ω.2 x)) hF.comap_le
  rw [MeasurableSpace.comap_comp] at h
  exact h

/-- The same map is measurable between the actual joint local sigma-algebras. -/
theorem coupling_scope_measurable_zeroPotentialReducedPair_local {d : ℕ}
    (U : Set (Vec d)) :
    @Measurable (FieldPair d) (FieldPair d) (localSigma U) (localSigma U)
      zeroPotentialReducedPair :=
  Measurable.of_comap_le (coupling_scope_localSigma_zeroPotentialReducedPair_comap_le U)

/-- The zero-potential reduction commutes with the actual spatial translation. -/
theorem coupling_scope_zeroPotentialReducedPair_translate {d : ℕ}
    (x : Vec d) (ω : FieldPair d) :
    zeroPotentialReducedPair (translate x ω) = translate x (zeroPotentialReducedPair ω) := by
  unfold zeroPotentialReducedPair
  rw [reduce_translate]
  rfl

/-- The literal zero-potential pushforward is stationary whenever the original
joint field law is stationary. -/
theorem coupling_scope_isStationary_map_zeroPotentialReducedPair {d : ℕ}
    (μ : Measure (FieldPair d)) (hμ : IsStationary μ) :
    IsStationary (μ.map zeroPotentialReducedPair) := by
  intro x
  rw [Measure.map_map (Probability.measurable_translate x)
    coupling_scope_measurable_zeroPotentialReducedPair]
  have hcomp : translate x ∘ zeroPotentialReducedPair =
      zeroPotentialReducedPair ∘ translate x :=
    funext fun ω => (coupling_scope_zeroPotentialReducedPair_translate x ω).symm
  rw [hcomp, ← Measure.map_map coupling_scope_measurable_zeroPotentialReducedPair
    (Probability.measurable_translate x), hμ x]

/-- Both joint local sigma-algebras shrink under the actual reduction. Thus
the finite-range radius and its strict-gap quantifiers are unchanged. -/
theorem coupling_scope_hasFiniteRange_map_zeroPotentialReducedPair {d : ℕ}
    (r₀ : ℝ) (μ : Measure (FieldPair d)) (hμ : HasFiniteRange r₀ μ) :
    HasFiniteRange r₀ (μ.map zeroPotentialReducedPair) := by
  intro U W hU hW hgap
  have hind := ProbabilityTheory.indep_of_indep_of_le (hμ U W hU hW hgap)
    (coupling_scope_localSigma_zeroPotentialReducedPair_comap_le U)
    (coupling_scope_localSigma_zeroPotentialReducedPair_comap_le W)
  rw [ProbabilityTheory.Indep_iff]
  intro s t hs ht
  have hsB : MeasurableSet s := Probability.localSigma_le_borel U s hs
  have htB : MeasurableSet t := Probability.localSigma_le_borel W t ht
  rw [Measure.map_apply coupling_scope_measurable_zeroPotentialReducedPair (hsB.inter htB),
    Measure.map_apply coupling_scope_measurable_zeroPotentialReducedPair hsB,
    Measure.map_apply coupling_scope_measurable_zeroPotentialReducedPair htB,
    Set.preimage_inter]
  exact (ProbabilityTheory.Indep_iff _ _ _).1 hind _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩

/-- The transformed law has the actual Euclidean ellipticity and Lipschitz
bounds, including both bounds on its zero potential. -/
theorem coupling_scope_ae_regular_map_zeroPotentialReducedPair {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ ω ∂Q.measure.map zeroPotentialReducedPair, IsRegular (sourceReducedBound Λ₀) ω := by
  apply (ae_map_iff coupling_scope_measurable_zeroPotentialReducedPair.aemeasurable
    (Sharpness.measurableSet_isRegular_fieldPair (sourceReducedBound Λ₀))).mpr
  filter_upwards [Q.regular] with ω hω
  exact isRegular_zeroPotentialReducedPair Q.ellipticity_parameter hω

/-- The full environment law of the literal reduced coefficient with zero
potential, on the existing field-pair carrier and with the original range. -/
noncomputable def couplingScopeReducedEnvironmentLaw {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : EnvironmentLaw d (sourceReducedBound Λ₀) r₀ where
  measure := Q.measure.map zeroPotentialReducedPair
  probability := inferInstance
  ellipticity_parameter := one_le_sourceReducedBound Q.ellipticity_parameter
  range_parameter := Q.range_parameter
  regular := coupling_scope_ae_regular_map_zeroPotentialReducedPair Q
  stationary := coupling_scope_isStationary_map_zeroPotentialReducedPair Q.measure Q.stationary
  finiteRange := coupling_scope_hasFiniteRange_map_zeroPotentialReducedPair r₀ Q.measure Q.finiteRange

/-- The constructor has exactly the literal pushforward measure. -/
theorem coupling_scope_reducedEnvironmentLaw_measure {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    (couplingScopeReducedEnvironmentLaw Q).measure = Q.measure.map zeroPotentialReducedPair := rfl

/-- Measurable events under the new law are evaluated on the literal reduced
pair, rather than identified with events under the original field law. -/
theorem coupling_scope_reducedEnvironmentLaw_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (A : Set (FieldPair d)) (hA : MeasurableSet A) :
    (couplingScopeReducedEnvironmentLaw Q).measure A =
      Q.measure (zeroPotentialReducedPair ⁻¹' A) :=
  Measure.map_apply coupling_scope_measurable_zeroPotentialReducedPair hA

/-- Almost-everywhere measurable predicates transport in both directions
between the actual original and transformed laws. -/
theorem coupling_scope_reducedEnvironmentLaw_ae_iff {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {p : FieldPair d → Prop}
    (hp : MeasurableSet {ω | p ω}) :
    (∀ᵐ ω ∂(couplingScopeReducedEnvironmentLaw Q).measure, p ω) ↔
      ∀ᵐ ω ∂Q.measure, p (zeroPotentialReducedPair ω) :=
  ae_map_iff coupling_scope_measurable_zeroPotentialReducedPair.aemeasurable hp

#print axioms coupling_scope_continuous_zeroPotentialReducedPair
#print axioms coupling_scope_measurable_zeroPotentialReducedPair
#print axioms coupling_scope_localSigma_zeroPotentialReducedPair_comap_le
#print axioms coupling_scope_measurable_zeroPotentialReducedPair_local
#print axioms coupling_scope_zeroPotentialReducedPair_translate
#print axioms coupling_scope_isStationary_map_zeroPotentialReducedPair
#print axioms coupling_scope_hasFiniteRange_map_zeroPotentialReducedPair
#print axioms coupling_scope_ae_regular_map_zeroPotentialReducedPair
#print axioms couplingScopeReducedEnvironmentLaw
#print axioms coupling_scope_reducedEnvironmentLaw_measure
#print axioms coupling_scope_reducedEnvironmentLaw_apply
#print axioms coupling_scope_reducedEnvironmentLaw_ae_iff
#lint

end EinsteinFull.Blueprint
