import EinsteinFull.Calculus.U2GMPFinalEnvironment
import EinsteinFull.Calculus.C8GMPMartingale
import MarkovProcess.Kernel.Lp
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import EinsteinFull.Calculus.C9ReducedEnvironmentLaw
import EinsteinFull.Calculus.C17UnforcedEnvironmentInvariant
import EinsteinFull.Calculus.C22SuppliedLawDiscountedOccupation
import EinsteinFull.Calculus.U2GMPEnvironmentRealization
import EinsteinRelation.Environment.ActualImageLpTransportSupport
import EinsteinRelation.Diffusion.FellerKernelUniquenessSupport
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.EMetricSpace.Lipschitz
import EinsteinRelation.Calculus.WeakGradientTranslation
import EinsteinRelation.Diffusion.PhysicalH1Representatives
import EinsteinRelation.Probability.ConjugateKernel

open EinsteinRelation MeasureTheory ProbabilityTheory Filter Topology
open EinsteinRelation.External.GantertSection7Support EinsteinRelation.SpatialDirichlet
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull

/-- The reciprocal clock converts the physical reversible measure into the
force measure. At zero force this is Lebesgue measure, the spatial invariant
measure associated with the reduced diffusion. -/
theorem u2_reversible_measure_reciprocal_clock {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) :
    (physicalReversibleMeasure ω hd lam).withDensity
      (fun x => ENNReal.ofReal ((clockDensity ω x)⁻¹)) =
        EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam := by
  have hf : Measurable (fun x => ENNReal.ofReal (physicalReversibleDensity ω hd lam x)) :=
    ENNReal.measurable_ofReal.comp (physicalReversibleDensity_continuous ω hd lam).measurable
  have hg : Measurable (fun x => ENNReal.ofReal ((clockDensity ω x)⁻¹)) :=
    ENNReal.measurable_ofReal.comp ((reduce ω).2.continuous.inv₀
      (fun x => (clockDensity_pos ω x).ne')).measurable
  ext s hs
  change ((physicalReversibleMeasure ω hd lam).withDensity
    (fun x => ENNReal.ofReal ((clockDensity ω x)⁻¹))) s =
      (volume.withDensity (fun x => ENNReal.ofReal (physicalForceWeight hd lam x))) s
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  change (∫⁻ x in s, ENNReal.ofReal ((clockDensity ω x)⁻¹)
    ∂(volume.withDensity (fun x => ENNReal.ofReal (physicalReversibleDensity ω hd lam x)))) = _
  rw [setLIntegral_withDensity_eq_setLIntegral_mul _ hf hg hs]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply, physicalReversibleDensity]
  rw [← ENNReal.ofReal_mul (mul_nonneg (physicalForceWeight_pos hd lam x).le
    (clockDensity_pos ω x).le)]
  congr 1
  rw [mul_assoc, mul_inv_cancel₀ (clockDensity_pos ω x).ne', mul_one]


/-- At zero force the reciprocal clock turns the reversible measure into volume. -/
theorem u2_reversible_measure_reciprocal_clock_zero {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) :
    (physicalReversibleMeasure ω hd 0).withDensity
      (fun x => ENNReal.ofReal ((clockDensity ω x)⁻¹)) =
        (volume : Measure (Vec d)) := by
  calc
    _ = EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd 0 :=
      u2_reversible_measure_reciprocal_clock hd ω 0
    _ = volume := physicalForceMeasure_zero (firstCoordinateIndex hd)


/-- Pushforward of a measurable density through an equivalence, adapted from
`EinsteinRelation.Probability.map_withDensity_equiv`. -/
theorem u2_map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  change (∫⁻ x in e ⁻¹' s, f x ∂μ) = ∫⁻ y in s, (f ∘ e.symm) y ∂μ.map e
  rw [setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable]
  simp only [Function.comp_apply, e.symm_apply_apply]

/-- The actual reversible measure picks up the exact signed-force factor
under translation, adapted from `map_add_left_physicalReversibleMeasure`. -/
theorem u2_physical_reversible_measure_translate {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ) (z : Vec d) :
    (physicalReversibleMeasure (translate z ω) hd lam).map (fun x => z + x) =
      ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd))) •
        physicalReversibleMeasure ω hd lam := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  have hf : Measurable (fun x => ENNReal.ofReal
      (physicalReversibleDensity (translate z ω) hd lam x)) :=
    ENNReal.measurable_ofReal.comp (physicalReversibleDensity_continuous _ hd lam).measurable
  have hfo : Measurable (fun x => ENNReal.ofReal (physicalReversibleDensity ω hd lam x)) :=
    ENNReal.measurable_ofReal.comp (physicalReversibleDensity_continuous ω hd lam).measurable
  have hm : (volume : Measure (Vec d)).map e = volume := by
    change (volume : Measure (Vec d)).map (fun x => z + x) = volume
    exact (measurePreserving_add_left (volume : Measure (Vec d)) z).map_eq
  change (volume.withDensity (fun x => ENNReal.ofReal
    (physicalReversibleDensity (translate z ω) hd lam x))).map e = _
  rw [u2_map_withDensity_equiv e _ _ hf, hm]
  have hden : (fun y => ENNReal.ofReal (physicalReversibleDensity (translate z ω) hd lam (e.symm y))) =
      ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd))) •
        (fun y => ENNReal.ofReal (physicalReversibleDensity ω hd lam y)) := by
    funext x
    have hclock : clockDensity (translate z ω) (e.symm x) = clockDensity ω x := by
      simp [clockDensity, translate, e]
    have hforce : physicalForceWeight hd lam (e.symm x) =
        Real.exp (-2 * lam * z (firstCoordinateIndex hd)) * physicalForceWeight hd lam x := by
      unfold physicalForceWeight
      rw [← Real.exp_add]
      congr 1
      change 2 * lam * (-z (firstCoordinateIndex hd) + x (firstCoordinateIndex hd)) = _
      ring
    change ENNReal.ofReal (physicalForceWeight hd lam (e.symm x) *
      clockDensity (translate z ω) (e.symm x)) = _
    rw [hclock, hforce, mul_assoc, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rfl
  rw [hden, withDensity_smul _ hfo]
  rfl

/-- Spatial translation scales the actual exponential force measure. -/
theorem u2_physical_force_measure_translate {d : ℕ}
    (hd : 2 ≤ d) (lam : ℝ) (z : Vec d) :
    (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam).map (fun x => z + x) =
      ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd))) •
        EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  have hf : Measurable (fun x => ENNReal.ofReal (physicalForceWeight hd lam x)) :=
    ENNReal.measurable_ofReal.comp (physicalForceWeight_continuous hd lam).measurable
  have hm : (volume : Measure (Vec d)).map e = volume := by
    change (volume : Measure (Vec d)).map (fun x => z + x) = volume
    exact (measurePreserving_add_left (volume : Measure (Vec d)) z).map_eq
  change (volume.withDensity (fun x => ENNReal.ofReal (physicalForceWeight hd lam x))).map e = _
  rw [u2_map_withDensity_equiv e _ _ hf, hm]
  have hw (x : Vec d) : physicalForceWeight hd lam (e.symm x) =
      Real.exp (-2 * lam * z (firstCoordinateIndex hd)) * physicalForceWeight hd lam x := by
    unfold physicalForceWeight
    rw [← Real.exp_add]
    congr 1
    change 2 * lam * (-z (firstCoordinateIndex hd) + x (firstCoordinateIndex hd)) = _
    ring
  have hden : (fun y => ENNReal.ofReal (physicalForceWeight hd lam (e.symm y))) =
      ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd))) •
        (fun y => ENNReal.ofReal (physicalForceWeight hd lam y)) := by
    funext x
    rw [hw, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rfl
  rw [hden, withDensity_smul _ hf]
  rfl

/-- Translation preserves Lp membership for the actual exponential force weight. -/
theorem u2_memLp_translate_physical_force_iff {d : ℕ} (hd : 2 ≤ d)
    (lam : ℝ) (z : Vec d) {E : Type*} [NormedAddCommGroup E]
    (f : Vec d → E) (p : ℝ≥0∞) :
    MemLp (fun y => f (z + y)) p (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) ↔
      MemLp f p (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd)))
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hm : (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam).map e = c • EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam :=
    u2_physical_force_measure_translate hd lam z
  have he : MemLp (fun y => f (z + y)) p (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) ↔
      MemLp f p ((EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam).map e) := by
    change MemLp (f ∘ e) p (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) ↔ _
    exact (e.memLp_map_measure_iff (g := f)).symm
  rw [he, hm]
  constructor
  · intro h
    have hi := h.smul_measure (c := c⁻¹) (by simpa using hc)
    simpa only [smul_smul, ENNReal.inv_mul_cancel hc hct, one_smul] using hi
  · intro h
    exact h.smul_measure hct

/-- Translate a full weighted weak-gradient graph without changing its domain. -/
def u2TranslatePhysicalGraph {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) (z : Vec d)
    (u : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam)) :
    SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) where
  value x := u.value (z + x)
  weakGradient x := u.weakGradient (z + x)
  value_memLp := (u2_memLp_translate_physical_force_iff hd lam z u.value 2).mpr u.value_memLp
  gradient_memLp := (u2_memLp_translate_physical_force_iff hd lam z u.weakGradient 2).mpr u.gradient_memLp
  distributionalGradient := u.distributionalGradient.comp_add_left z

/-- The full physical H1 domain is transported by spatial translation. -/
theorem u2_physicalH1Member_translate_iff {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ) (z : Vec d) (f : Vec d → ℝ) :
    physicalH1Member (translate z ω) hd lam f ↔
      physicalH1Member ω hd lam (fun y => f ((MeasurableEquiv.addLeft z).symm y)) := by
  rw [physicalH1Member_iff_exists_graph, physicalH1Member_iff_exists_graph]
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd)))
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      c • physicalReversibleMeasure ω hd lam :=
    u2_physical_reversible_measure_translate ω hd lam z
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u2TranslatePhysicalGraph hd lam (-z) u, ?_⟩
    have hmap : (fun y => u.value (e.symm y)) =ᵐ[
        (physicalReversibleMeasure (translate z ω) hd lam).map e]
          (fun y => f (e.symm y)) :=
      e.measurableEmbedding.ae_map_iff.mpr (by simpa only [Filter.EventuallyEq, e.symm_apply_apply] using hu)
    rw [hm] at hmap
    have h := (Measure.ae_ennreal_smul_measure_iff hc).mp hmap
    simpa [Filter.EventuallyEq, u2TranslatePhysicalGraph, e, sub_eq_neg_add] using h
  · rintro ⟨u, hu⟩
    refine ⟨u2TranslatePhysicalGraph hd lam z u, ?_⟩
    have hscaled := Measure.ae_smul_measure hu c
    rw [← hm] at hscaled
    have h := e.measurableEmbedding.ae_map_iff.mp hscaled
    simpa [Filter.EventuallyEq, u2TranslatePhysicalGraph, e] using h

/-- The full form is the energy of any weak-gradient representatives. -/
theorem u2_physical_form_eq_graph {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (u v : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (hv : v.value =ᵐ[physicalReversibleMeasure ω hd lam] g) :
    Blueprint.gmpPhysicalH1Form hd ω lam Λ hω f g =
      ∫ x, SpatialDirichlet.weightedFormIntegrand ω.1 u v x
        ∂physicalReversibleMeasure ω hd lam := by
  have hf : physicalH1Member ω hd lam f :=
    (physicalH1Member_iff_exists_graph ω hd lam f).mpr ⟨u, hu⟩
  have hg : physicalH1Member ω hd lam g :=
    (physicalH1Member_iff_exists_graph ω hd lam g).mpr ⟨v, hv⟩
  obtain ⟨a, ha⟩ := (Blueprint.gmpPhysicalH1Value_range_iff hd ω lam Λ hω f).mpr hf
  obtain ⟨b, hb⟩ := (Blueprint.gmpPhysicalH1Value_range_iff hd ω lam Λ hω g).mpr hg
  let a' := SpatialDirichlet.densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) a
  let b' := SpatialDirichlet.densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) b
  have hrep (w : Blueprint.GMPForceH1 hd lam)
      (q : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
      (hq : q.value =ᵐ[physicalReversibleMeasure ω hd lam]
        Blueprint.gmpPhysicalH1Value hd ω lam Λ hω w) :
      (fun x => WithLp.ofLp ((SpatialDirichlet.densityWeightedH1SpaceRepresentative
        (sourceReducedDensity hd lam) (continuousSourceReducedDensity hd lam)
        (positiveSourceReducedDensity hd lam) w).weakGradient x)) =ᵐ[
          physicalReversibleMeasure ω hd lam] (fun x => WithLp.ofLp (q.weakGradient x)) := by
    let r := SpatialDirichlet.densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) w
    have hr := Blueprint.gmpH1Representative_value_ae (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) w
    have hp := (Measure.absolutelyContinuous_of_le_smul
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq hr
    have hval : r.value =ᵐ[physicalReversibleMeasure ω hd lam] q.value :=
      hp.trans ((Blueprint.gmpPhysicalH1Value_ae_eq hd ω lam Λ hω w).symm.trans hq.symm)
    have hvol := (ae_withDensity_iff_volume_of_continuous_pos
      (sourcePhysicalDensity ω hd lam) (continuousSourcePhysicalDensity ω hd lam)
      (positiveSourcePhysicalDensity ω hd lam) _).mp hval
    have hgrad := weakGradients_ae_eq_of_value_ae_eq hvol r.distributionalGradient q.distributionalGradient
    exact (ae_withDensity_iff_volume_of_continuous_pos
      (sourcePhysicalDensity ω hd lam) (continuousSourcePhysicalDensity ω hd lam)
      (positiveSourcePhysicalDensity ω hd lam) _).mpr hgrad
  have hau := hrep a u (by simpa only [ha] using hu)
  have hbv := hrep b v (by simpa only [hb] using hv)
  rw [← ha, ← hb, Blueprint.gmpPhysicalH1Form_value, Blueprint.gmpPhysicalH1Energy_eq_source]
  apply integral_congr_ae
  filter_upwards [hau, hbv] with x hax hbx
  change (1 / 2 : ℝ) * dot (WithLp.ofLp (a'.weakGradient x))
      ((ω.1 x).mulVec (WithLp.ofLp (b'.weakGradient x))) =
    (1 / 2 : ℝ) * dot (WithLp.ofLp (u.weakGradient x))
      ((ω.1 x).mulVec (WithLp.ofLp (v.weakGradient x)))
  rw [hax, hbx]

/-- Full physical bilinear energy transforms with the reversible-measure factor. -/
theorem u2_physical_bilinear_energy_translate {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ) (z : Vec d)
    (u v : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam)) :
    (∫ x, SpatialDirichlet.weightedFormIntegrand (translate z ω).1 u v x
      ∂physicalReversibleMeasure (translate z ω) hd lam) =
    Real.exp (-2 * lam * z (firstCoordinateIndex hd)) *
      ∫ x, SpatialDirichlet.weightedFormIntegrand ω.1
        (u2TranslatePhysicalGraph hd lam (-z) u) (u2TranslatePhysicalGraph hd lam (-z) v) x
        ∂physicalReversibleMeasure ω hd lam := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  have hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd))) •
        physicalReversibleMeasure ω hd lam :=
    u2_physical_reversible_measure_translate ω hd lam z
  have hi := integral_map_equiv (μ := physicalReversibleMeasure (translate z ω) hd lam) e
    (fun y => SpatialDirichlet.weightedFormIntegrand (translate z ω).1 u v (e.symm y))
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hi
  calc
    _ = Real.exp (-2 * lam * z (firstCoordinateIndex hd)) *
        ∫ y, SpatialDirichlet.weightedFormIntegrand (translate z ω).1 u v (e.symm y)
          ∂physicalReversibleMeasure ω hd lam := by
      simpa only [e.symm_apply_apply, smul_eq_mul] using hi.symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp [SpatialDirichlet.weightedFormIntegrand, u2TranslatePhysicalGraph, translate, e]

/-- Conjugating a kernel transports its actual short-time form by the
same scaling as its reversible measure. -/
theorem u2_semigroup_form_quotient_conjugate {d : ℕ}
    (ω ω' : FieldPair d) (hd : 2 ≤ d) (lam : ℝ)
    (e : Vec d ≃ᵐ Vec d) (c : ℝ) (hc : 0 ≤ c)
    (hm : (physicalReversibleMeasure ω' hd lam).map e =
      ENNReal.ofReal c • physicalReversibleMeasure ω hd lam)
    (K : ℝ≥0 → Kernel (Vec d) (Vec d)) (t : ℝ≥0) (f : Vec d → ℝ) :
    semigroupFormDifferenceQuotient ω' hd lam (fun t => Probability.conjugateKernel e (K t)) t f =
      c * semigroupFormDifferenceQuotient ω hd lam K t (fun y => f (e.symm y)) := by
  let g : Vec d → ℝ := fun y =>
    (f (e.symm y) - ∫ z, f (e.symm z) ∂K t y) * f (e.symm y)
  have hi := integral_map_equiv (μ := physicalReversibleMeasure ω' hd lam) e g
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal hc] at hi
  have hi' : (∫ x, (f x - ∫ y, f (e.symm y) ∂K t (e x)) * f x
      ∂physicalReversibleMeasure ω' hd lam) =
      c * ∫ x, (f (e.symm x) - ∫ y, f (e.symm y) ∂K t x) * f (e.symm x)
        ∂physicalReversibleMeasure ω hd lam := by
    simpa only [g, e.symm_apply_apply, smul_eq_mul] using hi.symm
  simp only [semigroupFormDifferenceQuotient, Probability.integral_conjugateKernel]
  rw [hi']
  ring

/-- Conjugation carries L² representatives through a positive measure scaling. -/
theorem u2_memLp_comp_symm_of_map_eq_smul {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] (e : α ≃ᵐ α) (μ ν : Measure α)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞) (hm : μ.map e = c • ν)
    (f : α → E) (p : ℝ≥0∞) (hf : MemLp f p μ) :
    MemLp (fun y => f (e.symm y)) p ν := by
  have h : MemLp (fun y => f (e.symm y)) p (μ.map e) := by
    apply e.memLp_map_measure_iff.mpr
    simpa only [Function.comp_def, e.symm_apply_apply] using hf
  rw [hm] at h
  have h' := h.smul_measure (c := c⁻¹) (by simpa using hc0)
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul] using h'

/-- Almost-everywhere equality is preserved when representatives are transported
through the spatial equivalence and its positive measure scaling. -/
theorem u2_ae_comp_symm_of_map_eq_smul {α E : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (μ ν : Measure α) (c : ℝ≥0∞) (hc0 : c ≠ 0)
    (hm : μ.map e = c • ν) {f g : α → E} (hfg : f =ᵐ[μ] g) :
    (fun y => f (e.symm y)) =ᵐ[ν] (fun y => g (e.symm y)) := by
  have h : (fun y => f (e.symm y)) =ᵐ[μ.map e] (fun y => g (e.symm y)) :=
    e.measurableEmbedding.ae_map_iff.mpr (by simpa only [Filter.EventuallyEq, e.symm_apply_apply] using hfg)
  rw [hm] at h
  exact (Measure.ae_ennreal_smul_measure_iff hc0).mp h

/-- Translation of weighted L² classes as a linear map; no normalization is
introduced into the representatives. -/
noncomputable def u2LpCompSymmOfMapEqSmul {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (μ ν : Measure α) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hct : c ≠ ∞) (hm : μ.map e = c • ν) :
    Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 ν where
  toFun f := (u2_memLp_comp_symm_of_map_eq_smul e μ ν c hc0 hct hm f 2
    (Lp.memLp f)).toLp (fun y => f (e.symm y))
  map_add' f g := by
    apply Lp.ext
    have hf := (u2_memLp_comp_symm_of_map_eq_smul e μ ν c hc0 hct hm f 2 (Lp.memLp f)).coeFn_toLp
    have hg := (u2_memLp_comp_symm_of_map_eq_smul e μ ν c hc0 hct hm g 2 (Lp.memLp g)).coeFn_toLp
    have hfg := (u2_memLp_comp_symm_of_map_eq_smul e μ ν c hc0 hct hm (f + g) 2 (Lp.memLp (f + g))).coeFn_toLp
    have ha := u2_ae_comp_symm_of_map_eq_smul e μ ν c hc0 hm (Lp.coeFn_add f g)
    filter_upwards [hf, hg, hfg, ha, Lp.coeFn_add ((u2_memLp_comp_symm_of_map_eq_smul e μ ν c hc0 hct hm f 2 (Lp.memLp f)).toLp (fun y => f (e.symm y))) ((u2_memLp_comp_symm_of_map_eq_smul e μ ν c hc0 hct hm g 2 (Lp.memLp g)).toLp (fun y => g (e.symm y)))] with y hf' hg' hfg' ha' hs
    simp only [Pi.add_apply] at ha' hs
    rw [hfg', hs, hf', hg', ha']
  map_smul' a f := by
    apply Lp.ext
    have hf := (u2_memLp_comp_symm_of_map_eq_smul e μ ν c hc0 hct hm f 2 (Lp.memLp f)).coeFn_toLp
    have haf := (u2_memLp_comp_symm_of_map_eq_smul e μ ν c hc0 hct hm (a • f) 2 (Lp.memLp (a • f))).coeFn_toLp
    have ha := u2_ae_comp_symm_of_map_eq_smul e μ ν c hc0 hm (Lp.coeFn_smul a f)
    filter_upwards [hf, haf, ha, Lp.coeFn_smul a ((u2_memLp_comp_symm_of_map_eq_smul e μ ν c hc0 hct hm f 2 (Lp.memLp f)).toLp (fun y => f (e.symm y)))] with y hf' haf' ha' hs
    simp only [Pi.smul_apply] at ha' hs
    simp only [RingHom.id_apply]
    rw [haf', hs, hf', ha']

/-- The L² map is represented by the literal translated function. -/
theorem u2LpCompSymmOfMapEqSmul_coe {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (μ ν : Measure α) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hct : c ≠ ∞) (hm : μ.map e = c • ν) (f : Lp ℝ 2 μ) :
    u2LpCompSymmOfMapEqSmul e μ ν c hc0 hct hm f =ᵐ[ν] (fun y => f (e.symm y)) :=
  (u2_memLp_comp_symm_of_map_eq_smul e μ ν c hc0 hct hm f 2 (Lp.memLp f)).coeFn_toLp

/-- The inverse spatial map has the reciprocal measure-scaling factor. -/
theorem u2_map_symm_eq_inv_smul {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (μ ν : Measure α) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hct : c ≠ ∞) (hm : μ.map e = c • ν) :
    ν.map e.symm = c⁻¹ • μ := by
  have h := congrArg (fun m : Measure α => m.map e.symm) hm
  rw [e.map_symm_map, Measure.map_smul c e.symm.measurable.aemeasurable] at h
  calc
    ν.map e.symm = (c⁻¹ * c) • ν.map e.symm := by
      rw [ENNReal.inv_mul_cancel hc0 hct, one_smul]
    _ = c⁻¹ • μ := by rw [← smul_smul, ← h]

/-- The weighted L² transports in both directions are linear inverses. -/
noncomputable def u2LpCompSymmEquivOfMapEqSmul {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (μ ν : Measure α) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hct : c ≠ ∞) (hm : μ.map e = c • ν) :
    Lp ℝ 2 μ ≃ₗ[ℝ] Lp ℝ 2 ν := by
  let hi : c⁻¹ ≠ 0 := by simpa using hct
  let hit : c⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hc0
  let hm' := u2_map_symm_eq_inv_smul e μ ν c hc0 hct hm
  let F := u2LpCompSymmOfMapEqSmul e μ ν c hc0 hct hm
  let G := u2LpCompSymmOfMapEqSmul e.symm ν μ c⁻¹ hi hit hm'
  refine { F with invFun := G, left_inv := ?_, right_inv := ?_ }
  · intro f
    apply Lp.ext
    have h1 := u2LpCompSymmOfMapEqSmul_coe e μ ν c hc0 hct hm f
    have h2 := u2LpCompSymmOfMapEqSmul_coe e.symm ν μ c⁻¹ hi hit hm' (F f)
    have h3 := u2_ae_comp_symm_of_map_eq_smul e.symm ν μ c⁻¹ hi hm' h1
    filter_upwards [h2, h3] with x hx hy
    change G (F f) x = f x
    simpa only [MeasurableEquiv.symm_symm, e.symm_apply_apply] using hx.trans hy
  · intro f
    apply Lp.ext
    have h1 := u2LpCompSymmOfMapEqSmul_coe e.symm ν μ c⁻¹ hi hit hm' f
    have h2 := u2LpCompSymmOfMapEqSmul_coe e μ ν c hc0 hct hm (G f)
    have h3 := u2_ae_comp_symm_of_map_eq_smul e μ ν c hc0 hm h1
    filter_upwards [h2, h3] with x hx hy
    change F (G f) x = f x
    simpa only [MeasurableEquiv.symm_symm, e.apply_symm_apply] using hx.trans hy

/-- Transport scales the physical L² inner product by the measure factor. -/
theorem u2LpCompSymmOfMapEqSmul_inner {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (μ ν : Measure α) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hct : c ≠ ∞) (hm : μ.map e = c • ν)
    (f g : Lp ℝ 2 μ) :
    inner ℝ f g = c.toReal * inner ℝ
      (u2LpCompSymmOfMapEqSmul e μ ν c hc0 hct hm f)
      (u2LpCompSymmOfMapEqSmul e μ ν c hc0 hct hm g) := by
  have hi := integral_map_equiv (μ := μ) e
    (fun y => f (e.symm y) * g (e.symm y))
  rw [hm, integral_smul_measure] at hi
  have hfg : (∫ x, f x * g x ∂μ) =
      c.toReal * ∫ y, f (e.symm y) * g (e.symm y) ∂ν := by
    simpa only [e.symm_apply_apply, smul_eq_mul] using hi.symm
  rw [L2.inner_def]
  calc
    _ = c.toReal * ∫ y, f (e.symm y) * g (e.symm y) ∂ν := by
      simpa [RCLike.inner_apply, mul_comm] using hfg
    _ = _ := by
      congr 1
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [u2LpCompSymmOfMapEqSmul_coe e μ ν c hc0 hct hm f,
        u2LpCompSymmOfMapEqSmul_coe e μ ν c hc0 hct hm g] with y hf hg
      simp [RCLike.inner_apply, hf, hg, mul_comm]

/-- The unnormalized weighted L² translation is continuous with its exact
measure-scaling bound. -/
noncomputable def u2LpCompSymmContinuousOfMapEqSmul {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (μ ν : Measure α) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hct : c ≠ ∞) (hm : μ.map e = c • ν) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν := by
  let T := u2LpCompSymmOfMapEqSmul e μ ν c hc0 hct hm
  have hc : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
  have hs : 0 < Real.sqrt c.toReal := Real.sqrt_pos.mpr hc
  refine T.mkContinuous (Real.sqrt c.toReal)⁻¹ ?_
  intro f
  have h := u2LpCompSymmOfMapEqSmul_inner e μ ν c hc0 hct hm f f
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  change ‖f‖ ^ 2 = c.toReal * ‖T f‖ ^ 2 at h
  have hsq : (Real.sqrt c.toReal * ‖T f‖) ^ 2 = ‖f‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le]
    exact h.symm
  have heq : Real.sqrt c.toReal * ‖T f‖ = ‖f‖ := by
    nlinarith [mul_nonneg hs.le (norm_nonneg (T f)), norm_nonneg f]
  have hb : ‖T f‖ ≤ ‖f‖ / Real.sqrt c.toReal :=
    (le_div_iff₀ hs).mpr (by nlinarith [heq])
  simpa [div_eq_mul_inv, mul_comm] using hb

/-- The weighted L² equivalence carries the whole physical H¹ domain. -/
theorem u2_physicalH1Member_Lp_translate_iff {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ) (z : Vec d)
    (f : Lp ℝ 2 (physicalReversibleMeasure (translate z ω) hd lam)) :
    let e := MeasurableEquiv.addLeft z
    let c := ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd)))
    let hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    let hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      c • physicalReversibleMeasure ω hd lam :=
        u2_physical_reversible_measure_translate ω hd lam z
    physicalH1Member (translate z ω) hd lam f ↔
      physicalH1Member ω hd lam
        (u2LpCompSymmOfMapEqSmul e _ _ c hc ENNReal.ofReal_ne_top hm f) := by
  dsimp only
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  let c := ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd)))
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      c • physicalReversibleMeasure ω hd lam :=
    u2_physical_reversible_measure_translate ω hd lam z
  have hcoe := u2LpCompSymmOfMapEqSmul_coe e _ _ c hc ENNReal.ofReal_ne_top hm f
  rw [u2_physicalH1Member_translate_iff ω hd lam z f]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.trans hcoe.symm⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.trans hcoe⟩

/-- Translation intertwines the full physical bilinear forms, with the exact
signed reversible-measure factor. -/
theorem u2_physicalH1Form_translate {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (z : Vec d)
    (f g : Lp ℝ 2 (physicalReversibleMeasure (translate z ω) hd lam))
    (hf : physicalH1Member (translate z ω) hd lam f)
    (hg : physicalH1Member (translate z ω) hd lam g) :
    let e := MeasurableEquiv.addLeft z
    let c := ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd)))
    let hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    let hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      c • physicalReversibleMeasure ω hd lam :=
        u2_physical_reversible_measure_translate ω hd lam z
    Blueprint.gmpPhysicalH1Form hd (translate z ω) lam Λ
        ((ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω) f g =
      Real.exp (-2 * lam * z (firstCoordinateIndex hd)) *
        Blueprint.gmpPhysicalH1Form hd ω lam Λ hω
          (u2LpCompSymmOfMapEqSmul e _ _ c hc ENNReal.ofReal_ne_top hm f)
          (u2LpCompSymmOfMapEqSmul e _ _ c hc ENNReal.ofReal_ne_top hm g) := by
  dsimp only
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  let c := ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd)))
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      c • physicalReversibleMeasure ω hd lam :=
    u2_physical_reversible_measure_translate ω hd lam z
  obtain ⟨u, hu⟩ := (physicalH1Member_iff_exists_graph (translate z ω) hd lam f).mp hf
  obtain ⟨v, hv⟩ := (physicalH1Member_iff_exists_graph (translate z ω) hd lam g).mp hg
  have htrans (q : WeightedSobolevGraph
      (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
      (h : Lp ℝ 2 (physicalReversibleMeasure (translate z ω) hd lam))
      (hq : q.value =ᵐ[physicalReversibleMeasure (translate z ω) hd lam] h) :
      (u2TranslatePhysicalGraph hd lam (-z) q).value =ᵐ[physicalReversibleMeasure ω hd lam]
        u2LpCompSymmOfMapEqSmul e _ _ c hc ENNReal.ofReal_ne_top hm h := by
    have h1 := u2_ae_comp_symm_of_map_eq_smul e _ _ c hc hm hq
    have h2 := u2LpCompSymmOfMapEqSmul_coe e _ _ c hc ENNReal.ofReal_ne_top hm h
    have h3 : (u2TranslatePhysicalGraph hd lam (-z) q).value =ᵐ[
        physicalReversibleMeasure ω hd lam] (fun y => h (e.symm y)) := by
      simpa [u2TranslatePhysicalGraph, e, sub_eq_neg_add] using h1
    exact h3.trans h2.symm
  rw [u2_physical_form_eq_graph hd (translate z ω) lam Λ _ f g u v hu hv,
    u2_physical_form_eq_graph hd ω lam Λ hω _ _
      (u2TranslatePhysicalGraph hd lam (-z) u) (u2TranslatePhysicalGraph hd lam (-z) v)
      (htrans u f hu) (htrans v g hv)]
  exact u2_physical_bilinear_energy_translate ω hd lam z u v

/-- The actual physical resolvents commute with spatial translation. -/
theorem u2_physicalResolvent_translate {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (z : Vec d)
    (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure (translate z ω) hd lam)) :
    let e := MeasurableEquiv.addLeft z
    let c := ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd)))
    let hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    let hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      c • physicalReversibleMeasure ω hd lam :=
        u2_physical_reversible_measure_translate ω hd lam z
    u2LpCompSymmOfMapEqSmul e _ _ c hc ENNReal.ofReal_ne_top hm
      (Blueprint.gmpPhysicalResolvent hd (translate z ω) lam Λ hΛ
        ((ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω) α hα f) =
    Blueprint.gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
      (u2LpCompSymmOfMapEqSmul e _ _ c hc ENNReal.ofReal_ne_top hm f) := by
  dsimp only
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  let c := ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd)))
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      c • physicalReversibleMeasure ω hd lam :=
    u2_physical_reversible_measure_translate ω hd lam z
  let T := u2LpCompSymmOfMapEqSmul e _ _ c hc ENNReal.ofReal_ne_top hm
  let E := u2LpCompSymmEquivOfMapEqSmul e _ _ c hc ENNReal.ofReal_ne_top hm
  let hωz : IsRegular Λ (translate z ω) :=
    (ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω
  let U := Blueprint.gmpPhysicalResolvent hd (translate z ω) lam Λ hΛ hωz α hα f
  have hres := Blueprint.gmpPhysicalResolvent_isResolvent hd (translate z ω) lam Λ hΛ hωz α hα
  have hU : physicalH1Member (translate z ω) hd lam U :=
    (Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd (translate z ω) lam Λ hΛ hωz U).mp
      (hres.mem_domain f)
  have hTU : physicalH1Member ω hd lam (T U) :=
    (u2_physicalH1Member_Lp_translate_iff hd ω lam z U).mp hU
  apply Blueprint.gmpPhysicalResolvent_unique hd ω lam Λ hΛ hω α hα (T f) hTU
  intro v hv
  let w := E.symm v
  have hTw : T w = v := E.apply_symm_apply v
  have hv' : physicalH1Member ω hd lam v :=
    (Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω v).mp hv
  have hw : physicalH1Member (translate z ω) hd lam w := by
    apply (u2_physicalH1Member_Lp_translate_iff hd ω lam z w).mpr
    change physicalH1Member ω hd lam (T w)
    rw [hTw]
    exact hv' 
  have hw' := (Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd (translate z ω)
    lam Λ hΛ hωz w).mpr hw
  have heq := hres.eq f hw'
  change α * inner ℝ U w + Blueprint.gmpPhysicalH1Form hd (translate z ω) lam Λ hωz U w =
    inner ℝ f w at heq
  rw [u2LpCompSymmOfMapEqSmul_inner e _ _ c hc ENNReal.ofReal_ne_top hm U w,
    u2_physicalH1Form_translate hd ω lam Λ hω z U w hU hw,
    u2LpCompSymmOfMapEqSmul_inner e _ _ c hc ENNReal.ofReal_ne_top hm f w] at heq
  change α * (c.toReal * inner ℝ (T U) (T w)) +
      Real.exp (-2 * lam * z (firstCoordinateIndex hd)) *
        Blueprint.gmpPhysicalH1Form hd ω lam Λ hω (T U) (T w) =
      c.toReal * inner ℝ (T f) (T w) at heq
  have hcval : c.toReal = Real.exp (-2 * lam * z (firstCoordinateIndex hd)) :=
    ENNReal.toReal_ofReal (Real.exp_pos _).le
  rw [hcval, hTw] at heq
  have hp := Real.exp_pos (-2 * lam * z (firstCoordinateIndex hd))
  nlinarith

/-- The conjugated actual kernel has the complete translated H¹ form domain. -/
theorem u2_regular_conjugate_closedForm_domain {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (z : Vec d) (f : Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure (translate z ω) hd lam)) :
    ((∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient (translate z ω) hd lam
        (fun t => Probability.conjugateKernel (MeasurableEquiv.addLeft z)
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t)) t f ≤ C) ↔
      physicalH1Member (translate z ω) hd lam f) := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  let c : ℝ := Real.exp (-2 * lam * z (firstCoordinateIndex hd))
  have hc : 0 < c := Real.exp_pos _
  have hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      ENNReal.ofReal c • physicalReversibleMeasure ω hd lam :=
    u2_physical_reversible_measure_translate ω hd lam z
  have hf' := u2_memLp_comp_symm_of_map_eq_smul e _ _ (ENNReal.ofReal c)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top hm f 2 hf
  rw [u2_physicalH1Member_translate_iff, ← u2_regular_kernel_closedForm_domain hd ω lam Λ hΛ hω _ hf']
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C / c, fun t ht => ?_⟩
    have h := hC t ht
    rw [u2_semigroup_form_quotient_conjugate ω (translate z ω) hd lam e c hc.le hm] at h
    apply (le_div_iff₀ hc).mpr
    nlinarith
  · rintro ⟨C, hC⟩
    refine ⟨c * C, fun t ht => ?_⟩
    rw [u2_semigroup_form_quotient_conjugate ω (translate z ω) hd lam e c hc.le hm]
    exact mul_le_mul_of_nonneg_left (hC t ht) hc.le

/-- The conjugated actual kernel has the translated full H¹ energy. -/
theorem u2_regular_conjugate_closedForm_value {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (z : Vec d) (f : Vec d → ℝ)
    (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure (translate z ω) hd lam] f)
    (u : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure (translate z ω) hd lam] f) :
    Tendsto (fun t : ℝ≥0 => semigroupFormDifferenceQuotient (translate z ω) hd lam
      (fun t => Probability.conjugateKernel (MeasurableEquiv.addLeft z)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t)) t f)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 (physicalH1FormEnergy (translate z ω) hd lam u)) := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  let c : ℝ := Real.exp (-2 * lam * z (firstCoordinateIndex hd))
  have hc : 0 < c := Real.exp_pos _
  have hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      ENNReal.ofReal c • physicalReversibleMeasure ω hd lam :=
    u2_physical_reversible_measure_translate ω hd lam z
  have hmap : (fun y => u.value (e.symm y)) =ᵐ[
      (physicalReversibleMeasure (translate z ω) hd lam).map e] (fun y => f (e.symm y)) :=
    e.measurableEmbedding.ae_map_iff.mpr (by simpa only [Filter.EventuallyEq, e.symm_apply_apply] using hu)
  rw [hm] at hmap
  have huold : (u2TranslatePhysicalGraph hd lam (-z) u).value =ᵐ[
      physicalReversibleMeasure ω hd lam] (fun y => f (e.symm y)) := by
    have h := (Measure.ae_ennreal_smul_measure_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hc))).mp hmap
    simpa [Filter.EventuallyEq, u2TranslatePhysicalGraph, e, sub_eq_neg_add] using h
  obtain ⟨qold, hqold⟩ := (u2_physicalH1Member_translate_iff ω hd lam z f).mp ⟨q, hq⟩
  have hlim := (u2_regular_kernel_closedForm_value hd ω lam Λ hΛ hω
    (fun y => f (e.symm y)) qold hqold (u2TranslatePhysicalGraph hd lam (-z) u) huold).const_mul c
  have he : physicalH1FormEnergy (translate z ω) hd lam u =
      c * physicalH1FormEnergy ω hd lam (u2TranslatePhysicalGraph hd lam (-z) u) :=
    u2_physical_bilinear_energy_translate ω hd lam z u u
  rw [he]
  convert hlim using 1
  funext t
  exact u2_semigroup_form_quotient_conjugate ω (translate z ω) hd lam e c hc.le hm _ t f

/-- The actual translated kernel and conjugated kernel have the same full
short-time form domain. -/
theorem u2_regular_translated_conjugate_form_domain_eq {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (z : Vec d) (f : Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure (translate z ω) hd lam)) :
    (∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient (translate z ω) hd lam
        (fun t => u2RegularC0KernelSemigroup hd (translate z ω) lam Λ hΛ
          ((ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω) t) t f ≤ C) ↔
    (∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient (translate z ω) hd lam
        (fun t => Probability.conjugateKernel (MeasurableEquiv.addLeft z)
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t)) t f ≤ C) := by
  exact (u2_regular_kernel_closedForm_domain hd (translate z ω) lam Λ hΛ
    ((ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω) f hf).trans
      (u2_regular_conjugate_closedForm_domain hd ω lam Λ hΛ hω z f hf).symm

/-- Both actual kernels recover the same energy on the full translated form
 domain, for every weak-gradient representative. -/
theorem u2_regular_translated_conjugate_form_value_eq {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (z : Vec d) (f : Vec d → ℝ)
    (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure (translate z ω) hd lam] f)
    (u : SpatialDirichlet.WeightedSobolevGraph
      (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure (translate z ω) hd lam] f) :
    Tendsto (fun t : ℝ≥0 => semigroupFormDifferenceQuotient (translate z ω) hd lam
      (fun s => u2RegularC0KernelSemigroup hd (translate z ω) lam Λ hΛ
        ((ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω) s) t f -
      semigroupFormDifferenceQuotient (translate z ω) hd lam
      (fun s => Probability.conjugateKernel (MeasurableEquiv.addLeft z)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s)) t f)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 0) := by
  simpa using (u2_regular_kernel_closedForm_value hd (translate z ω) lam Λ hΛ
    ((ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω) f q hq u hu).sub
      (u2_regular_conjugate_closedForm_value hd ω lam Λ hΛ hω z f q hq u hu)

/-- The requested covariance holds at zero time, with the regularity witness
obtained from the actual translated coefficient pair. -/
theorem u2_regular_signed_kernel_translation_covariance_zero
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (z : Vec d) :
    ∃ hωz : IsRegular Λ (translate z ω), ∀ x : Vec d,
      u2RegularC0KernelSemigroup hd (translate z ω) lam Λ hΛ hωz 0 x =
        Measure.map (fun y : Vec d => y - z)
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω 0 (x + z)) := by
  refine ⟨(ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω, ?_⟩
  intro x
  rw [MarkovProcess.SubMarkovKernelSemigroup.kernel_zero,
    MarkovProcess.SubMarkovKernelSemigroup.kernel_zero, Kernel.id_apply, Kernel.id_apply,
    Measure.map_dirac' (by fun_prop)]
  congr 1
  abel

/-- An intertwiner of resolvents intertwines their bounded Yosida generators. -/
theorem u2_yosidaGenerator_intertwines {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : MarkovProcess.Semigroup.ContractiveResolvent E)
    (S : MarkovProcess.Semigroup.ContractiveResolvent F) (T : E →L[ℝ] F)
    (α : MarkovProcess.Semigroup.PositiveShift)
    (h : ∀ x, T (R.operator α x) = S.operator α (T x)) (x : E) :
    T (R.yosidaGenerator α x) = S.yosidaGenerator α (T x) := by
  simp only [MarkovProcess.Semigroup.ContractiveResolvent.yosidaGenerator,
    MarkovProcess.Semigroup.ContractiveResolvent.scaledOperator,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_smul, map_sub, h]

/-- Resolvent intertwining carries each bounded Yosida semigroup. -/
theorem u2_yosidaSemigroup_intertwines {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (R : MarkovProcess.Semigroup.ContractiveResolvent E)
    (S : MarkovProcess.Semigroup.ContractiveResolvent F) (T : E →L[ℝ] F)
    (α : MarkovProcess.Semigroup.PositiveShift)
    (h : ∀ x, T (R.operator α x) = S.operator α (T x)) (t : ℝ≥0) (x : E) :
    T (R.yosidaSemigroup α t x) = S.yosidaSemigroup α t (T x) := by
  let A := (t : ℝ) • R.yosidaGenerator α
  let B := (t : ℝ) • S.yosidaGenerator α
  have hp (n : ℕ) : T ((A ^ n) x) = (B ^ n) (T x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ', ContinuousLinearMap.mul_apply, A, B,
        ContinuousLinearMap.smul_apply, map_smul,
        u2_yosidaGenerator_intertwines R S T α h, ih]
  let u (n : ℕ) := ((n.factorial : ℝ)⁻¹) • (A ^ n) x
  let v (n : ℕ) := ((n.factorial : ℝ)⁻¹) • (B ^ n) (T x)
  have hsum (n : ℕ) : T (∑ k ∈ Finset.range n, u k) = ∑ k ∈ Finset.range n, v k := by
    simp only [map_sum, u, v, map_smul, hp]
  have hE := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).map
    (ContinuousLinearMap.apply ℝ _ x) (ContinuousLinearMap.continuous _)
  have hF := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) B).map
    (ContinuousLinearMap.apply ℝ _ (T x)) (ContinuousLinearMap.continuous _)
  have hlimE : Tendsto (fun n => ∑ k ∈ Finset.range n, u k) atTop
      (𝓝 (R.yosidaSemigroup α t x)) := by
    simpa [u, A, MarkovProcess.Semigroup.ContractiveResolvent.yosidaSemigroup_apply,
      MarkovProcess.Semigroup.ContractiveResolvent.yosidaOperator] using! hE.tendsto_sum_nat
  have hlimF : Tendsto (fun n => ∑ k ∈ Finset.range n, v k) atTop
      (𝓝 (S.yosidaSemigroup α t (T x))) := by
    simpa [v, B, MarkovProcess.Semigroup.ContractiveResolvent.yosidaSemigroup_apply,
      MarkovProcess.Semigroup.ContractiveResolvent.yosidaOperator] using! hF.tendsto_sum_nat
  apply tendsto_nhds_unique (T.continuous.tendsto _ |>.comp hlimE)
  change Tendsto (fun n => T (∑ k ∈ Finset.range n, u k)) atTop
    (𝓝 (S.yosidaSemigroup α t (T x)))
  simpa only [hsum] using hlimF

/-- Intertwining all resolvents intertwines their generated semigroups. -/
theorem u2_generatedSemigroup_intertwines {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (R : MarkovProcess.Semigroup.ContractiveResolvent E)
    (S : MarkovProcess.Semigroup.ContractiveResolvent F) (T : E →L[ℝ] F)
    (h : ∀ α x, T (R.operator α x) = S.operator α (T x)) (t : ℝ≥0) (x : E) :
    T (R.generatedSemigroup t x) = S.generatedSemigroup t (T x) := by
  apply tendsto_nhds_unique ((T.continuous.tendsto _).comp
    (R.tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup t x))
  change Tendsto (fun n => T (R.yosidaSemigroup
    (MarkovProcess.Semigroup.naturalShift n) t x)) atTop _
  simpa only [u2_yosidaSemigroup_intertwines R S T _ (h _) t x] using
    S.tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup t (T x)

/-- The actual physical weighted L² semigroups commute with translation. -/
theorem u2_physicalSemigroup_translate {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (z : Vec d)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure (translate z ω) hd lam)) :
    let e := MeasurableEquiv.addLeft z
    let c := ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd)))
    let hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    let hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      c • physicalReversibleMeasure ω hd lam :=
        u2_physical_reversible_measure_translate ω hd lam z
    u2LpCompSymmOfMapEqSmul e _ _ c hc ENNReal.ofReal_ne_top hm
      (Blueprint.gmpPhysicalSemigroup hd (translate z ω) lam Λ hΛ
        ((ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω) t f) =
    Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
      (u2LpCompSymmOfMapEqSmul e _ _ c hc ENNReal.ofReal_ne_top hm f) := by
  dsimp only
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  let c := ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd)))
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      c • physicalReversibleMeasure ω hd lam :=
    u2_physical_reversible_measure_translate ω hd lam z
  let T := u2LpCompSymmContinuousOfMapEqSmul e _ _ c hc ENNReal.ofReal_ne_top hm
  change T (Blueprint.gmpPhysicalSemigroup hd (translate z ω) lam Λ hΛ
    ((ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω) t f) =
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (T f)
  apply u2_generatedSemigroup_intertwines
  intro α g
  exact u2_physicalResolvent_translate hd ω lam Λ hΛ hω z α α.property g

/-- Compact continuous tests have pointwise translation-covariant C₀ evolutions. -/
theorem u2_regular_c0_compact_translate {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (z : Vec d)
    (t : ℝ≥0) (f : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (y : Vec d) :
    u2RegularC0Semigroup hd (translate z ω) lam Λ hΛ
      ((ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω) t
      (Blueprint.gmpPhysicalCompactC0 f hf hfc) (y - z) =
    u2RegularC0Semigroup hd ω lam Λ hΛ hω t
      (Blueprint.gmpPhysicalCompactC0 (fun y => f (y - z))
        (hf.comp (continuous_id.sub continuous_const))
        (by simpa [sub_eq_add_neg, Function.comp_def] using hfc.comp_homeomorph (Homeomorph.addRight (-z)))) y := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft z
  let c := ENNReal.ofReal (Real.exp (-2 * lam * z (firstCoordinateIndex hd)))
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hm : (physicalReversibleMeasure (translate z ω) hd lam).map e =
      c • physicalReversibleMeasure ω hd lam :=
    u2_physical_reversible_measure_translate ω hd lam z
  let T := u2LpCompSymmOfMapEqSmul e _ _ c hc ENNReal.ofReal_ne_top hm
  let hωz : IsRegular Λ (translate z ω) :=
    (ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω
  let g : Vec d → ℝ := fun y => f (y - z)
  have hg : Continuous g := hf.comp (continuous_id.sub continuous_const)
  have hgc : HasCompactSupport g := by
    simpa [g, sub_eq_add_neg, Function.comp_def] using hfc.comp_homeomorph (Homeomorph.addRight (-z))
  let f₀ := Blueprint.gmpPhysicalCompactC0 f hf hfc
  let g₀ := Blueprint.gmpPhysicalCompactC0 g hg hgc
  let F := (Blueprint.gmpPhysical_compactContinuous_memLp hd (translate z ω) lam f hf hfc).toLp f
  have hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure (translate z ω) hd lam] f₀ :=
    (Blueprint.gmpPhysical_compactContinuous_memLp hd (translate z ω) lam f hf hfc).coeFn_toLp
  have hTF : (T F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] g₀ := by
    have h1 := u2LpCompSymmOfMapEqSmul_coe e _ _ c hc ENNReal.ofReal_ne_top hm F
    have h2 := u2_ae_comp_symm_of_map_eq_smul e _ _ c hc hm hF
    filter_upwards [h1, h2] with x h1 h2
    simpa [T, e, g, g₀, f₀, Blueprint.gmpPhysicalCompactC0,
      EinsteinFull.Work.W5.gantertCompactObservable, sub_eq_add_neg, add_comm] using h1.trans h2
  have hp := u2_regular_semigroup_ae_of_memLp hd (translate z ω) lam Λ hΛ hωz t f₀ F hF
  have hpt := u2_ae_comp_symm_of_map_eq_smul e _ _ c hc hm hp
  have htc := u2LpCompSymmOfMapEqSmul_coe e _ _ c hc ENNReal.ofReal_ne_top hm
    (Blueprint.gmpPhysicalSemigroup hd (translate z ω) lam Λ hΛ hωz t F)
  have hq := u2_regular_semigroup_ae_of_memLp hd ω lam Λ hΛ hω t g₀ (T F) hTF
  have hs := u2_physicalSemigroup_translate hd ω lam Λ hΛ hω z t F
  have hae : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      u2RegularC0Semigroup hd (translate z ω) lam Λ hΛ hωz t f₀ (x - z) =
        u2RegularC0Semigroup hd ω lam Λ hΛ hω t g₀ x := by
    filter_upwards [hpt, htc, hq] with x hpt htc hq
    have htx := congrArg (fun v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) => v x) hs
    change T (Blueprint.gmpPhysicalSemigroup hd (translate z ω) lam Λ hΛ hωz t F) x =
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (T F) x at htx
    simpa [e, sub_eq_add_neg, add_comm] using hpt.symm.trans (htc.symm.trans (htx.trans hq))
  have hv : ∀ᵐ x ∂volume,
      u2RegularC0Semigroup hd (translate z ω) lam Λ hΛ hωz t f₀ (x - z) =
        u2RegularC0Semigroup hd ω lam Λ hΛ hω t g₀ x :=
    (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp hae
  have hclosed : IsClosed {x : Vec d |
      u2RegularC0Semigroup hd (translate z ω) lam Λ hΛ hωz t f₀ (x - z) =
        u2RegularC0Semigroup hd ω lam Λ hΛ hω t g₀ x} :=
    isClosed_eq (((u2RegularC0Semigroup hd (translate z ω) lam Λ hΛ hωz t f₀).continuous).comp
      (continuous_id.sub continuous_const))
      ((u2RegularC0Semigroup hd ω lam Λ hΛ hω t g₀).continuous)
  have hall := (hclosed.ae_eq_univ_iff_eq (μ := volume)).mp (ae_eq_univ.mpr hv)
  have hy : y ∈ {x : Vec d |
      u2RegularC0Semigroup hd (translate z ω) lam Λ hΛ hωz t f₀ (x - z) =
        u2RegularC0Semigroup hd ω lam Λ hΛ hω t g₀ x} := by rw [hall]; exact Set.mem_univ y
  exact hy

/-- The regular signed-force transition kernels commute with spatial translations. -/
theorem u2_regular_signed_kernel_translation_covariance
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (z : Vec d) :
    ∃ hωz : IsRegular Λ (translate z ω), ∀ (t : ℝ≥0) (x : Vec d),
      u2RegularC0KernelSemigroup hd (translate z ω) lam Λ hΛ hωz t x =
        Measure.map (fun y : Vec d => y - z)
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t (x + z)) := by
  let hωz := (ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω
  refine ⟨hωz, ?_⟩
  intro t x
  let : IsProbabilityMeasure (u2RegularC0KernelSemigroup hd (translate z ω) lam Λ hΛ hωz t x) :=
    ⟨u2_regular_kernel_conservative hd (translate z ω) lam Λ hΛ hωz t x⟩
  let : IsProbabilityMeasure (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t (x + z)) :=
    ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t (x + z)⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let g : Vec d → ℝ := fun y => f (y - z)
  have hg : Continuous g := f.continuous.comp (continuous_id.sub continuous_const)
  have hgc : HasCompactSupport g := by
    simpa [g, sub_eq_add_neg, Function.comp_def] using
      f.hasCompactSupport.comp_homeomorph (Homeomorph.addRight (-z))
  let f₀ := Blueprint.gmpPhysicalCompactC0 f f.continuous f.hasCompactSupport
  let g₀ := Blueprint.gmpPhysicalCompactC0 g hg hgc
  have he := u2_regular_c0_compact_translate hd ω lam Λ hΛ hω z t f
    f.continuous f.hasCompactSupport (x + z)
  have hnew := u2RegularC0KernelSemigroup_integral hd (translate z ω) lam Λ hΛ hωz t f₀ x
  have hold := u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω t g₀ (x + z)
  have hmap := integral_map (φ := fun y : Vec d => y - z) (f := (f : Vec d → ℝ))
    (μ := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t (x + z))
    (continuous_id.sub continuous_const).measurable.aemeasurable f.continuous.aestronglyMeasurable
  calc
    ∫ y, f y ∂(u2RegularC0KernelSemigroup hd (translate z ω) lam Λ hΛ hωz t x) =
        u2RegularC0Semigroup hd (translate z ω) lam Λ hΛ hωz t f₀ x := by
      simpa [f₀, Blueprint.gmpPhysicalCompactC0,
        EinsteinFull.Work.W5.gantertCompactObservable] using hnew
    _ = u2RegularC0Semigroup hd ω lam Λ hΛ hω t g₀ (x + z) := by
      simpa [f₀, g₀, g] using he
    _ = ∫ y, f (y - z) ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t (x + z)) := by
      simpa [g₀, g, Blueprint.gmpPhysicalCompactC0,
        EinsteinFull.Work.W5.gantertCompactObservable] using hold.symm
    _ = ∫ y, f y ∂(Measure.map (fun y : Vec d => y - z)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t (x + z))) := hmap.symm


/-- For the zero-potential reduced pair at zero force, the reversible
measure is Lebesgue measure. -/
theorem u2_unforced_reduced_reversible_measure {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) :
    physicalReversibleMeasure (zeroPotentialReducedPair ω) hd 0 =
      (volume : Measure (Vec d)) := by
  simp [physicalReversibleMeasure, physicalReversibleDensity, physicalForceWeight,
    clockDensity, zeroPotentialReducedPair_potential]

/-- The actual unforced regular kernel for the reduced coefficient preserves
Lebesgue measure. -/
theorem u2_unforced_reduced_kernel_volume_invariant {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ (zeroPotentialReducedPair ω)) (t : ℝ≥0) :
    (u2RegularC0KernelSemigroup hd (zeroPotentialReducedPair ω) 0 Λ hΛ hω t) ∘ₘ
      (volume : Measure (Vec d)) = volume := by
  simpa only [u2_unforced_reduced_reversible_measure] using
    u5_regular_kernel_invariant hd (zeroPotentialReducedPair ω) 0 Λ hΛ hω t

/-- The same unforced reduced kernel is reversible with respect to volume. -/
theorem u2_unforced_reduced_kernel_volume_reversible {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ (zeroPotentialReducedPair ω)) (t : ℝ≥0)
    (f g : Vec d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * (∫⁻ y, g y ∂u2RegularC0KernelSemigroup
      hd (zeroPotentialReducedPair ω) 0 Λ hΛ hω t x) ∂volume) =
    ∫⁻ x, g x * (∫⁻ y, f y ∂u2RegularC0KernelSemigroup
      hd (zeroPotentialReducedPair ω) 0 Λ hΛ hω t x) ∂volume := by
  simpa only [u2_unforced_reduced_reversible_measure] using
    u5_regular_kernel_full_reversibility hd (zeroPotentialReducedPair ω) 0 Λ hΛ hω t f g hf hg







/-- The supplied reduced martingale-problem kernel has the actual flat spatial
kernel as its endpoint marginal, simultaneously at every time. -/
theorem u2_supplied_unforced_kernel_regular_marginals
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω)) :
    ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
      ∀ t : ℝ≥0, (K ω).map (pathPosition t) =
        u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) 0
          (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
          (flatReducedEnvironment_regular Q.ellipticity_parameter hω) t 0 := by
  let hL := one_le_sourceReducedBound Q.ellipticity_parameter
  obtain ⟨L, hLmark, hLspec⟩ :=
    u2_foundation_unforced_origin_kernel_and_regular_marginals hd hL
      (flatReducedEnvironmentLaw Q)
  let : IsMarkovKernel L := hLmark
  let L' : Kernel (FieldPair d) (Path d) :=
    L.comap flatReducedEnvironment measurable_flatReducedEnvironment
  let : IsMarkovKernel L' := inferInstance
  have hspec : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (L' ω) ∧
      ∀ t : ℝ≥0, (L' ω).map (pathPosition t) =
        u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) 0
          (sourceReducedBound Λ₀) hL
          (flatReducedEnvironment_regular Q.ellipticity_parameter hω) t 0 := by
    have hpulled := ae_of_ae_map measurable_flatReducedEnvironment.aemeasurable
      (show ∀ᵐ ω ∂Q.measure.map flatReducedEnvironment, _ from hLspec)
    filter_upwards [hpulled] with ω hωreg hω
    have h := hωreg (flatReducedEnvironment_regular Q.ellipticity_parameter hω)
    have hgen : physicalGenerator (firstCoordinateIndex hd) (flatReducedEnvironment ω) 0 =
        reducedGenerator ⟨0, by omega⟩ ω 0 := by
      funext f x
      exact physicalGenerator_flatReducedEnvironment _ _ _ _ _
    constructor
    · change SolvesMartingaleProblem _ 0 (L (flatReducedEnvironment ω))
      rw [← hgen]
      exact h.1
    · exact h.2
  have hLmp : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (L' ω) := by
    filter_upwards [hspec, Q.regular] with ω h hω
    exact (h hω).1
  have heq := c17_unforced_environment_kernel_ae_unique (hpath := hpath) hd Q K L' hK hLmp
  filter_upwards [heq, hspec] with ω he hspecω hω t
  rw [he.1]
  exact (hspecω hω).2 t


/-- The supplied origin path law, translated to every spatial start. -/
def u2SuppliedSpatialKernel {d : ℕ} (K : Kernel (FieldPair d) (Path d))
    (t : ℝ≥0) : Kernel (FieldPair d × Vec d) (Vec d) :=
  let J := K.comap (fun p : FieldPair d × Vec d => translate p.2 p.1)
    (Probability.continuous_translate.measurable.comp (measurable_snd.prodMk measurable_fst))
  (Kernel.prod Kernel.id J).map (fun p : (FieldPair d × Vec d) × Path d => p.1.2 + p.2 t)

instance {d : ℕ} (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K] (t : ℝ≥0) :
    IsMarkovKernel (u2SuppliedSpatialKernel K t) := by
  unfold u2SuppliedSpatialKernel
  exact Kernel.IsMarkovKernel.map _
    ((measurable_snd.comp measurable_fst).add ((measurable_pathPosition t).comp measurable_snd))

/-- The translated kernel is literally the supplied endpoint law shifted by its start. -/
theorem u2_supplied_spatial_kernel_apply {d : ℕ}
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K] (t : ℝ≥0)
    (ω : FieldPair d) (x : Vec d) :
    u2SuppliedSpatialKernel K t (ω, x) =
      (K (translate x ω)).map (fun γ => x + γ t) := by
  have hm : Measurable (fun p : (FieldPair d × Vec d) × Path d => p.1.2 + p.2 t) :=
    (measurable_snd.comp measurable_fst).add ((measurable_pathPosition t).comp measurable_snd)
  have hm' : Measurable (fun γ : Path d => x + γ t) := measurable_const.add (measurable_pathPosition t)
  ext s hs
  rw [u2SuppliedSpatialKernel, Kernel.map_apply _ hm, Measure.map_apply hm hs,
    Kernel.id_prod_apply' _ _ (hs.preimage hm), Measure.map_apply hm' hs]
  rfl

/-- The original environment marginal is the translated reduced field under
the supplied all-start spatial kernel at the origin. -/
theorem u2_environment_kernel_eq_supplied_spatial_origin {d : ℕ}
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K] (t : ℝ≥0)
    (ω : FieldPair d) :
    c2EnvironmentKernel K t ω =
      (u2SuppliedSpatialKernel K t (ω, 0)).map (fun y => translate y (reduce ω)) := by
  rw [c2EnvironmentKernel_apply, u2_supplied_spatial_kernel_apply, translate_zero]
  simp only [zero_add]
  change Measure.map (fun γ : Path d => translate (pathPosition t γ) (reduce ω)) (K ω) =
    Measure.map (fun y : Vec d => translate y (reduce ω))
      (Measure.map (pathPosition t) (K ω))
  rw [Measure.map_map
    (show Measurable (fun y : Vec d => translate y (reduce ω)) from
      Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
    (measurable_pathPosition t)]
  rfl


/-- Translation covariance holds pointwise for the spatial kernel built from
any supplied origin kernel, including on exceptional environments. -/
theorem u2_supplied_spatial_kernel_translate {d : ℕ}
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K] (t : ℝ≥0)
    (ω : FieldPair d) (x z : Vec d) :
    u2SuppliedSpatialKernel K t (translate z ω, x) =
      (u2SuppliedSpatialKernel K t (ω, x + z)).map (fun y : Vec d => y - z) := by
  rw [u2_supplied_spatial_kernel_apply, u2_supplied_spatial_kernel_apply, translate_add]
  rw [Measure.map_map
    (show Measurable (fun y : Vec d => y - z) from measurable_id.sub measurable_const)
    (show Measurable (fun γ : Path d => (x + z) + γ t) from
      measurable_const.add (measurable_pathPosition t))]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun γ => by
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]


/-- For each spatial start, the measurable kernel obtained from the supplied
origin law agrees almost surely with the actual unforced regular semigroup. -/
theorem u2_supplied_spatial_kernel_eq_regular_ae
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (x : Vec d) :
    ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω, ∀ t : ℝ≥0,
      u2SuppliedSpatialKernel K t (ω, x) =
        u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) 0
          (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
          (flatReducedEnvironment_regular Q.ellipticity_parameter hω) t x := by
  have hbase := u2_supplied_unforced_kernel_regular_marginals (hpath := hpath) hd Q K hK
  have hshift := (measurePreserving_translate Q.measure Q.stationary x).quasiMeasurePreserving.ae hbase
  filter_upwards [hshift] with ω hωshift hω t
  have hregshift : IsRegular Λ₀ (translate x ω) :=
    (ActualImageLpStateTransport.isRegular_translate_iff x ω).mpr hω
  have hflat := flatReducedEnvironment_regular Q.ellipticity_parameter hω
  obtain ⟨hflatshift, hcov⟩ := u2_regular_signed_kernel_translation_covariance
    hd (flatReducedEnvironment ω) 0 (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) hflat x
  have hmarg : (K (translate x ω)).map (pathPosition t) =
      u2RegularC0KernelSemigroup hd (translate x (flatReducedEnvironment ω)) 0
        (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        hflatshift t 0 := by
    simpa only [flatReducedEnvironment_translate] using hωshift hregshift t
  rw [u2_supplied_spatial_kernel_apply]
  have hmap : (K (translate x ω)).map (fun γ => x + γ t) =
      ((K (translate x ω)).map (pathPosition t)).map (fun y : Vec d => x + y) := by
    rw [Measure.map_map (show Measurable (fun y : Vec d => x + y) from
      measurable_const.add measurable_id) (measurable_pathPosition t)]
    rfl
  rw [hmap, hmarg, hcov t 0]
  simp only [zero_add]
  rw [Measure.map_map (show Measurable (fun y : Vec d => x + y) from
    measurable_const.add measurable_id)
    (show Measurable (fun y : Vec d => y - x) from measurable_id.sub measurable_const)]
  simp [Function.comp_def, sub_eq_add_neg]

/-- A full event under a stationary environment law holds along almost every
point of almost every spatial orbit, even when the event itself is not measurable. -/
theorem u2_stationary_full_event_spatial_orbit {d : ℕ}
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) {p : FieldPair d → Prop}
    (hp : ∀ᵐ ω ∂Q.measure, p ω) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ x : Vec d ∂volume, p (translate x ω) := by
  obtain ⟨N, hsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  have hN : ∀ᵐ ω ∂Q.measure, ω ∉ N := by
    apply ae_iff.mpr
    simpa using hNzero
  have horbit : ∀ᵐ ω ∂Q.measure, ∀ᵐ x : Vec d ∂volume, translate x ω ∉ N := by
    apply (Measure.ae_ae_comm (μ := volume) (ν := Q.measure)
      (p := fun x ω => translate x ω ∉ N)
      (hNm.preimage Probability.continuous_translate.measurable).compl).mp
    exact Filter.Eventually.of_forall fun x =>
      (measurePreserving_translate Q.measure Q.stationary x).quasiMeasurePreserving.ae hN
  filter_upwards [horbit] with ω hω
  filter_upwards [hω] with x hx
  by_contra hbad
  exact hx (hsub hbad)

/-- On almost every environment, the supplied spatial kernel agrees with the
regular kernel at almost every spatial start, simultaneously at all times. -/
theorem u2_supplied_spatial_kernel_eq_regular_orbit_ae
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω)) :
    ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω, ∀ᵐ x : Vec d ∂volume, ∀ t : ℝ≥0,
      u2SuppliedSpatialKernel K t (ω, x) =
        u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) 0
          (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
          (flatReducedEnvironment_regular Q.ellipticity_parameter hω) t x := by
  have hbase := u2_supplied_unforced_kernel_regular_marginals (hpath := hpath) hd Q K hK
  have horbit := u2_stationary_full_event_spatial_orbit Q hbase
  filter_upwards [horbit] with ω hωshift hω
  filter_upwards [hωshift] with x hx t
  have hregshift : IsRegular Λ₀ (translate x ω) :=
    (ActualImageLpStateTransport.isRegular_translate_iff x ω).mpr hω
  have hflat := flatReducedEnvironment_regular Q.ellipticity_parameter hω
  obtain ⟨hflatshift, hcov⟩ := u2_regular_signed_kernel_translation_covariance
    hd (flatReducedEnvironment ω) 0 (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) hflat x
  have hmarg : (K (translate x ω)).map (pathPosition t) =
      u2RegularC0KernelSemigroup hd (translate x (flatReducedEnvironment ω)) 0
        (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        hflatshift t 0 := by
    simpa only [flatReducedEnvironment_translate] using hx hregshift t
  rw [u2_supplied_spatial_kernel_apply]
  have hmap : (K (translate x ω)).map (fun γ => x + γ t) =
      ((K (translate x ω)).map (pathPosition t)).map (fun y : Vec d => x + y) := by
    rw [Measure.map_map (show Measurable (fun y : Vec d => x + y) from
      measurable_const.add measurable_id) (measurable_pathPosition t)]
    rfl
  rw [hmap, hmarg, hcov t 0]
  simp only [zero_add]
  rw [Measure.map_map (show Measurable (fun y : Vec d => x + y) from
    measurable_const.add measurable_id)
    (show Measurable (fun y : Vec d => y - x) from measurable_id.sub measurable_const)]
  simp [Function.comp_def, sub_eq_add_neg]

/-- The all-start kernel constructed from the supplied origin law preserves
Lebesgue measure, on one full environment event and for every time. -/
theorem u2_supplied_spatial_kernel_volume_invariant
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω)) :
    ∀ᵐ ω ∂Q.measure, ∀ t : ℝ≥0,
      ((u2SuppliedSpatialKernel K t).comap (fun x => (ω, x))
        (measurable_const.prodMk measurable_id)) ∘ₘ (volume : Measure (Vec d)) = volume := by
  have horbit := u2_supplied_spatial_kernel_eq_regular_orbit_ae (hpath := hpath) hd Q K hK
  filter_upwards [horbit, Q.regular] with ω horbitω hω t
  let hflat := flatReducedEnvironment_regular Q.ellipticity_parameter hω
  have heq : ∀ᵐ x : Vec d ∂volume,
      (u2SuppliedSpatialKernel K t).comap (fun x => (ω, x))
          (measurable_const.prodMk measurable_id) x =
        u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) 0
          (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
          hflat t x := (horbitω hω).mono fun x hx => hx t
  calc
    _ = (u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) 0
        (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        hflat t) ∘ₘ (volume : Measure (Vec d)) := Measure.comp_congr heq
    _ = volume := u2_unforced_reduced_kernel_volume_invariant hd ω
        (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hflat t





/-- Stationarity and pointwise spatial covariance shift an annealed endpoint
integral to any prescribed starting point. -/
theorem u2_supplied_spatial_kernel_annealed_shift {d : ℕ}
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (t : ℝ≥0) (x : Vec d) (f : FieldPair d → ℝ≥0∞) (g : Vec d → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ ω, ∫⁻ y, f (translate y (reduce ω)) * g y
      ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure) =
    ∫⁻ ω, ∫⁻ y, f (translate y (reduce ω)) * g (y - x)
      ∂u2SuppliedSpatialKernel K t (ω, x) ∂Q.measure := by
  let J : Kernel (FieldPair d) (Vec d) :=
    (u2SuppliedSpatialKernel K t).comap (fun ω => (ω, 0))
      (measurable_id.prodMk measurable_const)
  let F : FieldPair d × Vec d → ℝ≥0∞ :=
    fun p => f (translate p.2 (reduce p.1)) * g p.2
  have hF : Measurable F := by
    apply Measurable.mul
    · exact hf.comp (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (Probability.measurable_reduce.comp measurable_fst)))
    · exact hg.comp measurable_snd
  let G : FieldPair d → ℝ≥0∞ := fun ω => ∫⁻ y, F (ω, y) ∂J ω
  have hG : Measurable G := hF.lintegral_kernel_prod_right
  calc
    _ = ∫⁻ ω, G (translate x ω) ∂Q.measure :=
      ((measurePreserving_translate Q.measure Q.stationary x).lintegral_comp hG).symm
    _ = _ := by
      apply lintegral_congr
      intro ω
      change (∫⁻ y, f (translate y (reduce (translate x ω))) * g y
        ∂u2SuppliedSpatialKernel K t (translate x ω, 0)) = _
      rw [u2_supplied_spatial_kernel_translate, zero_add,
        lintegral_map (by exact (hf.comp (Probability.continuous_translate.measurable.comp
          (measurable_id.prodMk measurable_const))).mul hg)
          (show Measurable (fun y : Vec d => y - x) from
            measurable_id.sub measurable_const)]
      apply lintegral_congr
      intro y
      simp [reduce_translate, translate_add, sub_eq_add_neg, add_comm]


/-- A measurable nonnegative spatial weight whose every translate has unit
Lebesgue integral. -/
theorem u2_exists_normalized_spatial_weight (d : ℕ) :
    ∃ g : Vec d → ℝ≥0∞, Measurable g ∧
      ∀ y : Vec d, ∫⁻ x, g (y + x) ∂volume = 1 := by
  let B : Set (Vec d) := Metric.ball 0 1
  let c : ℝ≥0∞ := (volume B)⁻¹
  let g : Vec d → ℝ≥0∞ := B.indicator (fun _ => c)
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hpos : volume B ≠ 0 := (Metric.measure_ball_pos volume (0 : Vec d) zero_lt_one).ne'
  have hfin : volume B ≠ ∞ := (measure_ball_lt_top (μ := (volume : Measure (Vec d)))
    (x := 0) (r := 1)).ne
  have hg : Measurable g := measurable_const.indicator hB
  have hnorm : (∫⁻ x, g x ∂volume) = 1 := by
    dsimp [g, c]
    rw [lintegral_indicator hB, lintegral_const, Measure.restrict_apply_univ]
    simpa only [mul_comm] using ENNReal.mul_inv_cancel hpos hfin
  refine ⟨g, hg, ?_⟩
  intro y
  calc
    _ = ∫⁻ x, g x ∂volume :=
      (measurePreserving_add_left (volume : Measure (Vec d)) y).lintegral_comp hg
    _ = 1 := hnorm


/-- A unit-integral spatial weight averages out of any endpoint integral. -/
theorem u2_supplied_spatial_origin_weight_average {d : ℕ}
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (t : ℝ≥0) (ω : FieldPair d) (f : FieldPair d → ℝ≥0∞)
    (g : Vec d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hnorm : ∀ y : Vec d, ∫⁻ x, g (y + x) ∂volume = 1) :
    (∫⁻ x, ∫⁻ y, f (translate y (reduce ω)) * g (y + x)
      ∂u2SuppliedSpatialKernel K t (ω, 0) ∂volume) =
    ∫⁻ y, f (translate y (reduce ω)) ∂u2SuppliedSpatialKernel K t (ω, 0) := by
  have hm : Measurable (fun p : Vec d × Vec d =>
      f (translate p.2 (reduce ω)) * g (p.2 + p.1)) := by
    apply Measurable.mul
    · exact hf.comp (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk measurable_const))
    · exact hg.comp (measurable_snd.add measurable_fst)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro y
  rw [lintegral_const_mul _ (show Measurable (fun x : Vec d => g (y + x)) from
    hg.comp (measurable_const.add measurable_id)), hnorm, mul_one]

/-- The supplied all-start kernel's volume invariance applies to arbitrary
nonnegative measurable endpoint functions. -/
theorem u2_supplied_spatial_kernel_lintegral_volume_invariant
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (t : ℝ≥0) (f : FieldPair d → ℝ≥0∞) (g : Vec d → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    ∀ᵐ ω ∂Q.measure,
      (∫⁻ x, ∫⁻ y, f (translate y (reduce ω)) * g y
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂volume) =
      ∫⁻ y, f (translate y (reduce ω)) * g y ∂volume := by
  filter_upwards [u2_supplied_spatial_kernel_volume_invariant (hpath := hpath) hd Q K hK] with ω hω
  let J : Kernel (Vec d) (Vec d) :=
    (u2SuppliedSpatialKernel K t).comap (fun x => (ω, x))
      (measurable_const.prodMk measurable_id)
  have hF : Measurable (fun y : Vec d => f (translate y (reduce ω)) * g y) :=
    (hf.comp (Probability.continuous_translate.measurable.comp
      (measurable_id.prodMk measurable_const))).mul hg
  change (∫⁻ x, ∫⁻ y, f (translate y (reduce ω)) * g y ∂J x ∂volume) = _
  rw [← Measure.lintegral_bind J.aemeasurable hF.aemeasurable, hω t]



/-- Stationarity removes a normalized spatial average of the reduced orbit. -/
theorem u2_stationary_reduced_orbit_weight_average {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : FieldPair d → ℝ≥0∞)
    (g : Vec d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hnorm : ∀ y : Vec d, ∫⁻ x, g (y + x) ∂volume = 1) :
    (∫⁻ ω, ∫⁻ y, f (translate y (reduce ω)) * g y ∂volume ∂Q.measure) =
      ∫⁻ ω, f (reduce ω) ∂Q.measure := by
  have hm : Measurable (fun p : FieldPair d × Vec d =>
      f (translate p.2 (reduce p.1)) * g p.2) := by
    apply Measurable.mul
    · exact hf.comp (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (Probability.measurable_reduce.comp measurable_fst)))
    · exact hg.comp measurable_snd
  have hred : Measurable (fun ω => f (reduce ω)) := hf.comp Probability.measurable_reduce
  have hs (y : Vec d) :
      (∫⁻ ω, f (translate y (reduce ω)) ∂Q.measure) =
        ∫⁻ ω, f (reduce ω) ∂Q.measure := by
    simpa only [Function.comp_def, reduce_translate] using
      (measurePreserving_translate Q.measure Q.stationary y).lintegral_comp hred
  have hzero : (∫⁻ y, g y ∂volume) = 1 := by simpa only [zero_add] using hnorm 0
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ = ∫⁻ y, (∫⁻ ω, f (translate y (reduce ω)) ∂Q.measure) * g y ∂volume := by
      apply lintegral_congr
      intro y
      rw [lintegral_mul_const _ (show Measurable (fun ω : FieldPair d =>
        f (translate y (reduce ω))) from hf.comp
        (Probability.continuous_translate.measurable.comp
          (measurable_const.prodMk Probability.measurable_reduce)))]
    _ = ∫⁻ y, (∫⁻ ω, f (reduce ω) ∂Q.measure) * g y ∂volume := by
      apply lintegral_congr
      intro y
      rw [hs]
    _ = _ := by rw [lintegral_const_mul _ hg, hzero, mul_one]



/-- Mass transport for the actual supplied origin law and nonnegative tests. -/
theorem u2_supplied_spatial_origin_annealed_invariant
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (t : ℝ≥0) (f : FieldPair d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∫⁻ y, f (translate y (reduce ω))
      ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure) =
      ∫⁻ ω, f (reduce ω) ∂Q.measure := by
  obtain ⟨g, hg, hnorm⟩ := u2_exists_normalized_spatial_weight d
  let J : Kernel (Vec d × FieldPair d) (Vec d) :=
    (u2SuppliedSpatialKernel K t).comap (fun p => (p.2, 0))
      (measurable_snd.prodMk measurable_const)
  let J' : Kernel (Vec d × FieldPair d) (Vec d) :=
    (u2SuppliedSpatialKernel K t).comap (fun p => (p.2, p.1))
      (measurable_snd.prodMk measurable_fst)
  have hF : Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      f (translate p.2 (reduce p.1.2)) * g (p.2 + p.1.1)) := by
    apply Measurable.mul
    · exact hf.comp (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (Probability.measurable_reduce.comp
          (measurable_snd.comp measurable_fst))))
    · exact hg.comp (measurable_snd.add (measurable_fst.comp measurable_fst))
  have hF' : Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      f (translate p.2 (reduce p.1.2)) * g p.2) := by
    apply Measurable.mul
    · exact hf.comp (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (Probability.measurable_reduce.comp
          (measurable_snd.comp measurable_fst))))
    · exact hg.comp measurable_snd
  have hA : Measurable (fun p : Vec d × FieldPair d => ∫⁻ y,
      f (translate y (reduce p.2)) * g (y + p.1) ∂J p) :=
    hF.lintegral_kernel_prod_right
  have hB : Measurable (fun p : Vec d × FieldPair d => ∫⁻ y,
      f (translate y (reduce p.2)) * g y ∂J' p) :=
    hF'.lintegral_kernel_prod_right
  calc
    _ = ∫⁻ ω, ∫⁻ x, ∫⁻ y, f (translate y (reduce ω)) * g (y + x)
        ∂u2SuppliedSpatialKernel K t (ω, 0) ∂volume ∂Q.measure := by
      apply lintegral_congr
      intro ω
      exact (u2_supplied_spatial_origin_weight_average K t ω f g hf hg hnorm).symm
    _ = ∫⁻ x, ∫⁻ ω, ∫⁻ y, f (translate y (reduce ω)) * g (y + x)
        ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure ∂volume :=
      lintegral_lintegral_swap (hA.comp (measurable_snd.prodMk measurable_fst)).aemeasurable
    _ = ∫⁻ x, ∫⁻ ω, ∫⁻ y, f (translate y (reduce ω)) * g y
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂Q.measure ∂volume := by
      apply lintegral_congr
      intro x
      have h := u2_supplied_spatial_kernel_annealed_shift Q K t x f
        (fun y => g (y + x)) hf (show Measurable (fun y => g (y + x)) from
          hg.comp (measurable_id.add measurable_const))
      simpa only [sub_add_cancel] using h
    _ = ∫⁻ ω, ∫⁻ x, ∫⁻ y, f (translate y (reduce ω)) * g y
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂volume ∂Q.measure :=
      (lintegral_lintegral_swap (show AEMeasurable
        (Function.uncurry (fun (ω : FieldPair d) (x : Vec d) => ∫⁻ y,
          f (translate y (reduce ω)) * g y ∂u2SuppliedSpatialKernel K t (ω, x)))
        (Q.measure.prod volume) from
        (hB.comp (measurable_snd.prodMk measurable_fst)).aemeasurable)).symm
    _ = ∫⁻ ω, ∫⁻ y, f (translate y (reduce ω)) * g y ∂volume ∂Q.measure :=
      lintegral_congr_ae (u2_supplied_spatial_kernel_lintegral_volume_invariant
        (hpath := hpath) hd Q K hK t f g hf hg)
    _ = _ := u2_stationary_reduced_orbit_weight_average Q f g hf hg hnorm



/-- The supplied unforced environment marginal preserves the reduced law. -/
theorem u2_unforced_environment_invariant_by_covariance
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω)) :
    ∀ t : ℝ≥0, c2EnvironmentKernel K t ∘ₘ Q.measure = reducedLaw Q := by
  intro t
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  change (∫⁻ ω, c2EnvironmentKernel K t ω s ∂Q.measure) = (Q.measure.map reduce) s
  let f : FieldPair d → ℝ≥0∞ := s.indicator 1
  have hf : Measurable f := measurable_const.indicator hs
  have hpoint (ω : FieldPair d) :
      (∫⁻ y, f (translate y (reduce ω)) ∂u2SuppliedSpatialKernel K t (ω, 0)) =
        c2EnvironmentKernel K t ω s := by
    rw [← lintegral_map hf (show Measurable (fun y : Vec d => translate y (reduce ω)) from
      Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)),
      ← u2_environment_kernel_eq_supplied_spatial_origin]
    simpa only [f] using (lintegral_indicator_one (μ := c2EnvironmentKernel K t ω) hs)
  calc
    _ = ∫⁻ ω, ∫⁻ y, f (translate y (reduce ω))
        ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure := by
      apply lintegral_congr
      intro ω
      exact (hpoint ω).symm
    _ = ∫⁻ ω, f (reduce ω) ∂Q.measure :=
      u2_supplied_spatial_origin_annealed_invariant (hpath := hpath) hd Q K hK t f hf
    _ = _ := by
      rw [← lintegral_map hf Probability.measurable_reduce]
      simpa only [f] using (lintegral_indicator_one (μ := Q.measure.map reduce) hs)



/-- The same supplied path law gives an invariant kernel on the reduced carrier. -/
theorem u2_reduced_environment_kernel_invariant
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) (t : ℝ≥0) :
    c2ReducedEnvironmentKernel K D hD t ∘ₘ reducedLaw Q = reducedLaw Q := by
  rw [c2ReducedEnvironmentKernel_comp Q K D hD hleft]
  exact u2_unforced_environment_invariant_by_covariance (hpath := hpath) hd Q K hK t

/-- The actual reduced environment kernel preserves real L². -/
theorem u2_reduced_environment_kernel_memLp
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) (t : ℝ≥0)
    {f : FieldPair d → ℝ} (hf : MemLp f 2 (reducedLaw Q)) :
    MemLp (MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) f)
      2 (reducedLaw Q) := by
  apply MarkovProcess.MemLp.kernelIntegral
    (MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel _) _ (by norm_num) hf
  exact le_of_eq (u2_reduced_environment_kernel_invariant (hpath := hpath) hd Q K hK D hD hleft t)



/-- Invariance gives the same supplied path kernel a contractive real L² action,
with its physical path representation on the original environment law. -/
theorem u2_unforced_reduced_kernel_L2_action
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (t : ℝ≥0) :
    ∃ T : Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q),
      ‖T‖ ≤ 1 ∧ ∀ F : Lp ℝ 2 (reducedLaw Q),
        ∀ᵐ ω ∂Q.measure, T F (reduce ω) =
          ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂K ω := by
  obtain ⟨D, hD, hleft⟩ := Probability.exists_measurable_leftInverse_reduce d
  let R := c2ReducedEnvironmentKernel K D hD t
  have hR : MarkovProcess.IsSubMarkovKernel R :=
    MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel R
  have hμ : R ∘ₘ reducedLaw Q ≤ reducedLaw Q :=
    le_of_eq (u2_reduced_environment_kernel_invariant (hpath := hpath) hd Q K hK D hD hleft t)
  letI : Fact (1 ≤ (2 : ℝ≥0)) := ⟨by norm_num⟩
  let T : Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q) :=
    MarkovProcess.kernelLpFinite (reducedLaw Q) R hR hμ 2
  refine ⟨T, MarkovProcess.norm_kernelLpFinite_le _ _ _ _ _, ?_⟩
  intro F
  have ha := MarkovProcess.coeFn_kernelLpFinite (reducedLaw Q) R hR hμ 2 F
  have ha' : ∀ᵐ ω ∂Q.measure, T F (reduce ω) =
      MarkovProcess.kernelIntegral R F (reduce ω) :=
    (Probability.measurableEmbedding_reduce d).ae_map_iff.mp ha
  filter_upwards [ha'] with ω hω
  rw [hω]
  change (∫ ρ, F ρ ∂c2ReducedEnvironmentKernel K D hD t (reduce ω)) = _
  rw [c2ReducedEnvironmentKernel_pullback K D hD hleft, c2EnvironmentKernel_apply]
  have hm : Measurable (fun γ : Path d => translate (γ t) (reduce ω)) :=
    (measurable_c2EnvironmentAt t).comp (measurable_const.prodMk measurable_id)
  exact integral_map hm.aemeasurable (Lp.stronglyMeasurable F).aestronglyMeasurable


/-- The full annealed path law has the reduced law as its environment
marginal at every time. -/
theorem u2_supplied_annealed_environment_marginal
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (t : ℝ≥0) :
    Measure.map (fun z : FieldPair d × Path d => translate (z.2 t) (reduce z.1))
      (Q.measure ⊗ₘ K) = reducedLaw Q := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  change Measure.map (c2EnvironmentAt t) (Q.measure ⊗ₘ K) = _
  rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ (measurable_c2EnvironmentAt t)]
  exact u2_unforced_environment_invariant_by_covariance (hpath := hpath) hd Q K hK t


/-- Invariance bounds the discounted occupation of every square-integrable
observation for the same supplied path kernel. -/
theorem u2_supplied_discounted_occupation_L2_bound
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (s : ℝ) (hs : 0 < s) :
    ∀ (r : FieldPair d → ℝ), Measurable r → ∀ hr : MemLp r 2 (reducedLaw Q),
      Integrable (fun p : ℝ × (FieldPair d × Path d) => Real.exp (-s * p.1) *
        |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
        ((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K)) ∧
      (∫ ω, (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        (∫ γ : Path d, |r (translate (γ t.toNNReal) (reduce ω))| ∂K ω)) ∂Q.measure)
          ≤ s⁻¹ * ‖hr.toLp r‖ := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  apply c22_discounted_occupation_L2_of_bounded_tests Q K s hs s⁻¹ (inv_nonneg.mpr hs.le)
  intro r hm ⟨B, hB⟩ hr
  have hi := c17_integrable_discounted_occupation_of_bounded Q K r hm B hB s hs
  have hn : (∫ w, |r w| ∂reducedLaw Q) ≤ ‖hr.toLp r‖ := by
    simp_rw [← Real.norm_eq_abs]
    rw [integral_norm_eq_lintegral_enorm hr.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm hr.aestronglyMeasurable, Lp.norm_toLp]
    exact ENNReal.toReal_mono hr.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hslice (t : ℝ) :
      (∫ z : FieldPair d × Path d,
        |r (translate (z.2 t.toNNReal) (reduce z.1))| ∂(Q.measure ⊗ₘ K)) =
      ∫ w, |r w| ∂reducedLaw Q := by
    have he := integral_map (μ := Q.measure ⊗ₘ K)
      (measurable_c2EnvironmentAt t.toNNReal).aemeasurable
      ((continuous_abs.measurable.comp hm).aestronglyMeasurable)
    have hmarg := u2_supplied_annealed_environment_marginal (hpath := hpath) hd Q K hK
      t.toNNReal
    change Measure.map (c2EnvironmentAt t.toNNReal) (Q.measure ⊗ₘ K) = reducedLaw Q at hmarg
    rw [hmarg] at he
    exact he.symm
  have hexp : (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t)) = s⁻¹ := by
    rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hs)]
    simp
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) * (∫ w, |r w| ∂reducedLaw Q) := by
      rw [integral_prod _ hi]
      simp_rw [integral_const_mul, hslice]
    _ = s⁻¹ * (∫ w, |r w| ∂reducedLaw Q) := by rw [integral_mul_const, hexp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hs.le)


/-- The supplied path kernel defines one contractive operator family, with
identity at time zero. -/
theorem u2_unforced_reduced_kernel_L2_family_zero
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω)) :
    ∃ T : ℝ≥0 → Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q),
      (∀ t, ‖T t‖ ≤ 1) ∧
      (∀ t F, ∀ᵐ ω ∂Q.measure, T t F (reduce ω) =
        ∫ γ : Path d, F (translate (γ t) (reduce ω)) ∂K ω) ∧
      ∀ F, T 0 F = F := by
  choose T hnorm hrep using fun t =>
    u2_unforced_reduced_kernel_L2_action (hpath := hpath) hd Q K hK t
  refine ⟨T, hnorm, hrep, ?_⟩
  intro F
  apply Lp.ext
  apply (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr
  filter_upwards [hrep 0 F, hK] with ω hω hmp
  rw [hω]
  calc
    _ = ∫ _γ : Path d, F (reduce ω) ∂K ω := by
      apply integral_congr_ae
      filter_upwards [hmp.2.1] with γ hγ
      simp only [hγ, translate_zero]
    _ = F (reduce ω) := by simp



/-- The supplied all-start kernel is reversible for Lebesgue measure on
almost every environment, for all nonnegative measurable spatial tests. -/
theorem u2_supplied_spatial_kernel_volume_reversible
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω)) :
    ∀ᵐ ω ∂Q.measure, ∀ t : ℝ≥0, ∀ f g : Vec d → ℝ≥0∞,
      Measurable f → Measurable g →
      (∫⁻ x, f x * (∫⁻ y, g y ∂u2SuppliedSpatialKernel K t (ω, x)) ∂volume) =
      ∫⁻ x, g x * (∫⁻ y, f y ∂u2SuppliedSpatialKernel K t (ω, x)) ∂volume := by
  filter_upwards [u2_supplied_spatial_kernel_eq_regular_orbit_ae (hpath := hpath) hd Q K hK,
    Q.regular] with ω horbit hω t f g hf hg
  let hflat := flatReducedEnvironment_regular Q.ellipticity_parameter hω
  have heq : ∀ᵐ x : Vec d ∂volume,
      u2SuppliedSpatialKernel K t (ω, x) =
        u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) 0
          (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
          hflat t x := (horbit hω).mono fun x hx => hx t
  calc
    _ = ∫⁻ x, f x * (∫⁻ y, g y ∂u2RegularC0KernelSemigroup hd
        (flatReducedEnvironment ω) 0 (sourceReducedBound Λ₀)
        (one_le_sourceReducedBound Q.ellipticity_parameter) hflat t x) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    _ = ∫⁻ x, g x * (∫⁻ y, f y ∂u2RegularC0KernelSemigroup hd
        (flatReducedEnvironment ω) 0 (sourceReducedBound Λ₀)
        (one_le_sourceReducedBound Q.ellipticity_parameter) hflat t x) ∂volume :=
      u2_unforced_reduced_kernel_volume_reversible hd ω (sourceReducedBound Λ₀)
        (one_le_sourceReducedBound Q.ellipticity_parameter) hflat t f g hf hg
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]



/-- Stationarity moves both endpoints of an annealed transition by the
same spatial displacement. -/
theorem u2_supplied_spatial_kernel_annealed_pair_shift {d : ℕ}
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (t : ℝ≥0) (x : Vec d) (f h : FieldPair d → ℝ≥0∞) (g : Vec d → ℝ≥0∞)
    (hf : Measurable f) (hh : Measurable h) (hg : Measurable g) :
    (∫⁻ ω, ∫⁻ y, f (reduce ω) * h (translate y (reduce ω)) * g y
      ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure) =
    ∫⁻ ω, ∫⁻ y, f (translate x (reduce ω)) * h (translate y (reduce ω)) * g (y - x)
      ∂u2SuppliedSpatialKernel K t (ω, x) ∂Q.measure := by
  let J : Kernel (FieldPair d) (Vec d) :=
    (u2SuppliedSpatialKernel K t).comap (fun ω => (ω, 0))
      (measurable_id.prodMk measurable_const)
  let F : FieldPair d × Vec d → ℝ≥0∞ :=
    fun p => f (reduce p.1) * h (translate p.2 (reduce p.1)) * g p.2
  have hF : Measurable F := by
    apply Measurable.mul
    · apply Measurable.mul
      · exact hf.comp (Probability.measurable_reduce.comp measurable_fst)
      · exact hh.comp (Probability.continuous_translate.measurable.comp
          (measurable_snd.prodMk (Probability.measurable_reduce.comp measurable_fst)))
    · exact hg.comp measurable_snd
  let G : FieldPair d → ℝ≥0∞ := fun ω => ∫⁻ y, F (ω, y) ∂J ω
  have hG : Measurable G := hF.lintegral_kernel_prod_right
  calc
    _ = ∫⁻ ω, G (translate x ω) ∂Q.measure :=
      ((measurePreserving_translate Q.measure Q.stationary x).lintegral_comp hG).symm
    _ = _ := by
      apply lintegral_congr
      intro ω
      change (∫⁻ y, f (reduce (translate x ω)) *
        h (translate y (reduce (translate x ω))) * g y
        ∂u2SuppliedSpatialKernel K t (translate x ω, 0)) = _
      rw [u2_supplied_spatial_kernel_translate, zero_add,
        lintegral_map (by
          exact (measurable_const.mul
            (hh.comp (Probability.continuous_translate.measurable.comp
              (measurable_id.prodMk measurable_const)))).mul hg)
          (show Measurable (fun y : Vec d => y - x) from
            measurable_id.sub measurable_const)]
      apply lintegral_congr
      intro y
      simp [reduce_translate, translate_add, sub_eq_add_neg, add_comm]



/-- Reversibility moves an endpoint weight from the destination to the
starting point. -/
theorem u2_supplied_spatial_kernel_weighted_reversible
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω)) :
    ∀ᵐ ω ∂Q.measure, ∀ t : ℝ≥0, ∀ f h g : Vec d → ℝ≥0∞,
      Measurable f → Measurable h → Measurable g →
      (∫⁻ x, ∫⁻ y, f x * h y * g y
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂volume) =
      ∫⁻ x, ∫⁻ y, h x * f y * g x
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂volume := by
  filter_upwards [u2_supplied_spatial_kernel_volume_reversible (hpath := hpath) hd Q K hK] with ω hω
  intro t f h g hf hh hg
  calc
    _ = ∫⁻ x, f x * (∫⁻ y, (h * g) y ∂u2SuppliedSpatialKernel K t (ω, x))
        ∂volume := by
      apply lintegral_congr
      intro x
      simp_rw [mul_assoc]
      exact lintegral_const_mul _ (hh.mul hg)
    _ = ∫⁻ x, (h * g) x * (∫⁻ y, f y ∂u2SuppliedSpatialKernel K t (ω, x))
        ∂volume := hω t f (h * g) hf (hh.mul hg)
    _ = _ := by
      apply lintegral_congr
      intro x
      change h x * g x * (∫⁻ y, f y ∂u2SuppliedSpatialKernel K t (ω, x)) = _
      rw [← lintegral_const_mul _ hf]
      apply lintegral_congr
      intro y
      ac_rfl



/-- A normalized average of starting points leaves the annealed two-point
integral unchanged. -/
theorem u2_supplied_spatial_pair_start_average {d : ℕ}
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (t : ℝ≥0) (f h : FieldPair d → ℝ≥0∞) (g : Vec d → ℝ≥0∞)
    (hf : Measurable f) (hh : Measurable h) (hg : Measurable g)
    (hnorm : ∀ y : Vec d, ∫⁻ x, g (y + x) ∂volume = 1) :
    (∫⁻ x, g x * (∫⁻ ω, ∫⁻ y,
      f (translate x (reduce ω)) * h (translate y (reduce ω))
      ∂u2SuppliedSpatialKernel K t (ω, x) ∂Q.measure) ∂volume) =
    ∫⁻ ω, ∫⁻ y, f (reduce ω) * h (translate y (reduce ω))
      ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure := by
  have hshift (x : Vec d) :
      (∫⁻ ω, ∫⁻ y, f (translate x (reduce ω)) * h (translate y (reduce ω))
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂Q.measure) =
      ∫⁻ ω, ∫⁻ y, f (reduce ω) * h (translate y (reduce ω))
        ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure := by
    simpa only [mul_one] using
      (u2_supplied_spatial_kernel_annealed_pair_shift Q K t x f h (fun _ => 1)
        hf hh measurable_const).symm
  simp_rw [hshift]
  rw [lintegral_mul_const _ hg]
  simpa only [zero_add, one_mul] using congrArg
    (fun c : ℝ≥0∞ => c * (∫⁻ ω, ∫⁻ y,
      f (reduce ω) * h (translate y (reduce ω))
      ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure)) (hnorm 0)


/-- Annealed two-point balance for the supplied physical origin kernel. -/
theorem u2_supplied_spatial_origin_annealed_reversible
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (t : ℝ≥0) (f h : FieldPair d → ℝ≥0∞) (hf : Measurable f) (hh : Measurable h) :
    (∫⁻ ω, ∫⁻ y, f (reduce ω) * h (translate y (reduce ω))
      ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure) =
    ∫⁻ ω, ∫⁻ y, h (reduce ω) * f (translate y (reduce ω))
      ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure := by
  obtain ⟨g, hg, hnorm⟩ := u2_exists_normalized_spatial_weight d
  let J : Kernel (Vec d × FieldPair d) (Vec d) :=
    (u2SuppliedSpatialKernel K t).comap (fun p => (p.2, 0))
      (measurable_snd.prodMk measurable_const)
  let J' : Kernel (Vec d × FieldPair d) (Vec d) :=
    (u2SuppliedSpatialKernel K t).comap (fun p => (p.2, p.1))
      (measurable_snd.prodMk measurable_fst)
  have hF : Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      f (reduce p.1.2) * h (translate p.2 (reduce p.1.2)) * g (p.2 + p.1.1)) := by
    exact ((hf.comp (Probability.measurable_reduce.comp (measurable_snd.comp measurable_fst))).mul
      (hh.comp (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (Probability.measurable_reduce.comp
          (measurable_snd.comp measurable_fst)))))).mul
      (hg.comp (measurable_snd.add (measurable_fst.comp measurable_fst)))
  have hF' : Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      f (translate p.1.1 (reduce p.1.2)) * h (translate p.2 (reduce p.1.2)) * g p.2) := by
    exact ((hf.comp (Probability.continuous_translate.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk
        (Probability.measurable_reduce.comp (measurable_snd.comp measurable_fst))))).mul
      (hh.comp (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (Probability.measurable_reduce.comp
          (measurable_snd.comp measurable_fst)))))).mul (hg.comp measurable_snd)
  have hA : Measurable (fun p : Vec d × FieldPair d => ∫⁻ y,
      f (reduce p.2) * h (translate y (reduce p.2)) * g (y + p.1) ∂J p) :=
    hF.lintegral_kernel_prod_right
  have hB : Measurable (fun p : Vec d × FieldPair d => ∫⁻ y,
      f (translate p.1 (reduce p.2)) * h (translate y (reduce p.2)) * g y ∂J' p) :=
    hF'.lintegral_kernel_prod_right
  calc
    _ = ∫⁻ ω, ∫⁻ x, ∫⁻ y, f (reduce ω) * h (translate y (reduce ω)) * g (y + x)
        ∂u2SuppliedSpatialKernel K t (ω, 0) ∂volume ∂Q.measure := by
      apply lintegral_congr
      intro ω
      exact (u2_supplied_spatial_origin_weight_average K t ω
        (fun z => f (reduce ω) * h z) g (measurable_const.mul hh) hg hnorm).symm
    _ = ∫⁻ x, ∫⁻ ω, ∫⁻ y, f (reduce ω) * h (translate y (reduce ω)) * g (y + x)
        ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure ∂volume :=
      lintegral_lintegral_swap (hA.comp (measurable_snd.prodMk measurable_fst)).aemeasurable
    _ = ∫⁻ x, ∫⁻ ω, ∫⁻ y, f (translate x (reduce ω)) * h (translate y (reduce ω)) * g y
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂Q.measure ∂volume := by
      apply lintegral_congr
      intro x
      have hs := u2_supplied_spatial_kernel_annealed_pair_shift Q K t x f h
        (fun y => g (y + x)) hf hh (hg.comp (measurable_id.add measurable_const))
      simpa only [sub_add_cancel] using hs
    _ = ∫⁻ ω, ∫⁻ x, ∫⁻ y, f (translate x (reduce ω)) * h (translate y (reduce ω)) * g y
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂volume ∂Q.measure :=
      (lintegral_lintegral_swap (show AEMeasurable
        (Function.uncurry (fun (ω : FieldPair d) (x : Vec d) => ∫⁻ y,
          f (translate x (reduce ω)) * h (translate y (reduce ω)) * g y
            ∂u2SuppliedSpatialKernel K t (ω, x))) (Q.measure.prod volume) from
        (hB.comp (measurable_snd.prodMk measurable_fst)).aemeasurable)).symm
    _ = ∫⁻ ω, ∫⁻ x, ∫⁻ y, h (translate x (reduce ω)) * f (translate y (reduce ω)) * g x
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂volume ∂Q.measure := by
      apply lintegral_congr_ae
      filter_upwards [u2_supplied_spatial_kernel_weighted_reversible (hpath := hpath) hd Q K hK] with ω hω
      exact hω t (fun x => f (translate x (reduce ω)))
        (fun x => h (translate x (reduce ω))) g
        (hf.comp (Probability.continuous_translate.measurable.comp
          (measurable_id.prodMk measurable_const)))
        (hh.comp (Probability.continuous_translate.measurable.comp
          (measurable_id.prodMk measurable_const))) hg
    _ = ∫⁻ x, g x * (∫⁻ ω, ∫⁻ y, h (translate x (reduce ω)) * f (translate y (reduce ω))
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂Q.measure) ∂volume := by
      have hC : Measurable (fun p : Vec d × FieldPair d => ∫⁻ y,
          h (translate p.1 (reduce p.2)) * f (translate y (reduce p.2)) * g p.1 ∂J' p) := by
        apply Measurable.lintegral_kernel_prod_right
        exact ((hh.comp (Probability.continuous_translate.measurable.comp
          ((measurable_fst.comp measurable_fst).prodMk
            (Probability.measurable_reduce.comp (measurable_snd.comp measurable_fst))))).mul
          (hf.comp (Probability.continuous_translate.measurable.comp
            (measurable_snd.prodMk (Probability.measurable_reduce.comp
              (measurable_snd.comp measurable_fst)))))).mul
          (hg.comp (measurable_fst.comp measurable_fst))
      rw [lintegral_lintegral_swap (show AEMeasurable
        (Function.uncurry (fun (ω : FieldPair d) (x : Vec d) => ∫⁻ y,
          h (translate x (reduce ω)) * f (translate y (reduce ω)) * g x
            ∂u2SuppliedSpatialKernel K t (ω, x))) (Q.measure.prod volume) from
        (hC.comp (measurable_snd.prodMk measurable_fst)).aemeasurable)]
      apply lintegral_congr
      intro x
      have hD : Measurable (fun p : Vec d × FieldPair d => ∫⁻ y,
          h (translate p.1 (reduce p.2)) * f (translate y (reduce p.2)) ∂J' p) := by
        apply Measurable.lintegral_kernel_prod_right
        exact (hh.comp (Probability.continuous_translate.measurable.comp
          ((measurable_fst.comp measurable_fst).prodMk
            (Probability.measurable_reduce.comp (measurable_snd.comp measurable_fst))))).mul
          (hf.comp (Probability.continuous_translate.measurable.comp
            (measurable_snd.prodMk (Probability.measurable_reduce.comp
              (measurable_snd.comp measurable_fst)))))
      calc
        _ = ∫⁻ ω, (∫⁻ y, h (translate x (reduce ω)) * f (translate y (reduce ω))
            ∂u2SuppliedSpatialKernel K t (ω, x)) * g x ∂Q.measure := by
          apply lintegral_congr
          intro ω
          have hm : Measurable (fun y : Vec d =>
              h (translate x (reduce ω)) * f (translate y (reduce ω))) :=
            measurable_const.mul (hf.comp (Probability.continuous_translate.measurable.comp
              (measurable_id.prodMk measurable_const)))
          exact lintegral_mul_const (g x) hm
        _ = _ := by
          have hm : Measurable (fun ω : FieldPair d => ∫⁻ y,
              h (translate x (reduce ω)) * f (translate y (reduce ω))
                ∂u2SuppliedSpatialKernel K t (ω, x)) :=
            hD.comp (measurable_const.prodMk measurable_id)
          simpa only [mul_comm] using
            (lintegral_mul_const (μ := Q.measure) (g x) hm)
    _ = _ := u2_supplied_spatial_pair_start_average Q K t h f g hh hf hg hnorm


/-- The supplied reduced kernel satisfies rectangle detailed balance. -/
theorem u2_reduced_environment_kernel_reversible
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) (t : ℝ≥0) :
    Kernel.IsReversible (c2ReducedEnvironmentKernel K D hD t) (reducedLaw Q) := by
  let R := c2ReducedEnvironmentKernel K D hD t
  have hrect (A B : Set (FieldPair d)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      (∫⁻ ρ in A, R ρ B ∂reducedLaw Q) =
        ∫⁻ ω, ∫⁻ y, (A.indicator 1) (reduce ω) *
          (B.indicator 1) (translate y (reduce ω))
          ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure := by
    let a : FieldPair d → ℝ≥0∞ := A.indicator 1
    let b : FieldPair d → ℝ≥0∞ := B.indicator 1
    have hb : Measurable b := measurable_const.indicator hB
    have hm : Measurable (A.indicator (fun ρ => R ρ B)) :=
      (R.measurable_coe hB).indicator hA
    rw [← lintegral_indicator hA]
    change (∫⁻ ρ, A.indicator (fun ρ => R ρ B) ρ ∂Q.measure.map reduce) = _
    rw [lintegral_map hm Probability.measurable_reduce]
    apply lintegral_congr
    intro ω
    have hs : (∫⁻ y, b (translate y (reduce ω))
        ∂u2SuppliedSpatialKernel K t (ω, 0)) = R (reduce ω) B := by
      rw [← lintegral_map hb (show Measurable (fun y : Vec d => translate y (reduce ω)) from
        Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)),
        ← u2_environment_kernel_eq_supplied_spatial_origin,
        ← c2ReducedEnvironmentKernel_pullback K D hD hleft]
      exact lintegral_indicator_one hB
    change A.indicator (fun ρ => R ρ B) (reduce ω) =
      ∫⁻ y, a (reduce ω) * b (translate y (reduce ω))
        ∂u2SuppliedSpatialKernel K t (ω, 0)
    have hc : (∫⁻ y, a (reduce ω) * b (translate y (reduce ω))
        ∂u2SuppliedSpatialKernel K t (ω, 0)) =
        a (reduce ω) * (∫⁻ y, b (translate y (reduce ω))
          ∂u2SuppliedSpatialKernel K t (ω, 0)) := by
      apply lintegral_const_mul
      exact hb.comp (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))
    rw [hc, hs]
    by_cases hω : reduce ω ∈ A <;> simp [a, Set.indicator, hω]
  intro A B hA hB
  rw [hrect A B hA hB, hrect B A hB hA]
  exact u2_supplied_spatial_origin_annealed_reversible (hpath := hpath) hd Q K hK t
    (A.indicator 1) (B.indicator 1) (measurable_const.indicator hA)
      (measurable_const.indicator hB)


/-- The reconstructed supplied unforced kernel is symmetric on real L². -/
theorem u2_unforced_reduced_kernel_real_L2_symmetric
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce)
    (t : ℝ≥0) (F G : Lp ℝ 2 (reducedLaw Q)) :
    (∫ ω, (∫ ρ, F ρ ∂c2ReducedEnvironmentKernel K D hD t ω) * G ω ∂reducedLaw Q) =
      ∫ ω, F ω * (∫ ρ, G ρ ∂c2ReducedEnvironmentKernel K D hD t ω) ∂reducedLaw Q := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  simpa only [mul_comm] using
    (C8GMP.reversible_kernel_pairing (reducedLaw Q) (c2ReducedEnvironmentKernel K D hD t)
      (u2_reduced_environment_kernel_reversible (hpath := hpath) hd Q K hK D hD hleft t) G F)


/-- The reconstructed reduced kernel starts at the identity almost surely. -/
theorem u2_reduced_environment_kernel_zero_ae
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) :
    ∀ᵐ ρ ∂reducedLaw Q,
      c2ReducedEnvironmentKernel K D hD 0 ρ = Measure.dirac ρ := by
  apply (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr
  filter_upwards [hK] with ω hω
  rw [c2ReducedEnvironmentKernel_pullback K D hD hleft]
  exact c2EnvironmentKernel_zero_of_start K ω hω.2.1


/-- The supplied spatial marginals obey Chapman--Kolmogorov from the origin
at positive first time, on the same full environment event. -/
theorem u2_supplied_spatial_kernel_add_origin_ae
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω)) :
    ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ ω, ∀ s t : ℝ≥0, 0 < s →
      ∀ A : Set (Vec d), MeasurableSet A →
        u2SuppliedSpatialKernel K (s + t) (ω, 0) A =
          ∫⁻ x, u2SuppliedSpatialKernel K t (ω, x) A
            ∂u2SuppliedSpatialKernel K s (ω, 0) := by
  filter_upwards [u2_supplied_spatial_kernel_eq_regular_ae (hpath := hpath) hd Q K hK 0,
    u2_supplied_spatial_kernel_eq_regular_orbit_ae (hpath := hpath) hd Q K hK] with ω hzero horbit
  intro hω s t hs A hA
  let P := u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) 0
    (sourceReducedBound Λ) (one_le_sourceReducedBound Q.ellipticity_parameter)
    (flatReducedEnvironment_regular Q.ellipticity_parameter hω)
  obtain ⟨M, p, hM, hp, hpb, hrep⟩ :=
    u2_regular_unforced_kernel_bounded_density hd (flatReducedEnvironment ω)
      (sourceReducedBound Λ) (one_le_sourceReducedBound Q.ellipticity_parameter)
      (flatReducedEnvironment_regular Q.ellipticity_parameter hω) s hs
  have hac : P s 0 ≪ (volume : Measure (Vec d)) := by
    rw [hrep 0]
    exact withDensity_absolutelyContinuous _ _
  have heq : ∀ᵐ x ∂P s 0, u2SuppliedSpatialKernel K t (ω, x) = P t x := by
    filter_upwards [hac.ae_le (horbit hω)] with x hx
    exact hx t
  calc
    u2SuppliedSpatialKernel K (s + t) (ω, 0) A = P (s + t) 0 A := by
      rw [hzero hω (s + t)]
    _ = ∫⁻ x, P t x A ∂P s 0 := by
      rw [P.kernel_add, Kernel.comp_apply' _ _ _ hA]
    _ = ∫⁻ x, u2SuppliedSpatialKernel K t (ω, x) A
          ∂u2SuppliedSpatialKernel K s (ω, 0) := by
      rw [hzero hω s]
      apply lintegral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]


/-- At any spatially translated reduced field, the environment transition is
exactly the corresponding supplied spatial transition mapped along the orbit. -/
theorem u2_reduced_environment_kernel_spatial_pullback {d : ℕ}
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) (t : ℝ≥0)
    (ω : FieldPair d) (x : Vec d) :
    c2ReducedEnvironmentKernel K D hD t (translate x (reduce ω)) =
      (u2SuppliedSpatialKernel K t (ω, x)).map (fun y => translate y (reduce ω)) := by
  calc
    _ = c2EnvironmentKernel K t (translate x ω) := by
      simpa only [reduce_translate] using
        c2ReducedEnvironmentKernel_pullback K D hD hleft t (translate x ω)
    _ = _ := by
      rw [c2EnvironmentKernel_apply, u2_supplied_spatial_kernel_apply,
        Measure.map_map
          (show Measurable (fun y : Vec d => translate y (reduce ω)) from
            Probability.continuous_translate.measurable.comp
              (measurable_id.prodMk measurable_const))
          (show Measurable (fun γ : Path d => x + γ t) from
            measurable_const.add (measurable_pathPosition t))]
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun γ => by
        simp [reduce_translate, translate_add, add_comm]


/-- Positive-time Chapman--Kolmogorov for the actual reconstructed reduced
kernel, simultaneously for all times on a full reduced-law event. -/
theorem u2_reduced_environment_kernel_add_ae
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) :
    ∀ᵐ ρ ∂reducedLaw Q, ∀ s t : ℝ≥0, 0 < s →
      c2ReducedEnvironmentKernel K D hD (s + t) ρ =
        (c2ReducedEnvironmentKernel K D hD t ∘ₖ c2ReducedEnvironmentKernel K D hD s) ρ := by
  apply (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr
  filter_upwards [u2_supplied_spatial_kernel_add_origin_ae (hpath := hpath) hd Q K hK, Q.regular]
    with ω hadd hω
  intro s t hs
  ext A hA
  let f : Vec d → FieldPair d := fun y => translate y (reduce ω)
  have hf : Measurable f := Probability.continuous_translate.measurable.comp
    (measurable_id.prodMk measurable_const)
  calc
    c2ReducedEnvironmentKernel K D hD (s + t) (reduce ω) A =
        u2SuppliedSpatialKernel K (s + t) (ω, 0) (f ⁻¹' A) := by
      rw [c2ReducedEnvironmentKernel_pullback K D hD hleft,
        u2_environment_kernel_eq_supplied_spatial_origin, Measure.map_apply hf hA]
    _ = ∫⁻ x, u2SuppliedSpatialKernel K t (ω, x) (f ⁻¹' A)
        ∂u2SuppliedSpatialKernel K s (ω, 0) :=
      hadd hω s t hs (f ⁻¹' A) (hA.preimage hf)
    _ = ∫⁻ x, c2ReducedEnvironmentKernel K D hD t (f x) A
        ∂u2SuppliedSpatialKernel K s (ω, 0) := by
      apply lintegral_congr
      intro x
      rw [u2_reduced_environment_kernel_spatial_pullback K D hD hleft,
        Measure.map_apply hf hA]
    _ = (c2ReducedEnvironmentKernel K D hD t ∘ₖ
          c2ReducedEnvironmentKernel K D hD s) (reduce ω) A := by
      rw [Kernel.comp_apply' _ _ _ hA, c2ReducedEnvironmentKernel_pullback K D hD hleft,
        u2_environment_kernel_eq_supplied_spatial_origin,
        lintegral_map ((c2ReducedEnvironmentKernel K D hD t).measurable_coe hA) hf]


/-- The reconstructed environment kernels satisfy both zero-time and
composition laws on a common full reduced-law event. -/
theorem u2_reduced_environment_kernel_semigroup_ae
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) :
    ∀ᵐ ρ ∂reducedLaw Q,
      c2ReducedEnvironmentKernel K D hD 0 ρ = Measure.dirac ρ ∧
      ∀ s t : ℝ≥0, c2ReducedEnvironmentKernel K D hD (s + t) ρ =
        (c2ReducedEnvironmentKernel K D hD t ∘ₖ c2ReducedEnvironmentKernel K D hD s) ρ := by
  filter_upwards [u2_reduced_environment_kernel_zero_ae hd Q K hK D hD hleft,
    u2_reduced_environment_kernel_add_ae (hpath := hpath) hd Q K hK D hD hleft] with ρ hzero hadd
  refine ⟨hzero, ?_⟩
  intro s t
  by_cases hs : s = 0
  · subst s
    simp only [zero_add]
    rw [Kernel.comp_apply, hzero, Measure.dirac_bind (Kernel.measurable _)]
  · exact hadd s t (lt_of_le_of_ne (zero_le : 0 ≤ s) (Ne.symm hs))



/-- Square-integrable observations are integrable against almost every
reconstructed transition measure. -/
theorem u2_reduced_environment_kernel_integrable_ae
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) (t : ℝ≥0)
    (F : Lp ℝ 2 (reducedLaw Q)) :
    ∀ᵐ ρ ∂reducedLaw Q, Integrable F (c2ReducedEnvironmentKernel K D hD t ρ) := by
  let R := c2ReducedEnvironmentKernel K D hD t
  have hμ : R ∘ₘ reducedLaw Q ≤ reducedLaw Q :=
    le_of_eq (u2_reduced_environment_kernel_invariant (hpath := hpath) hd Q K hK D hD hleft t)
  have hf := (Lp.memLp F).mono_measure hμ
  have heq : ∀ᵐ ρ ∂reducedLaw Q, F =ᵐ[R ρ] hf.aestronglyMeasurable.mk F :=
    Measure.ae_ae_of_ae_comp hf.aestronglyMeasurable.ae_eq_mk
  have hint := Measure.ae_integrable_of_integrable_comp
    (hf.integrable_norm_rpow (by norm_num) (by simp))
  filter_upwards [heq, hint] with ρ hρeq hρint
  have hm : AEStronglyMeasurable F (R ρ) :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk.aestronglyMeasurable.congr hρeq.symm
  have hmem : MemLp F 2 (R ρ) :=
    (integrable_norm_rpow_iff hm (by norm_num) (by simp)).mp hρint
  exact hmem.integrable (by norm_num)



/-- The canonical reconstructed-kernel operators form a contractive real L²
semigroup. -/
theorem u2_unforced_reduced_kernel_L2_semigroup
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) :
    ∃ T : ℝ≥0 → Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q),
      (∀ t, ‖T t‖ ≤ 1) ∧
      (∀ t F, T t F =ᵐ[reducedLaw Q]
        MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) F) ∧
      (∀ F, T 0 F = F) ∧
      ∀ s t F, T (s + t) F = T s (T t F) := by
  let R := c2ReducedEnvironmentKernel K D hD
  let hR : ∀ t, MarkovProcess.IsSubMarkovKernel (R t) := fun t =>
    MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel (R t)
  let hμ : ∀ t, R t ∘ₘ reducedLaw Q ≤ reducedLaw Q := fun t =>
    le_of_eq (u2_reduced_environment_kernel_invariant (hpath := hpath) hd Q K hK D hD hleft t)
  letI : Fact (1 ≤ (2 : ℝ≥0)) := ⟨by norm_num⟩
  let T : ℝ≥0 → Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q) := fun t =>
    MarkovProcess.kernelLpFinite (reducedLaw Q) (R t) (hR t) (hμ t) 2
  have hrep (t : ℝ≥0) (F : Lp ℝ 2 (reducedLaw Q)) :
      T t F =ᵐ[reducedLaw Q] MarkovProcess.kernelIntegral (R t) F :=
    MarkovProcess.coeFn_kernelLpFinite _ _ _ _ _ F
  refine ⟨T, fun t => MarkovProcess.norm_kernelLpFinite_le _ _ _ _ _, hrep, ?_, ?_⟩
  · intro F
    apply Lp.ext
    refine (hrep 0 F).trans ?_
    filter_upwards [u2_reduced_environment_kernel_zero_ae hd Q K hK D hD hleft] with ρ hρ
    change (∫ x, F x ∂R 0 ρ) = F ρ
    rw [hρ, integral_dirac' _ _ (Lp.stronglyMeasurable F)]
  · intro s t F
    apply Lp.ext
    refine (hrep (s + t) F).trans ?_
    have hadd : MarkovProcess.kernelIntegral (R (s + t)) F =ᵐ[reducedLaw Q]
        MarkovProcess.kernelIntegral (R s) (MarkovProcess.kernelIntegral (R t) F) := by
      filter_upwards [u2_reduced_environment_kernel_semigroup_ae (hpath := hpath) hd Q K hK D hD hleft,
        u2_reduced_environment_kernel_integrable_ae (hpath := hpath) hd Q K hK D hD hleft (s + t) F]
        with ρ hsem hint
      change (∫ x, F x ∂R (s + t) ρ) = _
      rw [hsem.2 s t] at hint ⊢
      exact Kernel.integral_comp hint
    refine hadd.trans ?_
    refine (MarkovProcess.kernelIntegral_congr_ae (hμ s) (hrep t F).symm).trans ?_
    exact (hrep s (T t F)).symm



/-- Bounded continuous observations yield continuous orbits for any operator
family associated with the reconstructed path kernel. -/
theorem u2_reduced_kernel_bounded_orbit_continuous
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (T : ℝ≥0 → Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q))
    (hrep : ∀ t F, T t F =ᵐ[reducedLaw Q]
      MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) F)
    (hinv : ∀ t, c2ReducedEnvironmentKernel K D hD t ∘ₘ reducedLaw Q ≤ reducedLaw Q)
    (f : BoundedContinuousFunction (FieldPair d) ℝ) :
    Continuous (fun t => T t (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℝ f)) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let F := BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℝ f
  let M : ℝ≥0 → FieldPair d → ℝ := fun t ρ =>
    ∫ γ : Path d, f (translate (γ t) (reduce (D ρ))) ∂K (D ρ)
  have hM (t : ℝ≥0) (ρ : FieldPair d) :
      MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) f ρ = M t ρ := by
    change (∫ x, f x ∂c2EnvironmentKernel K t (D ρ)) = _
    rw [c2EnvironmentKernel_apply]
    exact integral_map ((measurable_c2EnvironmentAt t).comp
      (measurable_const.prodMk measurable_id)).aemeasurable f.continuous.aestronglyMeasurable
  have he (t : ℝ≥0) : T t F =ᵐ[reducedLaw Q] M t := by
    refine (hrep t F).trans ?_
    refine (MarkovProcess.kernelIntegral_congr_ae (hinv t)
      (BoundedContinuousFunction.coeFn_toLp 2 (reducedLaw Q) ℝ f)).trans ?_
    exact Filter.Eventually.of_forall (hM t)
  have hc (ρ : FieldPair d) : Continuous (fun t => M t ρ) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact tendsto_integral_filter_of_dominated_convergence (μ := K (D ρ))
      (fun _ : Path d => ‖f‖)
      (Filter.Eventually.of_forall fun t : ℝ≥0 =>
        (f.continuous.comp (Probability.continuous_translate.comp
          ((continuous_eval_const t).prodMk (continuous_const (y := reduce (D ρ)))))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t : ℝ≥0 =>
        Filter.Eventually.of_forall fun γ : Path d => f.norm_coe_le_norm _)
      (integrable_const ‖f‖)
      (Filter.Eventually.of_forall fun γ : Path d =>
        (f.continuous.comp (Probability.continuous_translate.comp
          (γ.continuous.prodMk (continuous_const (y := reduce (D ρ)))))).tendsto s)
  have hb (t : ℝ≥0) (ρ : FieldPair d) : ‖M t ρ‖ ≤ ‖f‖ := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := K (D ρ))
        (Filter.Eventually.of_forall fun γ : Path d => f.norm_coe_le_norm _))
  have hm (t : ℝ≥0) : Measurable (M t) := by
    have h : Measurable (MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) f) :=
      (f.continuous.stronglyMeasurable.integral_kernel
        (κ := c2ReducedEnvironmentKernel K D hD t)).measurable
    convert h using 1
    funext ρ
    exact (hM t ρ).symm
  apply continuous_iff_continuousAt.mpr
  intro s
  have hlim : Tendsto (fun t : ℝ≥0 => ∫ ρ, ‖M t ρ - M s ρ‖ ^ 2 ∂reducedLaw Q)
      (𝓝 s) (𝓝 0) := by
    have ht := tendsto_integral_filter_of_dominated_convergence (μ := reducedLaw Q)
      (fun _ : FieldPair d => (2 * ‖f‖) ^ 2)
      (Filter.Eventually.of_forall fun t : ℝ≥0 =>
        (((hm t).sub (hm s)).norm.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t : ℝ≥0 => Filter.Eventually.of_forall fun ρ => by
        rw [Real.norm_eq_abs, abs_sq]
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (norm_sub_le _ _).trans ((add_le_add (hb t ρ) (hb s ρ)).trans_eq (two_mul ‖f‖).symm))
      (integrable_const ((2 * ‖f‖) ^ 2))
      (Filter.Eventually.of_forall fun ρ => by
        have h := (((hc ρ).sub (continuous_const (y := M s ρ))).norm.pow 2).tendsto s
        change Tendsto (fun t : ℝ≥0 => ‖M t ρ - M s ρ‖ ^ 2) (𝓝 s)
          (𝓝 (‖M s ρ - M s ρ‖ ^ 2)) at h
        simpa only [Pi.sub_apply, sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0)] using h)
    simpa only [Pi.sub_apply, Pi.pow_apply, sub_self, norm_zero,
      zero_pow (by omega : 2 ≠ 0), integral_zero] using ht
  have hsq : Tendsto (fun t : ℝ≥0 => ‖T t F - T s F‖ ^ 2) (𝓝 s) (𝓝 0) := by
    apply hlim.congr
    intro t
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (T t F) (T s F), he t, he s] with ρ hsub ht hs
    simp only [hsub, Pi.sub_apply, ht, hs]
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h



/-- The reconstructed unforced kernel induces a strongly continuous real L²
contraction semigroup. -/
theorem u2_unforced_reduced_kernel_L2_strongly_continuous
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) :
    ∃ T : ℝ≥0 → Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q),
      (∀ t, ‖T t‖ ≤ 1) ∧
      (∀ t F, T t F =ᵐ[reducedLaw Q]
        MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) F) ∧
      (∀ F, T 0 F = F) ∧
      (∀ s t F, T (s + t) F = T s (T t F)) ∧
      ∀ F, Continuous (fun t => T t F) := by
  obtain ⟨T, hn, hr, hz, ha⟩ :=
    u2_unforced_reduced_kernel_L2_semigroup (hpath := hpath) hd Q K hK D hD hleft
  refine ⟨T, hn, hr, hz, ha, ?_⟩
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let _ : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  let _ : PolishSpace (FieldPair d) := inferInstance
  let A : Set (Lp ℝ 2 (reducedLaw Q)) := Set.range
    (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℝ)
  have hA : Dense A := BoundedContinuousFunction.toLp_denseRange ℝ (reducedLaw Q) ℝ (by norm_num)
  have hc : ∀ F ∈ A, Continuous (fun t => T t F) := by
    rintro F ⟨f, rfl⟩
    exact u2_reduced_kernel_bounded_orbit_continuous Q K D hD T hr
      (fun t => le_of_eq (u2_reduced_environment_kernel_invariant (hpath := hpath) hd Q K hK D hD hleft t)) f
  intro F
  apply continuous_iff_continuousAt.mpr
  intro s
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨G, hG, hFG⟩ := hA.exists_dist_lt F (div_pos hε (by norm_num : (0 : ℝ) < 3))
  have hg := Metric.tendsto_nhds.mp ((hc G hG).continuousAt (x := s)) (ε / 3) (by positivity)
  filter_upwards [hg] with t ht
  have hfirst : dist (T t F) (T t G) ≤ dist F G := by
    calc
      _ ≤ ‖T t‖ * dist F G := (T t).dist_le_opNorm _ _
      _ ≤ 1 * dist F G := mul_le_mul_of_nonneg_right (hn t) dist_nonneg
      _ = _ := one_mul _
  have hlast : dist (T s G) (T s F) ≤ dist F G := by
    rw [dist_comm]
    calc
      _ ≤ ‖T s‖ * dist F G := (T s).dist_le_opNorm _ _
      _ ≤ 1 * dist F G := mul_le_mul_of_nonneg_right (hn s) dist_nonneg
      _ = _ := one_mul _
  calc
    dist (T t F) (T s F) ≤ dist (T t F) (T t G) +
        (dist (T t G) (T s G) + dist (T s G) (T s F)) :=
      (dist_triangle (T t F) (T t G) (T s F)).trans
        (add_le_add le_rfl (dist_triangle (T t G) (T s G) (T s F)))
    _ < ε := by linarith



/-- A uniformly contractive complex L² action has continuous orbits everywhere
when its continuous orbits form a dense set. -/
theorem u2_complex_L2_action_continuous_of_real_parts
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (T : ℝ≥0 → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hbound : ∀ t, ‖T t‖ ≤ 1)
    (hdense : Dense {f : Lp ℂ 2 μ | Continuous (fun t : ℝ≥0 => T t f)}) :
    ∀ f, Continuous (fun t : ℝ≥0 => T t f) := by
  have hjoint : Continuous (fun ft : Lp ℂ 2 μ × ℝ≥0 => T ft.2 ft.1) := by
    apply continuous_prod_of_dense_continuous_lipschitzWith _ 1 hdense
    · intro f hf
      exact hf
    · intro t
      exact ContinuousLinearMap.lipschitzWith_of_opNorm_le (f := T t) (K := 1) (hbound t)
  intro f
  exact hjoint.comp (continuous_const.prodMk continuous_id)


/-- Discounted continuous orbits are Bochner integrable on every finite interval. -/
theorem u2_discounted_C0_orbit_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ≥0 → E →L[ℝ] E)
    (hcont : ∀ f, Continuous (fun t : ℝ≥0 => T t f))
    (f : E) (a b c : ℝ) :
    IntervalIntegrable (fun s : ℝ => Real.exp (-c*s) • T s.toNNReal f) volume a b := by
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    ((hcont f).comp continuous_real_toNNReal)).intervalIntegrable a b


/-- The reconstructed unforced L² semigroup has integrable discounted orbits. -/
theorem u2_unforced_reduced_kernel_L2_discounted_intervalIntegrable
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (D : FieldPair d → FieldPair d) (hD : Measurable D)
    (hleft : Function.LeftInverse D reduce) :
    ∃ T : ℝ≥0 → Lp ℝ 2 (reducedLaw Q) →L[ℝ] Lp ℝ 2 (reducedLaw Q),
      (∀ t, ‖T t‖ ≤ 1) ∧
      (∀ t F, T t F =ᵐ[reducedLaw Q]
        MarkovProcess.kernelIntegral (c2ReducedEnvironmentKernel K D hD t) F) ∧
      (∀ F, T 0 F = F) ∧
      (∀ s t F, T (s + t) F = T s (T t F)) ∧
      (∀ F, Continuous (fun t => T t F)) ∧
      ∀ F a b c, IntervalIntegrable
        (fun s : ℝ => Real.exp (-c*s) • T s.toNNReal F) volume a b := by
  obtain ⟨T, hn, hr, hz, ha, hc⟩ :=
    u2_unforced_reduced_kernel_L2_strongly_continuous (hpath := hpath) hd Q K hK D hD hleft
  exact ⟨T, hn, hr, hz, ha, hc, fun F a b c =>
    u2_discounted_C0_orbit_intervalIntegrable T hc F a b c⟩


end EinsteinFull
