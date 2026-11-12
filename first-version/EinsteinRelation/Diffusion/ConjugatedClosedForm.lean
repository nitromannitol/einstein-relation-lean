import EinsteinRelation.Diffusion.ConjugatedFormQuotient

/-!
# Transporting the full fixed-environment closed form

Source `paper/main.tex:406–408`. Once the actual weak-gradient domain
and energy have been transported, the source realization's domain and
short-time limit pass to the conjugated semigroup.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.External.GantertSection7Support

/-- Positive coordinate scaling preserves the full bounded-form
characterization of the actual Sobolev domain. -/
theorem closedForm_domain_conjugate {d : ℕ}
    (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (ω' : FieldPair d) (e : Vec d ≃ᵐ Vec d) (c : ℝ) (hc : 0 < c)
    (hm : (physicalReversibleMeasure ω' hd lam).map e =
      ENNReal.ofReal c • physicalReversibleMeasure ω hd lam)
    (hH1 : ∀ f : Vec d → ℝ, physicalH1Member ω' hd lam f ↔
      physicalH1Member ω hd lam (fun y => f (e.symm y)))
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω' hd lam)) :
    ((∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient ω' hd lam
        (fun t => Probability.conjugateKernel e (r.transitionKernel t)) t f ≤ C) ↔
      physicalH1Member ω' hd lam f) := by
  have hf' := memLp_comp_symm_of_map_eq_smul e _ _ (ENNReal.ofReal c)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top hm f 2 hf
  rw [hH1 f, ← r.closedForm_domain (fun y => f (e.symm y)) hf']
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C / c, fun t ht => ?_⟩
    have h := hC t ht
    rw [semigroupFormDifferenceQuotient_conjugate ω ω' hd lam e c hc.le hm] at h
    apply (le_div_iff₀ hc).mpr
    nlinarith
  · rintro ⟨C, hC⟩
    refine ⟨c * C, fun t ht => ?_⟩
    rw [semigroupFormDifferenceQuotient_conjugate ω ω' hd lam e c hc.le hm]
    exact mul_le_mul_of_nonneg_left (hC t ht) hc.le

/-- Transport of actual graph representatives and their energy gives
all source closed-form limits for the conjugated semigroup. -/
theorem closedForm_value_conjugate {d : ℕ}
    (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (ω' : FieldPair d) (e : Vec d ≃ᵐ Vec d) (c : ℝ) (hc : 0 < c)
    (hm : (physicalReversibleMeasure ω' hd lam).map e =
      ENNReal.ofReal c • physicalReversibleMeasure ω hd lam)
    (hH1 : ∀ f : Vec d → ℝ, physicalH1Member ω' hd lam f ↔
      physicalH1Member ω hd lam (fun y => f (e.symm y)))
    (T : SpatialDirichlet.WeightedSobolevGraph (physicalForceMeasure hd lam) →
      SpatialDirichlet.WeightedSobolevGraph (physicalForceMeasure hd lam))
    (hTv : ∀ u x, (T u).value x = u.value (e.symm x))
    (hTe : ∀ u, physicalH1FormEnergy ω' hd lam u = c * physicalH1FormEnergy ω hd lam (T u))
    (f : Vec d → ℝ)
    (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω' hd lam] f)
    (u : SpatialDirichlet.WeightedSobolevGraph (physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω' hd lam] f) :
    Tendsto (fun t : ℝ≥0 => semigroupFormDifferenceQuotient ω' hd lam
      (fun t => Probability.conjugateKernel e (r.transitionKernel t)) t f)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 (physicalH1FormEnergy ω' hd lam u)) := by
  have hmap : (fun y => u.value (e.symm y)) =ᵐ[
      (physicalReversibleMeasure ω' hd lam).map e] (fun y => f (e.symm y)) :=
    e.measurableEmbedding.ae_map_iff.mpr (by simpa only [e.symm_apply_apply] using hu)
  rw [hm] at hmap
  have huold : (T u).value =ᵐ[physicalReversibleMeasure ω hd lam]
      (fun y => f (e.symm y)) := by
    have h := (Measure.ae_smul_measure_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hc))).mp hmap
    exact h.mono fun x hx => (hTv u x).trans hx
  obtain ⟨qold, hqold⟩ := (hH1 f).mp ⟨q, hq⟩
  have hlim := (r.closedForm_value (fun y => f (e.symm y)) qold hqold (T u) huold).const_mul c
  rw [hTe u]
  convert hlim using 1
  funext t
  exact semigroupFormDifferenceQuotient_conjugate ω ω' hd lam e c hc.le hm r.transitionKernel t f


end EinsteinRelation.External.GantertSection7Support
