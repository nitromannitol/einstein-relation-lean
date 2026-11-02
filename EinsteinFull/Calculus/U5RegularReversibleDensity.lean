import EinsteinFull.Calculus.U7RegularKernelDensity
import EinsteinFull.Calculus.U5RegularKernelInvariance

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

namespace EinsteinFull

/-- Transport an every-start volume absolute continuity result to the reversible measure. -/
theorem u5_regular_reversible_density_of_ac {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (hAC : ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d))) :
    ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y) ∧
      (∀ x, Integrable (p x) (physicalReversibleMeasure ω hd lam) ∧
        ∫ y, p x y ∂physicalReversibleMeasure ω hd lam = 1) ∧
      (∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        (physicalReversibleMeasure ω hd lam).withDensity (fun y => ENNReal.ofReal (p x y))) := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t
  letI : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  letI : IsMarkovKernel K := ⟨fun x =>
    ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩⟩
  have hv : (volume : Measure (Vec d)) ≪ μ := by
    apply Measure.ae_le_iff_absolutelyContinuous.mp
    intro P hP
    exact (Blueprint.gmpPhysical_ae_iff_volume hd ω lam P).mp hP
  have hK (x : Vec d) : K x ≪ μ := by
    exact (hAC x).trans hv
  let ν := μ.toFinite
  let η : Kernel (Vec d) (Vec d) := Kernel.const _ ν
  let q := ν.rnDeriv μ
  let r : Vec d → Vec d → ℝ≥0∞ := fun x y => q y * K.rnDeriv η x y
  have hq : Measurable q := Measure.measurable_rnDeriv _ _
  have hr : Measurable (Function.uncurry r) :=
    (hq.comp measurable_snd).mul (Kernel.measurable_rnDeriv K η)
  have hrep (x : Vec d) : K x = μ.withDensity (r x) := by
    have hν : μ.withDensity q = ν := Measure.withDensity_rnDeriv_eq ν μ
      (toFinite_absolutelyContinuous μ)
    have hKν : K x ≪ ν := (hK x).trans (absolutelyContinuous_toFinite μ)
    have heq := Kernel.withDensity_rnDeriv_eq (κ := K) (η := η) hKν
    rw [Kernel.withDensity_apply η (Kernel.measurable_rnDeriv K η)] at heq
    change ν.withDensity (K.rnDeriv η x) = K x at heq
    change K x = μ.withDensity (fun y => q y * K.rnDeriv η x y)
    rw [show (fun y => q y * K.rnDeriv η x y) = q * K.rnDeriv η x by rfl,
      withDensity_mul μ hq (Kernel.measurable_rnDeriv_right K η x), hν]
    exact heq.symm
  let p : Vec d → Vec d → ℝ := fun x y => (r x y).toReal
  have hp : Measurable (Function.uncurry p) := ENNReal.measurable_toReal.comp hr
  have hn (x y : Vec d) : 0 ≤ p x y := ENNReal.toReal_nonneg
  have hreal (x : Vec d) : K x = μ.withDensity (fun y => ENNReal.ofReal (p x y)) := by
    have hmeas : Measurable (r x) := hr.comp (measurable_const.prodMk measurable_id)
    have hfin : (∫⁻ y, r x y ∂μ) ≠ ∞ := by
      have hm : μ.withDensity (r x) Set.univ ≠ ∞ := by
        rw [← hrep x]
        exact measure_ne_top (K x) Set.univ
      simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hm
    have hae := ae_lt_top hmeas hfin
    rw [hrep x]
    apply withDensity_congr_ae
    filter_upwards [hae] with y hy
    exact (ENNReal.ofReal_toReal hy.ne).symm
  refine ⟨p, hp, hn, ?_, hreal⟩
  intro x
  have hpmeas : Measurable (p x) := hp.comp (measurable_const.prodMk measurable_id)
  have hm : (∫⁻ y, ENNReal.ofReal (p x y) ∂μ) = 1 := by
    have he := congrArg (fun m : Measure (Vec d) => m Set.univ) (hreal x)
    simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] using he.symm
  have hf : Integrable (fun y => (ENNReal.ofReal (p x y)).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hpmeas.ennreal_ofReal.aemeasurable (by rw [hm]; simp)
  have hi : Integrable (p x) μ := by
    simpa only [ENNReal.toReal_ofReal (hn x _)] using hf
  refine ⟨hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (hn x))
  rw [hm] at he
  have he' := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (hn x)), ENNReal.toReal_one] using he'

#print axioms u5_regular_reversible_density_of_ac

/-- Every-start absolute continuity and reversibility give a symmetric density. -/
theorem u5_regular_symmetric_density_of_ac {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (hAC : ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d))) :
    ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y) ∧
      (∀ x, Integrable (p x) (physicalReversibleMeasure ω hd lam) ∧
        ∫ y, p x y ∂physicalReversibleMeasure ω hd lam = 1) ∧
      (∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        (physicalReversibleMeasure ω hd lam).withDensity (fun y => ENNReal.ofReal (p x y))) ∧
      ∀ᵐ q ∂(physicalReversibleMeasure ω hd lam).prod
        (physicalReversibleMeasure ω hd lam), p q.1 q.2 = p q.2 q.1 := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  obtain ⟨p, hp, hn, hi, hr⟩ := u5_regular_reversible_density_of_ac hd ω lam Λ hΛ hω t hAC
  refine ⟨p, hp, hn, hi, hr, ?_⟩
  let f : Vec d × Vec d → ℝ≥0∞ := fun q => ENNReal.ofReal (p q.1 q.2)
  let g : Vec d × Vec d → ℝ≥0∞ := fun q => ENNReal.ofReal (p q.2 q.1)
  have hf : Measurable f := hp.ennreal_ofReal
  have hg : Measurable g := hf.comp measurable_swap
  have hrect (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      (μ.prod μ).withDensity f (A ×ˢ B) = (μ.prod μ).withDensity g (A ×ˢ B) := by
    rw [withDensity_apply _ (hA.prod hB), withDensity_apply _ (hA.prod hB),
      setLIntegral_prod _ hf.aemeasurable.restrict,
      setLIntegral_prod_symm _ hg.aemeasurable.restrict]
    have h := u5_regular_kernel_measurable_rectangles hd ω lam Λ hΛ hω t A B hA hB
    change (∫⁻ x in A, K x B ∂μ) = ∫⁻ y in B, K y A ∂μ at h
    simp_rw [show ∀ x, K x = μ.withDensity (fun y => ENNReal.ofReal (p x y)) from hr,
      withDensity_apply _ hA, withDensity_apply _ hB] at h
    simpa only [f, g] using h
  have heq : (μ.prod μ).withDensity f = (μ.prod μ).withDensity g := by
    apply Measure.ext_of_iUnion_eq_univ (s := fun n => spanningSets μ n ×ˢ Set.univ)
    · ext q
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_univ, and_true, iff_true]
      exact Set.mem_iUnion.mp (iUnion_spanningSets μ ▸ Set.mem_univ q.1)
    · intro n
      let S := spanningSets μ n
      have hS : MeasurableSet S := measurableSet_spanningSets μ n
      have hfinite : (μ.prod μ).withDensity f (S ×ˢ Set.univ) < ∞ := by
        rw [withDensity_apply _ (hS.prod MeasurableSet.univ),
          setLIntegral_prod _ hf.aemeasurable.restrict]
        have hval (x : Vec d) : (∫⁻ y, f (x, y) ∂μ) = 1 := by
          have h := congrArg (fun m : Measure (Vec d) => m Set.univ) (hr x)
          rw [u2_regular_kernel_conservative] at h
          simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, f] using h.symm
        simp only [Measure.restrict_univ, hval, lintegral_const, one_mul, Measure.restrict_apply_univ]
        exact measure_spanningSets_lt_top μ n
      let : IsFiniteMeasure (((μ.prod μ).withDensity f).restrict (S ×ˢ Set.univ)) :=
        ⟨by simpa using hfinite⟩
      apply Measure.ext_prod
      intro A B hA hB
      rw [Measure.restrict_apply (hA.prod hB), Measure.restrict_apply (hA.prod hB)]
      rw [show (A ×ˢ B) ∩ (S ×ˢ Set.univ) = (A ∩ S) ×ˢ B by ext q; simp [and_assoc, and_comm, and_left_comm]]
      exact hrect (A ∩ S) B (hA.inter hS) hB
  have hae := (withDensity_eq_iff_of_sigmaFinite hf.aemeasurable hg.aemeasurable).mp heq
  filter_upwards [hae] with q hq
  simpa only [f, g, ENNReal.toReal_ofReal (hn _ _)] using congrArg ENNReal.toReal hq

#print axioms u5_regular_symmetric_density_of_ac


end EinsteinFull
