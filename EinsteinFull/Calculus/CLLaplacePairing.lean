import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Calculus.ComplexGeneratorOperatorSupport
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Laplace transforms of the unforced semigroup

The Laplace transform of an orbit of the unforced environment semigroup is the unforced resolvent
(the orbit identity is the one of `Blueprint/G3/Proofs/W3Queue0420_2`), so the Laplace transform of
the pairing `t ↦ ∫ g · P_t f` is `∫ g · R_s f`. Laplace transforms of an integrable function on
`(0, ∞)` converge to its integral as the mass tends to zero.
-/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

theorem cl_unforced_norm_apply_le (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) : ‖P t f‖ ≤ ‖f‖ := by
  have hb := hP.norm_le t
  norm_num [complexForceShift] at hb
  exact ((P t).le_opNorm f).trans (by
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right hb (norm_nonneg f))

theorem cl_integrable_laplace_orbit (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (reducedLaw Q)) :
    IntegrableOn (fun t : ℝ => Real.exp (-s*t) • P t.toNNReal f) (Ici 0) := by
  have he := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const ‖f‖
  have he : IntegrableOn (fun t : ℝ => Real.exp (-s*t) * ‖f‖) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr he
  apply he.mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((hP.2.2.1 f).comp continuous_real_toNNReal)).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (cl_unforced_norm_apply_le hP _ f) (Real.exp_pos _).le

theorem cl_integral_Icc_tendsto_Ici {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E}
    (hf : IntegrableOn f (Ici 0)) :
    Tendsto (fun T : ℝ => ∫ t in Icc (0 : ℝ) T, f t) atTop
      (𝓝 (∫ t in Ici (0 : ℝ), f t)) := by
  have hsets : (⋃ T : ℝ, Icc (0 : ℝ) T) = Ici 0 := by
    ext t
    simp only [mem_iUnion, mem_Icc, mem_Ici]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨t, h, le_rfl⟩⟩
  have ht := tendsto_setIntegral_of_monotone
    (fun T : ℝ => measurableSet_Icc (a := 0) (b := T))
    (fun _ _ h => Icc_subset_Icc_right h) (hsets ▸ hf)
  simpa only [hsets] using! ht

/-- The Laplace transform of an unforced orbit is the unforced resolvent. -/
theorem cl_laplace_orbit_eq_resolvent (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ t in Ici (0 : ℝ), Real.exp (-s*t) • P t.toNNReal f) =
      unforcedComplexResolvent Q i s hs f := by
  let u := unforcedComplexResolvent Q i s hs f
  have hu := unforcedComplexResolvent_spec Q i s hs f
  have hcont : Continuous (fun t : ℝ => Real.exp (-s*t) • P t.toNNReal u) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((hP.2.2.1 u).comp continuous_real_toNNReal)
  have hint := cl_integrable_laplace_orbit hP s hs f
  have hlim : Tendsto (fun t : ℝ => Real.exp (-s*t) • P t.toNNReal u) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun t : ℝ => Real.exp (-s*t) * ‖u‖)
    · intro t
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (cl_unforced_norm_apply_le hP _ u) (Real.exp_pos _).le
    · have ht := Real.tendsto_exp_atBot.comp
        (Filter.Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hs) tendsto_id)
      simpa only [zero_mul] using! ht.mul_const ‖u‖
  have hd (t : ℝ) (ht : 0 ≤ t) :
      HasDerivWithinAt (fun r : ℝ => Real.exp (-s*r) • P r.toNNReal u)
        (-(Real.exp (-s*t) • P t.toNNReal f)) (Ici t) t := by
    have he : HasDerivAt (fun r : ℝ => Real.exp (-s*r))
        ((-s) * Real.exp (-s*t)) t := by
      simpa only [id_eq, mul_one, mul_comm] using!
        (((hasDerivAt_id t).const_mul (-s)).exp)
    have h := he.hasDerivWithinAt.smul (hP.hasDerivWithinAt_orbit hu t ht)
    convert! h using 1
    change -(Real.exp (-s*t) • P t.toNNReal f) =
      Real.exp (-s*t) • P t.toNNReal ((s : ℂ) • u - f) +
        (-s * Real.exp (-s*t)) • P t.toNNReal u
    rw [map_sub, map_smul, Complex.coe_smul, smul_sub]
    module
  have hi (T : ℝ) (hT : 0 ≤ T) :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hcont.continuousOn
      (fun t ht => (hd t ht.1.le).mono Ioi_subset_Ici_self)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
        (hint.mono_set (fun _ h => h.1))).neg
  have hi' (T : ℝ) (hT : 0 ≤ T) :
      (∫ t in Icc (0 : ℝ) T, Real.exp (-s*t) • P t.toNNReal f) =
        u - Real.exp (-s*T) • P T.toNNReal u := by
    have h := hi T hT
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_of_le hT,
      ← integral_Icc_eq_integral_Ioc] at h
    simp only [mul_zero, Real.exp_zero, one_smul, Real.toNNReal_zero, hP.1,
      ContinuousLinearMap.id_apply] at h
    exact (neg_eq_iff_eq_neg.mp h).trans (neg_sub _ _)
  have ht := cl_integral_Icc_tendsto_Ici hint
  have ht' : Tendsto (fun T : ℝ => u - Real.exp (-s*T) • P T.toNNReal u)
      atTop (𝓝 u) := by
    simpa only [sub_zero] using! (tendsto_const_nhds (x := u)).sub hlim
  exact tendsto_nhds_unique ht (ht'.congr' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (hi' T hT).symm))

/-- The bilinear pairing is the inner product with the conjugate. -/
theorem cl_integral_mul_eq_inner_star (g h : Lp ℂ 2 (reducedLaw Q)) :
    ∫ ω, g ω * h ω ∂reducedLaw Q = inner ℂ (star g) h := by
  erw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star g] with ω hω
  change (star g : Lp ℂ 2 (reducedLaw Q)) ω = star (g ω) at hω
  simp only [hω, RCLike.inner_apply, Complex.star_def, Complex.conj_conj, mul_comm]

/-- The Laplace transform of the pairing `t ↦ ∫ g · P_t f` is `∫ g · R_s f`. -/
theorem cl_laplace_pairing_eq_resolvent (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (s : ℝ) (hs : 0 < s) (g f : Lp ℂ 2 (reducedLaw Q)) :
    IntegrableOn (fun t : ℝ => (Real.exp (-s * t) : ℂ) *
        ∫ ω, g ω * P t.toNNReal f ω ∂reducedLaw Q) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
          ∫ ω, g ω * P t.toNNReal f ω ∂reducedLaw Q =
        ∫ ω, g ω * unforcedComplexResolvent Q i s hs f ω ∂reducedLaw Q := by
  have hint := cl_integrable_laplace_orbit hP s hs f
  let L := innerSL ℂ (star g)
  have hfun : (fun t : ℝ => (Real.exp (-s * t) : ℂ) *
      ∫ ω, g ω * P t.toNNReal f ω ∂reducedLaw Q) =
      fun t => L (Real.exp (-s * t) • P t.toNNReal f) := by
    funext t
    rw [ContinuousLinearMap.map_smul_of_tower, Complex.real_smul, cl_integral_mul_eq_inner_star]
    rfl
  rw [hfun]
  refine ⟨IntegrableOn.mono_set (L.integrable_comp hint) Ioi_subset_Ici_self, ?_⟩
  rw [← integral_Ici_eq_integral_Ioi, L.integral_comp_comm hint,
    cl_laplace_orbit_eq_resolvent hP s hs f, cl_integral_mul_eq_inner_star]
  rfl

/-- Laplace transforms of an integrable function on `(0, ∞)` converge to its integral. -/
theorem cl_laplace_tendsto_Ioi {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) (mass : ℕ → ℝ)
    (hm : ∀ n, 0 < mass n) (hm0 : Tendsto mass atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t in Ioi (0 : ℝ), Real.exp (-mass n * t) * g t)
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), g t)) := by
  have hcm : ∀ n, AEStronglyMeasurable (fun t : ℝ => Real.exp (-mass n * t))
      (volume.restrict (Ioi (0 : ℝ))) := fun n =>
    (Continuous.aestronglyMeasurable (by fun_prop))
  apply tendsto_integral_of_dominated_convergence (F := fun n t => Real.exp (-mass n * t) * g t)
    (fun t => ‖g t‖) (fun n => (hcm n).mul hg.aestronglyMeasurable) hg.norm
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hm n).le) (le_of_lt ht)))
  · exact Eventually.of_forall fun t => by
      have he := Real.continuous_exp.continuousAt.tendsto.comp (hm0.neg.mul_const t)
      simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul] using! he.mul_const (g t)

end EinsteinFull.Blueprint
