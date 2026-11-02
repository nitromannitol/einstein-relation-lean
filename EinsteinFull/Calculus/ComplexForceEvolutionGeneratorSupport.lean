import EinsteinFull.Calculus.ComplexForceEvolutionLimitSupport
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Identifying the full shifted forced stationary generator

The strong Yosida limit is compared with one fixed bounded evolution to
recover the derivative on the actual full weak generator domain. Shifted
resolvent commutation supplies the converse domain inclusion.
-/

open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

private theorem tendsto_coe_right_zero :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨(NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin⟩

private theorem tendsto_yosida_slope {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ •
      (forcedComplexYosidaEvolution Q i ζ n t f - f)) (𝓝[>] (0 : ℝ≥0))
      (𝓝 (forcedComplexYosida Q i ζ n f)) := by
  have h := ((hasDerivAt_forcedComplexYosidaEvolution Q i ζ n f 0).tendsto_slope_zero_right).comp
    tendsto_coe_right_zero
  simpa only [zero_add, forcedComplexYosidaEvolution_zero, ContinuousLinearMap.id_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.ofReal_inv,
    RCLike.ofReal_inv, Function.comp_def] using! h

/-- The actual weak generator controls the error against one fixed bounded evolution. -/
theorem IsComplexGeneratorPair.shifted_forced_evolution_sub_yosida_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (n : ℕ) (t : ℝ≥0) :
    ‖shiftedForcedComplexEvolution Q i ζ t f - forcedComplexYosidaEvolution Q i ζ n t f‖ ≤
      (t : ℝ) * ‖g - (complexForceShift d Λ₀ ζ : ℂ) • f - forcedComplexYosida Q i ζ n f‖ := by
  exact le_of_tendsto_of_tendsto
    ((tendsto_forcedComplexYosidaEvolution Q i ζ t f).sub_const
      (forcedComplexYosidaEvolution Q i ζ n t f)).norm
    (tendsto_const_nhds.mul
      (hfg.tendsto_forcedComplexYosida.sub_const (forcedComplexYosida Q i ζ n f)).norm)
    (Eventually.of_forall fun m =>
      norm_forcedComplexYosidaEvolution_sub_evolution_le Q i ζ m n f t t.property)

/-- Every pair in the full actual weak graph is a right derivative pair of the limiting family. -/
theorem IsComplexGeneratorPair.tendsto_shiftedForcedComplexEvolution_slope
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (shiftedForcedComplexEvolution Q i ζ t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (g - (complexForceShift d Λ₀ ζ : ℂ) • f)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hfg.tendsto_forcedComplexYosida
    (ε/3) (by positivity)
  have hng := hn n le_rfl
  have hy := Metric.tendsto_nhds.mp (tendsto_yosida_slope Q i ζ n f) (ε/3) (by positivity)
  filter_upwards [hy, eventually_mem_nhdsWithin] with t ht hpos
  have htpos : 0 < (t : ℝ) := hpos
  have hb : dist (((t : ℝ) : ℂ)⁻¹ • (shiftedForcedComplexEvolution Q i ζ t f-f))
      (((t : ℝ) : ℂ)⁻¹ • (forcedComplexYosidaEvolution Q i ζ n t f-f)) ≤
        ‖g - (complexForceShift d Λ₀ ζ : ℂ) • f - forcedComplexYosida Q i ζ n f‖ := by
    rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    calc
      _ ≤ (t : ℝ)⁻¹ * ((t : ℝ) * ‖g - (complexForceShift d Λ₀ ζ : ℂ) • f - forcedComplexYosida Q i ζ n f‖) :=
        mul_le_mul_of_nonneg_left (hfg.shifted_forced_evolution_sub_yosida_le n t)
          (inv_nonneg.mpr t.property)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ htpos.ne', one_mul]
  have htri := dist_triangle4
    (((t : ℝ) : ℂ)⁻¹ • (shiftedForcedComplexEvolution Q i ζ t f-f))
    (((t : ℝ) : ℂ)⁻¹ • (forcedComplexYosidaEvolution Q i ζ n t f-f))
    (forcedComplexYosida Q i ζ n f) (g - (complexForceShift d Λ₀ ζ : ℂ) • f)
  have hnrev : ‖g - (complexForceShift d Λ₀ ζ : ℂ) • f - forcedComplexYosida Q i ζ n f‖ < ε/3 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hng
  linarith only [htri, hb, ht, hnrev, hng]

private theorem yosidaEvolution_commute_resolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n : ℕ) (t s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) :
    Commute (forcedComplexYosidaEvolution Q i ζ n t) (forcedComplexResolvent Q i ζ s hs) := by
  have hR := forcedComplexResolvent_commute Q i ζ
    (complexForceShift d Λ₀ ζ + ((n : ℝ)+1)) s
    (lt_add_of_pos_right _ (by positivity)) hs
  have hB := hR.smul_left (((n : ℝ)+1 : ℝ) : ℂ)
  change Commute (forcedComplexResolventApproximation Q i ζ n)
    (forcedComplexResolvent Q i ζ s hs) at hB
  have hA := (hB.sub_left (Commute.one_left _)).smul_left (((n : ℝ)+1 : ℝ) : ℂ)
  change Commute (forcedComplexYosida Q i ζ n) (forcedComplexResolvent Q i ζ s hs) at hA
  exact (hA.smul_left t).exp_left

/-- The actual limiting evolution commutes with every shifted forced resolvent. -/
theorem shiftedForcedComplexEvolution_commute_resolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) :
    Commute (shiftedForcedComplexEvolution Q i ζ t) (forcedComplexResolvent Q i ζ s hs) := by
  apply ContinuousLinearMap.ext
  intro f
  have he (n : ℕ) : forcedComplexYosidaEvolution Q i ζ n t
      (forcedComplexResolvent Q i ζ s hs f) =
      forcedComplexResolvent Q i ζ s hs (forcedComplexYosidaEvolution Q i ζ n t f) :=
    congrArg (fun A : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) => A f)
      (yosidaEvolution_commute_resolvent Q i ζ n t s hs).eq
  have h := ((forcedComplexResolvent Q i ζ s hs).continuous.tendsto
    (shiftedForcedComplexEvolution Q i ζ t f)).comp (tendsto_forcedComplexYosidaEvolution Q i ζ t f)
  simp only [Function.comp_def] at h
  simp_rw [← he] at h
  exact tendsto_nhds_unique (tendsto_forcedComplexYosidaEvolution Q i ζ t
    (forcedComplexResolvent Q i ζ s hs f)) h

/-- The full generator of the contraction family is exactly the shifted frozen weak graph. -/
theorem tendsto_shiftedForcedComplexEvolution_slope_iff {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (f g : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (shiftedForcedComplexEvolution Q i ζ t f-f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔
        IsComplexGeneratorPair Q i ζ f (g + (complexForceShift d Λ₀ ζ : ℂ) • f) := by
  constructor
  · intro hfg
    let s := complexForceShift d Λ₀ ζ + 1
    have hs : complexForceShift d Λ₀ ζ < s := lt_add_one _
    let R := forcedComplexResolvent Q i ζ s hs
    have he (t : ℝ≥0) : R (shiftedForcedComplexEvolution Q i ζ t f) =
        shiftedForcedComplexEvolution Q i ζ t (R f) :=
      (congrArg (fun A : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) => A f)
        (shiftedForcedComplexEvolution_commute_resolvent Q i ζ t s hs).eq).symm
    have hR := (R.continuous.tendsto g).comp hfg
    simp only [Function.comp_def] at hR
    simp_rw [map_smul, map_sub, he] at hR
    have hr := (forcedComplexResolvent_spec Q i ζ s hs f).tendsto_shiftedForcedComplexEvolution_slope
    have hid : R g = R f-f := by
      convert tendsto_nhds_unique hR hr using 1
      dsimp [s]
      module
    apply (isComplexGeneratorPair_iff_forced_resolvent Q i ζ s hs f _).mpr
    change R ((s : ℂ) • f - (g + (complexForceShift d Λ₀ ζ : ℂ) • f)) = f
    have ha : (s : ℂ) • f - (g + (complexForceShift d Λ₀ ζ : ℂ) • f) = f-g := by
      dsimp [s]
      module
    rw [ha, map_sub, hid, sub_sub_cancel]
  · intro h
    convert h.tendsto_shiftedForcedComplexEvolution_slope using 1
    simp only [add_sub_cancel_right]

end EinsteinFull
