import EinsteinFull.Calculus.ComplexEvolutionLimitSupport
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Identifying the full unforced stationary generator

The strong Yosida limit is compared with one fixed bounded evolution to
recover the derivative on the actual full weak generator domain. Positive
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
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ •
      (unforcedComplexYosidaEvolution Q i n t f - f)) (𝓝[>] (0 : ℝ≥0))
      (𝓝 (unforcedComplexYosida Q i n f)) := by
  have h := ((hasDerivAt_unforcedComplexYosidaEvolution Q i n f 0).tendsto_slope_zero_right).comp
    tendsto_coe_right_zero
  simpa only [zero_add, unforcedComplexYosidaEvolution_zero, ContinuousLinearMap.id_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.ofReal_inv, RCLike.ofReal_inv, Function.comp_def] using! h

/-- The actual weak generator controls the error against one fixed bounded evolution. -/
theorem IsComplexGeneratorPair.unforced_evolution_sub_yosida_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    (n : ℕ) (t : ℝ≥0) :
    ‖unforcedComplexEvolution Q i t f - unforcedComplexYosidaEvolution Q i n t f‖ ≤
      (t : ℝ) * ‖g - unforcedComplexYosida Q i n f‖ := by
  exact le_of_tendsto_of_tendsto
    ((tendsto_unforcedComplexYosidaEvolution Q i t f).sub_const
      (unforcedComplexYosidaEvolution Q i n t f)).norm
    (tendsto_const_nhds.mul
      (hfg.tendsto_unforcedComplexYosida.sub_const (unforcedComplexYosida Q i n f)).norm)
    (Eventually.of_forall fun m =>
      norm_unforcedComplexYosidaEvolution_sub_evolution_le Q i m n f t t.property)

/-- Every pair in the full actual weak graph is a right derivative pair of the limiting family. -/
theorem IsComplexGeneratorPair.tendsto_unforcedComplexEvolution_slope
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (unforcedComplexEvolution Q i t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hfg.tendsto_unforcedComplexYosida
    (ε/3) (by positivity)
  have hng := hn n le_rfl
  have hy := Metric.tendsto_nhds.mp (tendsto_yosida_slope Q i n f) (ε/3) (by positivity)
  filter_upwards [hy, eventually_mem_nhdsWithin] with t ht hpos
  have htpos : 0 < (t : ℝ) := hpos
  have hb : dist (((t : ℝ) : ℂ)⁻¹ • (unforcedComplexEvolution Q i t f-f))
      (((t : ℝ) : ℂ)⁻¹ • (unforcedComplexYosidaEvolution Q i n t f-f)) ≤
        ‖g - unforcedComplexYosida Q i n f‖ := by
    rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    calc
      _ ≤ (t : ℝ)⁻¹ * ((t : ℝ) * ‖g - unforcedComplexYosida Q i n f‖) :=
        mul_le_mul_of_nonneg_left (hfg.unforced_evolution_sub_yosida_le n t)
          (inv_nonneg.mpr t.property)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ htpos.ne', one_mul]
  have htri := dist_triangle4
    (((t : ℝ) : ℂ)⁻¹ • (unforcedComplexEvolution Q i t f-f))
    (((t : ℝ) : ℂ)⁻¹ • (unforcedComplexYosidaEvolution Q i n t f-f))
    (unforcedComplexYosida Q i n f) g
  have hnrev : ‖g - unforcedComplexYosida Q i n f‖ < ε/3 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hng
  linarith only [htri, hb, ht, hnrev, hng]

private theorem yosidaEvolution_commute_resolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ) (t s : ℝ) (hs : 0 < s) :
    Commute (unforcedComplexYosidaEvolution Q i n t) (unforcedComplexResolvent Q i s hs) := by
  have hR := unforcedComplexResolvent_commute Q i ((n : ℝ)+1) s (by positivity) hs
  have hB := hR.smul_left (((n : ℝ)+1 : ℝ) : ℂ)
  change Commute (unforcedComplexResolventApproximation Q i n)
    (unforcedComplexResolvent Q i s hs) at hB
  have hA := (hB.sub_left (Commute.one_left _)).smul_left (((n : ℝ)+1 : ℝ) : ℂ)
  change Commute (unforcedComplexYosida Q i n) (unforcedComplexResolvent Q i s hs) at hA
  exact (hA.smul_left t).exp_left

/-- The actual limiting evolution commutes with every positive unforced resolvent. -/
theorem unforcedComplexEvolution_commute_resolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ≥0) (s : ℝ) (hs : 0 < s) :
    Commute (unforcedComplexEvolution Q i t) (unforcedComplexResolvent Q i s hs) := by
  apply ContinuousLinearMap.ext
  intro f
  have he (n : ℕ) : unforcedComplexYosidaEvolution Q i n t
      (unforcedComplexResolvent Q i s hs f) =
      unforcedComplexResolvent Q i s hs (unforcedComplexYosidaEvolution Q i n t f) :=
    congrArg (fun A : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) => A f)
      (yosidaEvolution_commute_resolvent Q i n t s hs).eq
  have h := ((unforcedComplexResolvent Q i s hs).continuous.tendsto
    (unforcedComplexEvolution Q i t f)).comp (tendsto_unforcedComplexYosidaEvolution Q i t f)
  simp only [Function.comp_def] at h
  simp_rw [← he] at h
  exact tendsto_nhds_unique (tendsto_unforcedComplexYosidaEvolution Q i t
    (unforcedComplexResolvent Q i s hs f)) h

/-- The full infinitesimal generator graph of the constructed family is exactly the frozen weak graph. -/
theorem tendsto_unforcedComplexEvolution_slope_iff {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (f g : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (unforcedComplexEvolution Q i t f-f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔ IsComplexGeneratorPair Q i 0 f g := by
  constructor
  · intro hfg
    let R := unforcedComplexResolvent Q i 1 zero_lt_one
    have he (t : ℝ≥0) : R (unforcedComplexEvolution Q i t f) =
        unforcedComplexEvolution Q i t (R f) :=
      (congrArg (fun A : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) => A f)
        (unforcedComplexEvolution_commute_resolvent Q i t 1 zero_lt_one).eq).symm
    have hR := (R.continuous.tendsto g).comp hfg
    simp only [Function.comp_def] at hR
    simp_rw [map_smul, map_sub, he] at hR
    have hr := (unforcedComplexResolvent_spec Q i 1 zero_lt_one f).tendsto_unforcedComplexEvolution_slope
    have hid : R g = R f-f := by
      simpa only [Complex.ofReal_one, one_smul] using tendsto_nhds_unique hR hr
    apply (isComplexGeneratorPair_iff_resolvent Q i 1 zero_lt_one f g).mpr
    change R ((1 : ℂ) • f-g) = f
    rw [one_smul, map_sub, hid, sub_sub_cancel]
  · exact IsComplexGeneratorPair.tendsto_unforcedComplexEvolution_slope

/-- The constructed contraction family satisfies the complete frozen unforced semigroup predicate. -/
theorem isComplexEnvironmentSemigroup_unforcedComplexEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    IsComplexEnvironmentSemigroup Q i 0 (unforcedComplexEvolution Q i) :=
  ⟨unforcedComplexEvolution_zero Q i, unforcedComplexEvolution_add Q i,
    continuous_unforcedComplexEvolution_apply Q i, tendsto_unforcedComplexEvolution_slope_iff Q i⟩

end EinsteinFull
